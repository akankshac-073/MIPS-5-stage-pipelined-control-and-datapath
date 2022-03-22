// Rising-edge synchronous 32-bit Program Counter. Async reset will set program counter to 0 asynchronously. 

// Dff implementation for registers

module d_ff (
    input clk, 
    input reset, 
    input write_enable, 
    input d, 
    output reg q);

    always @ (reset)
        if(reset == 1)
            q = 0;	
    always @ (posedge clk)
        if(write_enable == 1)	
            q = d;	
endmodule

// Creating a 32-bit Program Counter register that holds exe instruction's address

module program_counter #(parameter N = 32) (
    input clk, 
    input reset, 
    input PCWrite,
    input [N-1:0] pc_in, 
    output [N-1:0] pc_out);

    // To generate N = 32 instances of d_ff to store the 32-bit input  
    genvar i;
    generate      
        for (i = 0; i < N; i = i+1) 
        begin            
            d_ff d0 (clk, reset, PCWrite, pc_in[i], pc_out[i]);
        end
    endgenerate
endmodule 

// Instruction memory - consisting of 32 entries - instructions commented
// NOTE - valid range of read addr/4 is from 0 to 31

module instruction_memory (
    input reset,
    input[31:0] read_addr,
    output [31:0] instruction);

    reg [31:0] inst_memory [0:31]; // instruction memory size - 32
    
    wire [29:0] shifted_read_addr; // byte address
    assign shifted_read_addr = read_addr [31:2]; // word address
    assign instruction = inst_memory [shifted_read_addr];

    integer i;
    always @(posedge reset)
    begin

        for (i=0; i<32; i=i+1) 
        begin
           inst_memory[i] = 32'b0;
        end
        inst_memory[0] = 32'b00000000000000000000000000000000;         // nop
        inst_memory[1] = 32'b100011_00000_10001_0000000000001000;      // lw  $s1($17), 8($0)
        inst_memory[2] = 32'b100011_00000_10010_0000000000000100;      // lw  $s2($18), 4($0)
        inst_memory[3] = 32'b101011_10011_00000_0000000000001100;      // sw  $s3($19), 12($0)
        inst_memory[4] = 32'b000100_10001_10001_0000000000000010;      // beq
        inst_memory[5] = 32'b00000000000000000000000000000000;         // nop
        inst_memory[6] = 32'b00000000000000000000000000000000;         // nop
        inst_memory[7] = 32'b000000_10001_10010_01000_00000_100000;    // add $t0($8), $s1($17), $s2($18)
        inst_memory[8] = 32'b000000_10001_10010_01001_00000_100010;    // sub $t1($9), $s1($17), $s2($18)
        inst_memory[9] = 32'b000000_10001_10010_01010_00000_100100;    // and $t2($10), $s1($17), $s2($18)
        inst_memory[10] = 32'b000000_10001_10010_01011_00000_100101;   // or $t3($11), $s1($17), $s2($18)
        inst_memory[11] = 32'b000000_10001_10010_01100_00000_101010;   // slt $t4($12), $s1($17), $s2($18)
        inst_memory[12] = 32'b001000_10001_01101_0000000000001111;     // addi $t5($13), $s1($17), 15
        inst_memory[13] = 32'b001100_10001_01110_1010101010101010;     // andi $t6($14), $s1($17), 43690
        inst_memory[14] = 32'b001101_10001_01111_1111000011110000;     // ori $t7($15), $s1($17), 61680
        inst_memory[15] = 32'b001010_10001_10100_0000000000000000;     // slti $s4($20), $s1($17), 0
        inst_memory[16] = 32'b000100_10001_10010_0000000000000100;     // beq
        inst_memory[17] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[18] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[19] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[20] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[21] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[22] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[23] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[24] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[25] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[26] = 32'b00000000000000000000000000000000;        // nop 
        inst_memory[27] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[28] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[29] = 32'b00000000000000000000000000000000;        // nop 
        inst_memory[30] = 32'b00000000000000000000000000000000;        // nop
        inst_memory[31] = 32'b00000000000000000000000000000000;        // nop
    end
endmodule


// MIPS ALU 32-bit - performs operation corresponding to the ALU control signal. It is used for -  
// A. PC updation as an adder (ALU always wired to add the 2 32?bit inputs and place the sum on its output.
// B. Arithmetic and Logical operations for executing instructions - appropriate ALU control must be designed for
// the instruction set considered for execution. 

module ALU_32_bit (
    input [3:0] ALU_ctrl,
    input [31:0] A, B,
    output reg [31:0] result,
    output reg carry_out, 
    output zero);

    always @ (ALU_ctrl, A, B) 
    begin
        case(ALU_ctrl)
            0:  result <= A & B;
            1:  result <= A | B;
            2:  {carry_out, result[31:0]} <= A + B;
            6:  {carry_out, result[31:0]} <= A - B;
            7:  result <= A < B ? 1 : 0; 
            12: result <= ~(A | B);
            default: result <= 0;
        endcase
    end
    assign zero = (({result} == 0)) ? 1 : 0;
endmodule

module  ALU_testbench;

    // inputs
    reg [3:0] ALU_ctrl;
    reg [31:0] A, B;

    // outputs
    wire  [31:0] result;
    wire  carry_out, zero;

    // instantiate module
    ALU_32_bit  u (.zero(zero), .carry_out(carry_out), .result(result), .A(A), .B(B), .ALU_ctrl(ALU_ctrl));

    initial begin
        $monitor($time, " :A = %b,\n\t B = %b,\n\t ALU_ctrlerartion = %b,\n\t Result = %b,\n\t Carry Out = %b,\n\t Zero = %b.", A, B, ALU_ctrl, result, carry_out, zero);
        #0  A = 32'ha5a5a5a5; B = 32'h5a5a5a5a; ALU_ctrl = 4'b0000;     // AND resulting in 00000000 (0000 0000 0000 0000 0000 0000 0000 0000)
        #10  ALU_ctrl = 4'b0001;                                        // OR resulting in FFFFFFFF(1111 1111 1111 1111 1111 1111 1111 1111)
        #10  ALU_ctrl = 4'b0010;                                        // ADD resulting in FFFFFFFF (1111 1111 1111 1111 1111 1111 1111 1111)
        #10  ALU_ctrl = 4'b0110;                                        // SUB resulting in 4B4B4B4B (0100 1011 0100 1011 0100 1011 0100 1011)
        #10  A = 32'hA5A5A5A5; B = 32'hA5A5A5A5; ALU_ctrl = 4'b0110;    // SUB resulting in 00000000 (0000 0000 0000 0000 0000 0000 0000 0000) -- Check for zero 
        #10  B = 32'hA5A5A5A5; A = 32'h5A5A5A5A; ALU_ctrl = 4'b0111;    // SLT resulting in 00000001 (0000 0000 0000 0000 0000 0000 0000 0001)
        #10  B = 32'hA5A5A5A5; A = 32'h5A5A5A5A; ALU_ctrl = 4'b1100;    // NOR resulting in 00000000(0000 0000 0000 0000 0000 0000 0000 0000)
        #20  $finish;
    end
endmodule

// N-bit MUX - selects one of the two N-bit inputs provided to MUX depending on the control signal generated 

module mux_N_bit #(parameter N = 32)(
    input [N-1:0] in0, 
    input [N-1:0] in1,
    input select,
    output [N-1:0] mux_out);

    assign mux_out = select ? in1 : in0;
endmodule


// IF/ID stage register

module IF_ID_reg (
    input clk, 
    input reset,
    input IF_ID_write,           // Hazard control - updation
    input IF_flush,              // Hazard control - flush
    input [31:0] pc_inc4_in, 
    input [31:0] instruction_in,
    output reg [31:0] pc_inc4_out, 
    output reg [31:0] instruction_out);

    always @(posedge clk or posedge reset)
    begin

        // Async reset sets PC register content and exe instruction addr to 0
        if (reset == 1)
        begin
            pc_inc4_out <= 32'b0;
            instruction_out <= 32'b0;
        end
 
       // If IF_flush is set, flush all content
        else if (IF_flush == 1)
        begin
            pc_inc4_out <= 32'b0;
            instruction_out <= 32'b0;
        end

        // If IF_ID_write is set update PC and instruction value for this posedge
        else if (IF_ID_write == 1)
        begin
            pc_inc4_out <= pc_inc4_in;
            instruction_out <= instruction_in;
        end
    end	
endmodule

// Register file structure - contains all 32 general-purpose registers and has 2 read ports and 1 write port.  
// Any of these can be read/written(by specifying the control signal) their number in the register file.

module register_file (
    input clk, 
    input reset, 
    input RegWrite,
    input [4:0] read_addr1, read_addr2, 
    input [4:0] write_addr,
    input [31:0] write_data,
    output [31:0] read_data1, read_data2);

    reg [31:0] register_file [31:0];
    integer k;

    assign read_data1 = register_file[read_addr1];
    assign read_data2 = register_file[read_addr2];

    always @(posedge clk or posedge reset)
    begin

        // Async reset sets all register content to 0
        if (reset == 1)
        begin
            for (k=0; k<32; k=k+1) 
            begin
                register_file[k] = 32'b0;
            end
        end

        // Write on rising edge if RegWrite control is set
        else if (RegWrite == 1) 
            register_file[write_addr] = write_data; 
    end
endmodule

// Sign extends immediate operand from 16-bit to 32-bit value

module sign_extender(
    input [15:0] in,
    output [31:0] out);

    assign out = {{16{in[15]}}, in};	
endmodule


// Shift left by 2 for jump instruction - word address

module left_shifter_jump (
    input [25:0] in,
    output [27:0] out);

    assign out = {in[25:0],1'b0,1'b0};
endmodule

// Main control 

module main_control ( 
    input [5:0] op_code,
    output RegDst, Jump, Branch, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite,
    output [1:0] ALU_op);
                                                                                                                // Opcodes for which control signal is active
    assign RegDst =(~op_code[5])&(~op_code[4])&(~op_code[3])&(~op_code[2])&(~op_code[1])&(~op_code[0]);         // 000000
    assign Jump =(~op_code[5])&(~op_code[4])&(~op_code[3])&(~op_code[2])&(op_code[1])&(~op_code[0]);            // 000010
    assign Branch =(~op_code[5])&(~op_code[4])&(~op_code[3])&(op_code[2])&(~op_code[1])&(~op_code[0]);          // 000100
    assign MemRead =(op_code[5])&(~op_code[4])&(~op_code[3])&(~op_code[2])&(op_code[1])&(op_code[0]);           // 100011
    assign MemtoReg =(op_code[5])&(~op_code[4])&(~op_code[3])&(~op_code[2])&(op_code[1])&(op_code[0]);          // 100011
    assign MemWrite =(op_code[5])&(~op_code[4])&(op_code[3])&(~op_code[2])&(op_code[1])&(op_code[0]);           // 101011

    assign ALUSrc = ((~op_code[5])&(~op_code[4])&(op_code[3])&(~op_code[2])&(~op_code[1])&(~op_code[0])) |      // 001000
                    ((~op_code[5])&(~op_code[4])&(op_code[3])&(op_code[2])&(~op_code[1])&(~op_code[0])) |       // 001100
                    ((op_code[5])&(~op_code[4])&(~op_code[3])&(~op_code[2])&(op_code[1])&(op_code[0])) |        // 100011
                    (((op_code[5])&(~op_code[4])&(op_code[3])&(~op_code[2])&(op_code[1])&(op_code[0]))) |       // 101011
                    ((~op_code[5])&(~op_code[4])&(op_code[3])&(op_code[2])&(~op_code[1])&(op_code[0])) |        // 001101
                    (((~op_code[5])&(~op_code[4])&(op_code[3])&(~op_code[2])&(op_code[1])&(~op_code[0])));      // 001010

    assign RegWrite = (~op_code[5])&(~op_code[4])&(~op_code[3])&(~op_code[2])&(~op_code[1])&(~op_code[0]) |     // 000000
                      ((~op_code[5])&(~op_code[4])&(op_code[3])&(~op_code[2])&(~op_code[1])&(~op_code[0])) |    // 001000
                      ((~op_code[5])&(~op_code[4])&(op_code[3])&(op_code[2])&(~op_code[1])&(~op_code[0])) |     // 001100
                      ((op_code[5])&(~op_code[4])&(~op_code[3])&(~op_code[2])&(op_code[1])&(op_code[0])) |      // 100011
                      ((~op_code[5])&(~op_code[4])&(op_code[3])&(op_code[2])&(~op_code[1])&(op_code[0])) |      // 001101
                      ((~op_code[5])&(~op_code[4])&(op_code[3])&(~op_code[2])&(op_code[1])&(~op_code[0]));      // 001010
    
    assign ALU_op[1] = ((~op_code[5])&(~op_code[4])&(~op_code[3])&(~op_code[2])&(~op_code[1])&(~op_code[0])) |  // 000000
                       ((~op_code[5])&(~op_code[4])&(op_code[3])&(op_code[2])&(~op_code[1])&(~op_code[0])) |    // 001100
                       ((~op_code[5])&(~op_code[4])&(op_code[3])&(~op_code[2])&(~op_code[1])&(~op_code[0])) |   // 001000
                       ((~op_code[5])&(~op_code[4])&(op_code[3])&(op_code[2])&(~op_code[1])&(op_code[0])) |     // 001101
                       ((~op_code[5])&(~op_code[4])&(op_code[3])&(~op_code[2])&(op_code[1])&(~op_code[0]));     // 001010

    assign ALU_op[0] = ((~op_code[5])&(~op_code[4])&(~op_code[3])&(op_code[2])&(~op_code[1])&(~op_code[0])) |   // 000100
                       ((~op_code[5])&(~op_code[4])&(op_code[3])&(op_code[2])&(~op_code[1])&(~op_code[0])) |    // 001100
                       ((~op_code[5])&(~op_code[4])&(op_code[3])&(~op_code[2])&(~op_code[1])&(~op_code[0])) |   // 001000
                       ((~op_code[5])&(~op_code[4])&(op_code[3])&(op_code[2])&(~op_code[1])&(op_code[0])) |     // 001101
                       ((~op_code[5])&(~op_code[4])&(op_code[3])&(~op_code[2])&(op_code[1])&(~op_code[0]));     // 001010
endmodule


// ID/EX stage register

module ID_EX_reg (
    input clk, reset,

    // Hazard control signals - lw, beq
    input ID_flush_lw_stall, ID_flush_branch,

    // WB control signals
    input RegWrite_in, MemtoReg_in,
 
    // MEM control signals
    input Branch_in, MemRead_in, MemWrite_in, Jump_in,

    // EXE control signals
    input RegDst_in, ALUSrc_in,
    input [1:0] ALUOp_in,

    // Addresses, memory and register contents
    input [31:0] jump_addr_in, pc_inc4_in,
    input [31:0] reg_read_data1_in, reg_read_data2_in, imm_sign_extended_in,
    input [4:0] IF_ID_register_rs_in, IF_ID_register_rt_in, IF_ID_register_rd_in,
    input [5:0] IF_ID_funct_in,
    input [5:0] IF_ID_opcode_in,

    // Corresponding updated outputs
    output reg RegWrite_out, MemtoReg_out,
    output reg Branch_out, MemRead_out, MemWrite_out, Jump_out,
    output reg RegDst_out, ALUSrc_out,
    output reg [1:0] ALUOp_out,
    output reg [31:0] jump_addr_out, pc_inc4_out,
    output reg [31:0] reg_read_data1_out, reg_read_data2_out, imm_sign_extended_out,
    output reg [4:0] IF_ID_register_rs_out, IF_ID_register_rt_out, IF_ID_register_rd_out,
    output reg [5:0] IF_ID_funct_out,
    output reg [5:0] IF_ID_opcode_out);

    always @(posedge clk or posedge reset)
    begin

        // Async reset -  reset WB, MEM and EX control signals to 0 and clear all addr, data and reg content
        if (reset == 1)
        begin
            
            RegWrite_out = 1'b0;
            MemtoReg_out = 1'b0;
            Branch_out = 1'b0;
            MemRead_out = 1'b0;
            MemWrite_out = 1'b0;
            Jump_out = 1'b0;
            RegDst_out = 1'b0;
            ALUSrc_out = 1'b0;
            ALUOp_out = 2'b0;

            jump_addr_out = 32'b0;
            pc_inc4_out = 32'b0;
            reg_read_data1_out = 32'b0;
            reg_read_data2_out = 32'b0;
            imm_sign_extended_out = 32'b0;
            IF_ID_register_rs_out = 5'b0;
            IF_ID_register_rt_out = 5'b0;
            IF_ID_register_rd_out = 5'b0;
            IF_ID_funct_out = 6'b0;
            IF_ID_opcode_out = 6'b0;
			
        end

        // Hazard control - in case of lw stall or branch hazard, reset WB, MEM and EX control signals to 0 
        // leave the addr, data and reg content unchanged
  
        else if (ID_flush_lw_stall == 1'b1)
        begin
            RegWrite_out = 1'b0;
            MemtoReg_out = 1'b0;
            Branch_out = 1'b0;
            MemRead_out = 1'b0;
            MemWrite_out = 1'b0;
            Jump_out = 1'b0;
            RegDst_out = 1'b0;
            ALUSrc_out = 1'b0;
            ALUOp_out = 2'b0;
         end

         else if (ID_flush_branch == 1'b1)
         begin
             RegWrite_out = 1'b0;
             MemtoReg_out = 1'b0;
             Branch_out = 1'b0;
             MemRead_out = 1'b0;
             MemWrite_out = 1'b0;
             Jump_out = 1'b0;
             RegDst_out = 1'b0;
             ALUSrc_out = 1'b0;
             ALUOp_out = 2'b0;
         end

         // If no hazard control required, proceed normally (retain all values as it is)
         else 
         begin
             RegWrite_out = RegWrite_in;
             MemtoReg_out = MemtoReg_in;
             Branch_out = Branch_in;
             MemRead_out = MemRead_in;
             MemWrite_out = MemWrite_in;
             Jump_out = Jump_in;
             RegDst_out = RegDst_in;
             ALUSrc_out = ALUSrc_in;
             ALUOp_out = ALUOp_in;

             jump_addr_out = jump_addr_in;
             pc_inc4_out = pc_inc4_in;
             reg_read_data1_out = reg_read_data1_in;
             reg_read_data2_out = reg_read_data2_in;
             imm_sign_extended_out = imm_sign_extended_in;
             IF_ID_register_rs_out = IF_ID_register_rs_in;
             IF_ID_register_rt_out = IF_ID_register_rt_in;
             IF_ID_register_rd_out = IF_ID_register_rd_in;
             IF_ID_funct_out = IF_ID_funct_in;
             IF_ID_opcode_out = IF_ID_opcode_in;
         end	
    end	
endmodule

// ALU control unit

module ALU_control (
    input [1:0] ALU_op,
    input [5:0] funct,
    input [5:0] op_code, // reqd for i-type instructions
    output [3:0] ALU_ctrl);

    assign ALU_ctrl[3] = 0;

    assign ALU_ctrl[2] = ((~ALU_op[1])&(ALU_op[0])) | 
                         ((ALU_op[1])&(~ALU_op[0])&(~funct[3])&(~funct[2])&(funct[1])&(~funct[0])) | 
                         ((ALU_op[1])&(~ALU_op[0])&(funct[3])&(~funct[2])&(funct[1])&(~funct[0])) |
                         ((ALU_op[1])&(ALU_op[0]) & op_code[1]);

    assign ALU_ctrl[1] = ((~ALU_op[1])&(~ALU_op[0])) |
                         ((~ALU_op[1])&(ALU_op[0])) | 
                         ((ALU_op[1])&(~ALU_op[0])&(~funct[3])&(~funct[2])&(~funct[1])&(~funct[0])) | 
                         ((ALU_op[1])&(~ALU_op[0])&(~funct[3])&(~funct[2])&(funct[1])&(~funct[0]))|
                         ((ALU_op[1])&(~ALU_op[0])&(funct[3])&(~funct[2])&(funct[1])&(~funct[0])) |
                         ((ALU_op[1])&(ALU_op[0])&(~op_code[2]));

    assign ALU_ctrl[0]=((ALU_op[1])&(~ALU_op[0])&(~funct[3])&(funct[2])&(~funct[1])&(funct[0])) |
                       ((ALU_op[1])&(~ALU_op[0])&(funct[3])&(~funct[2])&(funct[1])&(~funct[0])) |
                       ((ALU_op[1])&(ALU_op[0])&(op_code[2])&(~op_code[1])&(op_code[0])) |
                       ((ALU_op[1])&(ALU_op[0])&(~op_code[2])&(op_code[1])&(~op_code[0]));
endmodule

// 3 to 1 N-bit muxes

module mux_N_bit_3to1 #(parameter N = 32)(
    input [31:0] in0, in1, in2,
    input [1:0] select,
    output reg [31:0] mux_out);

    always @(in0 or in1 or in2 or select)
    begin
        case(select)
            2'b00: mux_out <= in0;
            2'b01: mux_out <= in1;
            2'b10: mux_out <= in2;
            default: mux_out <= in0;
        endcase
    end 
endmodule

// left shift branch offset by 2

module left_shifter_branch (
    input [31:0] in,
    output [31:0] out);

    assign out[31:0]={in[29:0],2'b00};
endmodule

// EX/MEM state registers

module EX_MEM_reg (
    input clk, reset,

    // Hazard control signal - branch/jump
    input EX_flush, 

    // WB control signals
    input RegWrite_in, MemtoReg_in, 

    // MEM control signals
    input Branch_in, MemRead_in, MemWrite_in, Jump_in,
 
    // Addresses, memory and register contents
    input [31:0] jump_addr_in, branch_addr_in,
    input ALU_zero_in, 
    input [31:0] ALU_result_in, reg_read_data2_in,
    input [4:0] ID_EX_register_rd_in, 

    // Corresponding updated outputs
    output reg RegWrite_out, MemtoReg_out, 
    output reg Branch_out, MemRead_out, MemWrite_out, Jump_out,  
    output reg [31:0] jump_addr_out, branch_addr_out, 
    output reg ALU_zero_out,  
    output reg [31:0] ALU_result_out, reg_read_data2_out, 
    output reg [4:0] EX_MEM_register_rd_out);

    always @(posedge clk or posedge reset)
    begin

        // Async reset -  reset WB, MEM and EX control signals to 0 and clear all addr, data and reg content
        if (reset == 1)
        begin
            RegWrite_out <= 1'b0;
            MemtoReg_out <= 1'b0;
            Branch_out <= 1'b0;
            MemRead_out <= 1'b0;
            MemWrite_out <= 1'b0;
            Jump_out <= 1'b0;
            jump_addr_out <= 32'b0;
            branch_addr_out <= 32'b0;
            ALU_zero_out <= 1'b0;
            ALU_result_out <= 32'b0;
            reg_read_data2_out <= 32'b0;
            EX_MEM_register_rd_out <= 5'b0; 
        end

        // Hazard control - in case of branch/jump hazards, reset WB, MEM and EX control signals to 0 
        // leave the addr, data and reg content unchanged
        else if (EX_flush == 1)
        begin
            RegWrite_out <= 1'b0;
            MemtoReg_out <= 1'b0;
            Branch_out <= 1'b0;
            MemRead_out <= 1'b0;
            MemWrite_out <= 1'b0;
            Jump_out <= 1'b0;
        end

         // If no hazard control required, proceed normally (retain all values as it is)
        else 
            begin
                RegWrite_out <= RegWrite_in;
                MemtoReg_out <= MemtoReg_in;
                Branch_out <= Branch_in;
                MemRead_out <= MemRead_in;
                MemWrite_out <= MemWrite_in;
                Jump_out <= Jump_in;
                jump_addr_out <= jump_addr_in;
                branch_addr_out <= branch_addr_in;
                ALU_zero_out <= ALU_zero_in;
                ALU_result_out <= ALU_result_in;
                reg_read_data2_out <= reg_read_data2_in;
                EX_MEM_register_rd_out <= ID_EX_register_rd_in;
            end
        end
endmodule

// Data memory 

module data_memory (
    input clk, reset, MemRead, MemWrite,
    input [7:0] addr,
    input [31:0] write_data,
    output [31:0] read_data);

    reg [31:0] data_memory [63:0];
    integer k;

    wire [5:0] shifted_addr;
    assign shifted_addr = addr[7:2];

    assign read_data = (MemRead) ? data_memory[shifted_addr] : 32'bx;

    always @(posedge clk or posedge reset)
    begin
        if (reset == 1'b1) 
        begin

            data_memory[0] = 32'b0000_0000_0000_0000_1111_1111_1111_1111;
            data_memory[1] = 32'b0000_0000_0000_1111_0000_0000_0000_0000;
            data_memory[2] = 32'b0101_0101_0101_0101_0101_0101_0101_0101;

            for (k = 3; k < 64; k = k+1) 
            begin
                data_memory[k] = 32'b0;
            end
        end

        else
            if (MemWrite) 
                data_memory[shifted_addr] = write_data;
    end
endmodule

// To determine if the instruction executing is branch or jump setting PCSrc and PC register accordingly.

module determine_jump_or_branch (
    input Jump, Branch_taken, 
    input [31:0] branch_addr, jump_addr,
    output reg PCSrc,
    output reg [31:0] addr_out);

    always @(Jump or Branch_taken or branch_addr or jump_addr)
    begin

        // If Branch is set, set branch_addr as the next instruction address
        // PCSrc is 1
        if (Branch_taken == 1)
        begin 
            addr_out <= branch_addr;
            PCSrc <= 1; 
        end

        // If Jump is set, set jump_addr as the next instruction address
        // PCSrc is 1
        else if (Jump == 1)
        begin 
            addr_out <= jump_addr;
            PCSrc <= 1;
        end

	// Else PCSrc is set to 0, addr_out does not matter as next instruction address is simply PC + 4
        else 
            begin 
                PCSrc <= 0; 
                addr_out <= 32'b0; 
            end
	end
endmodule

// MEM/WB atate register

module MEM_WB_reg (
    input clk, reset,

    // WB control signal
    input RegWrite_in, MemtoReg_in,

    // Addresses, memory and register contents
    input [31:0] dm_read_data_in, dm_read_addr_in,
    input [4:0] EX_MEM_register_rd_in,

    // Corresponding updated outputs
    output reg RegWrite_out, MemtoReg_out,
    output reg [31:0] dm_read_data_out, dm_read_addr_out,
    output reg [4:0] MEM_WB_register_rd_out);
	
    always @(posedge clk or posedge reset)
    begin
        // Async reset -  reset WB control signals to 0 and clear all addr, data and reg content
        if (reset == 1)
        begin
            RegWrite_out <= 1'b0;
            MemtoReg_out <= 1'b0;
            dm_read_data_out <= 32'b0;
            dm_read_addr_out <= 32'b0;
            MEM_WB_register_rd_out <= 5'b0;
        end

        // Else, proceed normally (retain all values as it is)
        else 
        begin
            RegWrite_out <= RegWrite_in;
            MemtoReg_out <= MemtoReg_in;
            dm_read_data_out <= dm_read_data_in;
            dm_read_addr_out <= dm_read_addr_in;
            MEM_WB_register_rd_out <= EX_MEM_register_rd_in;
        end
    end
endmodule

// Forwarding unit

module forwarding_unit (
    input EX_MEM_RegWrite, MEM_WB_RegWrite, // Forward only if instruction WRITES to reg 
    input [4:0] IF_ID_register_rs,IF_ID_register_rt,
    input [4:0] ID_EX_register_rs, ID_EX_register_rt,
    input [4:0] EX_MEM_register_rd, MEM_WB_register_rd, 

    output reg [1:0] ForwardA, ForwardB);

    wire equal_EXMEM_rs,equal_EXMEM_rt,equal_MEMWB_rs,equal_MEMWB_rt;
    wire nonzero_EXMEM_rd,nonzero_MEMWB_rd;

    // EXE hazard - When an instruction tries to use a register in its EX stage 
    // that an earlier instruction intends to write in its WB stage
    assign equal_EXMEM_rs = (EX_MEM_register_rd == ID_EX_register_rs) ? 1 : 0;
    assign equal_EXMEM_rt = (EX_MEM_register_rd == ID_EX_register_rt)? 1 : 0;

    // MEM hazard - When the Memory and Writeback stages contain matching
    // destination registers  
    assign equal_MEMWB_rs = (MEM_WB_register_rd == ID_EX_register_rs) ? 1 : 0;
    assign equal_MEMWB_rt = (MEM_WB_register_rd == ID_EX_register_rt) ? 1 : 0;

    // Hazard condition - In the event that an instruction in the pipeline has $0 as its destination 
    // - avoid forwarding a possibly nonzero result value.
    assign nonzero_EXMEM_rd = (EX_MEM_register_rd == 0) ? 0 : 1;
    assign nonzero_MEMWB_rd = (MEM_WB_register_rd == 0) ? 0 : 1;

    always@ (EX_MEM_RegWrite or MEM_WB_RegWrite or nonzero_EXMEM_rd or nonzero_MEMWB_rd or equal_EXMEM_rs
    or equal_EXMEM_rt or equal_MEMWB_rs or equal_MEMWB_rt)
    begin

        // EX hazard - The first ALU operand is forwarded from the prior ALU result
        if(EX_MEM_RegWrite & nonzero_EXMEM_rd & equal_EXMEM_rs)
            ForwardA <= 2'b10;

        // MEM hazard - The first ALU operand is forwarded from data memory or an earlier ALU result
        // (more recent result)
        else if (MEM_WB_RegWrite & nonzero_MEMWB_rd & equal_MEMWB_rs)
            ForwardA <= 2'b01;

        // The first ALU operand comes from the register file
        else 
            ForwardA <= 2'b00;
	
        // EX hazard - The second ALU operand is forwarded from the prior ALU result		
        if(EX_MEM_RegWrite & nonzero_EXMEM_rd & equal_EXMEM_rt)
            ForwardB <= 2'b10;

        // MEM hazard - The second ALU operand is forwarded from data memory or an earlier ALU result
        // (more recent result)
        else if (MEM_WB_RegWrite & nonzero_MEMWB_rd & equal_MEMWB_rt)
            ForwardB <= 2'b01;

        // The second ALU operand comes from the register file
        else 
            ForwardB <= 2'b00;
	end
endmodule

// Hazard detection unit for lw - to insert a stall between the load and its use

module lw_stall_unit (
    input ID_EX_MemRead,
    input [4:0] ID_EX_register_rt, IF_ID_register_rs, IF_ID_register_rt,
    output reg PCWrite, IF_ID_write, ID_flush_lw_stall);

    always @ (ID_EX_MemRead or ID_EX_register_rt or IF_ID_register_rs or IF_ID_register_rt)
    begin

        // If the instruction is a load (needs data memory)and if the destination register field of the load in 
        // the EX stage matches either source register of the instruction in the ID stage - STALL
        if(ID_EX_MemRead & ((ID_EX_register_rt == IF_ID_register_rs) | (ID_EX_register_rt == IF_ID_register_rt)))
        begin 
            PCWrite <= 0;           // if instruction in the ID stage is stalled, then the instruction in the IF stage must also be stalled
            IF_ID_write <= 0;       // otherwise, we would lose the fetched instruction - set PCWrite as well as IF/IDwrite to 0  
            ID_flush_lw_stall <= 1; // for stalling in ID stage
        end

        else 
        begin 
            PCWrite <= 1;
            IF_ID_write <= 1;
            ID_flush_lw_stall<=0; 
        end

    end
endmodule

// If branch is taken or a jump instruction is detected at MEM stage - MEMPCSrc set to 1

module branch_and_jump_hazard_unit (
    input MEM_PCSrc, 
    output reg IF_flush, ID_flush_branch, EX_flush);

    always @(MEM_PCSrc)
    begin
        if(MEM_PCSrc)
        begin 
            IF_flush <= 1;      
            ID_flush_branch <=1; 
            EX_flush <=1; 
        end

        else 
        begin 
            IF_flush <= 0; 
            ID_flush_branch <= 0; 
            EX_flush <= 0; 
        end
    end
endmodule


module pipelined_proc (
    input clk, reset, 
    output [31:0] read_data1);

    // Initialize the 32-bit Program Counter Register
    wire [31:0] pc_in;
    wire [31:0] pc_out;
    program_counter #(.N(32)) u0 (.clk(clk), .reset(reset), .PCWrite(PCWrite), .pc_in(pc_in), .pc_out(pc_out)); // PCWrite

    // Fetch the instruction corresponding to the PC address stored in instruction memory
    wire [31:0] instruction;
    instruction_memory u1 (.reset(reset), .read_addr(pc_out), .instruction(instruction));

    // PC = PC + 4, The PC adder is implemented as 32-bit MIPS ALU with ALU control hard wired to ADD, input B to 4 
    wire [31:0] pc_inc4;
    wire carry_out;
    wire zero; 
    ALU_32_bit u2 (.ALU_ctrl(4'b0010), .A(pc_out), .B(32'b0100), .result(pc_inc4), .carry_out(carry_out), .zero(zero));

    // N-bit MUX to select the PC updated depending on the instruction (branch/jump --> PC + offset, other --> PC + 4)
    wire [31:0] branch_jump_addr;
    wire PCsrc;
    mux_N_bit #(.N(32)) u3 (.in0(pc_inc4), .in1(branch_jump_addr), .select(PCSrc), .mux_out(pc_out));

    // IF/ID stage 
    wire [31:0] IF_ID_pc_out;
    wire [31:0] IF_ID_instruction_out;
    IF_ID_reg u4 (.clk(clk), .reset(reset), .IF_ID_write(IF_ID_write), .IF_flush(IF_flush), .pc_inc4_in(pc_inc4), .instruction_in(instruction), .pc_inc4_out(IF_ID_pc_out), .instruction_out(IF_ID_instruction_out));

    // Read/write register file
    wire RegWrite;
    wire [4:0] read_addr1;
    wire [4:0] MEM_WB_register_rd;
    wire [31:0] reg_write_data;
    // wire [31:0] read_data1;
    wire [31:0] read_data2;
    register_file u5 (.clk(clk), .reset(reset), .RegWrite(RegWrite), .read_addr1(read_addr1), .read_addr2(IF_ID_instruction_out[20:16]), .write_addr(MEM_WB_register_rd), .write_data(reg_write_data), .read_data1(read_data1), .read_data2(read_data2));

    // Sign extend immediate operand
    wire [31:0] imm_sign_extended;
    sign_extender u6 (.in(IF_ID_instruction_out[15:0]), .out(imm_sign_extended));

    // If instruction is jump, get jump address from instruction format
    wire [27:0] jump_target;
    left_shifter_jump u7 (.in(IF_ID_instruction_out[25:0]), .out(jump_target));
    wire [31:0] jump_addr;
    assign jump_addr = {IF_ID_pc_out[31:28], jump_target}; 

    // Generate control signals
    wire RegDst; 
    wire Jump; 
    wire Branch; 
    wire MemRead; 
    wire MemtoReg; 
    wire MemWrite; 
    wire ALUSrc; 
    // wire RegWrite;
    wire [1:0] ALU_op;
    main_control u8 (.op_code(IF_ID_instruction_out[31:26]),.RegDst(RegDst), .Jump(Jump), .Branch(Branch), .MemRead(MemRead), .MemtoReg(MemtoReg), .MemWrite(MemWrite), .ALUSrc(ALUSrc), .RegWrite(RegWrite), .ALU_op(ALU_op));

    // ID/EX stage
    wire ID_EX_RegDst, ID_EX_Jump, ID_EX_Branch, ID_EX_MemRead, ID_EX_MemtoReg, ID_EX_MemWrite, ID_EX_ALUSrc, ID_EX_RegWrite;
    wire [1:0] ID_EX_ALUOp;
    wire [31:0] ID_EX_jump_addr;
    wire [31:0] ID_EX_pc_inc4, ID_EX_reg_read_data1, ID_EX_reg_read_data2;
    wire [31:0] ID_EX_imm_sign_extended;
    wire [4:0] ID_EX_register_rs, ID_EX_register_rt, ID_EX_register_rd;
    wire [5:0] ID_EX_funct, ID_EX_opcode;
    ID_EX_reg u9 (.clk(clk), .reset(reset), .ID_flush_lw_stall(ID_flush_lw_stall), .ID_flush_branch(ID_flush_branch), .RegWrite_in(RegWrite), .MemtoReg_in(MemtoReg), .Branch_in(Branch), .MemRead_in(MemRead), .MemWrite_in(MemWrite), .Jump_in(Jump), 
    .RegDst_in(RegDst), .ALUSrc_in(ALUSrc), .ALUOp_in(ALU_op), .jump_addr_in(jump_addr), .pc_inc4_in(IF_ID_pc_out), .IF_ID_register_rs_in(IF_ID_instruction_out[25:21]), .IF_ID_register_rt_in(IF_ID_instruction_out[20:16]), 
    .IF_ID_register_rd_in(IF_ID_instruction_out[15:11]), .IF_ID_funct_in(IF_ID_instruction_out[5:0]), .IF_ID_opcode_in(IF_ID_instruction_out[31:26]), .RegWrite_out(ID_EX_RegWrite), .MemtoReg_out(ID_EX_MemtoReg), 
    .Branch_out(ID_EX_Branch), .MemRead_out(ID_EX_MemRead), .MemWrite_out(ID_EX_MemWrite), .Jump_out(ID_EX_Jump), .reg_read_data1_in(read_data1), .reg_read_data2_in(read_data2), .imm_sign_extended_in(imm_sign_extended),
    .RegDst_out(ID_EX_RegDst), .ALUSrc_out(ID_EX_ALUSrc), .ALUOp_out(ID_EX_ALUOp), .jump_addr_out(ID_EX_jump_addr), .pc_inc4_out(ID_EX_pc_inc4),.reg_read_data1_out(ID_EX_reg_read_data1), .reg_read_data2_out(ID_EX_reg_read_data2), 
    .imm_sign_extended_out(ID_EX_imm_sign_extended), .IF_ID_register_rs_out(ID_EX_register_rs), .IF_ID_register_rt_out(ID_EX_register_rt), .IF_ID_register_rd_out(ID_EX_register_rd), .IF_ID_funct_out(ID_EX_funct), 
    .IF_ID_opcode_out(ID_EX_opcode));
 
    // Mux selects reg
    wire [4:0] EX_register_rd;
    mux_N_bit #(.N(5)) u10 (.in0(ID_EX_register_rt), .in1(ID_EX_register_rd), .select(ID_EX_RegDst), .mux_out(EX_register_rd));

    // ALU control
    wire [3:0] ALU_ctrl;
    ALU_control u11 (.ALU_op(ID_EX_ALUOp), .funct(ID_EX_funct), .op_code(ID_EX_opcode), .ALU_ctrl(ALU_ctrl));

    // Determine ALU inputs
    wire [31:0] muxA_out, muxB_out;
    wire [1:0] ForwardA, ForwardB;
    wire [31:0] EX_MEM_ALU_result;
    mux_N_bit_3to1 #(.N(32)) u12 (.in0(ID_EX_reg_read_data1), .in1(reg_write_data), .in2(EX_MEM_ALU_result), .select(ForwardA), .mux_out(muxA_out)); 
    mux_N_bit_3to1 #(.N(32)) u13 (.in0(ID_EX_reg_read_data2), .in1(reg_write_data), .in2(EX_MEM_ALU_result), .select(ForwardB), .mux_out(muxB_out)); 

    wire [31:0] after_ALUSrc;
    mux_N_bit #(.N(32)) u14 (.in0(muxB_out), .in1(ID_EX_imm_sign_extended), .select(ID_EX_ALUSrc), .mux_out(after_ALUSrc));

    // ALU ops
    wire [31:0] ALU_result;
    wire ALU_zero, ALU_carry_out;
    ALU_32_bit u15 (.ALU_ctrl(ALU_ctrl), .A(muxA_out), .B(after_ALUSrc), .result(ALU_result), .carry_out(ALU_carry_out), .zero(ALU_zero));

    // PC = PC + 4 + branch wd offset - implemented as 32-bit MIPS ALU with ALU control wired to ADD, input B to shifted branch offset 
    wire [31:0] after_shift;
    left_shifter_branch u16 (.in(ID_EX_imm_sign_extended), .out(after_shift));
    wire [31:0] branch_addr;
    ALU_32_bit u17 (.ALU_ctrl(4'b0010), .A(ID_EX_pc_inc4), .B(after_shift), .result(branch_addr), .carry_out(carry_out), .zero(zero));

    // EX/MEM reg
    wire [4:0] EX_MEM_register_rd;
    wire EX_MEM_RegWrite, EX_MEM_MemtoReg, EX_MEM_Branch, EX_MEM_MemRead, EX_MEM_MemWrite, EX_MEM_Jump;
    wire [31:0] EX_MEM_jump_addr, EX_MEM_branch_addr;
    wire EX_MEM_ALU_zero;
    wire [31:0] EX_MEM_reg_read_data2;
    EX_MEM_reg u18 (.clk(clk), .reset(reset), .EX_flush(EX_flush), .RegWrite_in(ID_EX_RegWrite), .MemtoReg_in(ID_EX_MemtoReg), .Branch_in(ID_EX_Branch), 
    .MemRead_in(ID_EX_MemRead), .MemWrite_in(ID_EX_MemWrite), .Jump_in(ID_EX_Jump), .jump_addr_in(ID_EX_jump_addr), .branch_addr_in(branch_addr),
    .ALU_zero_in(ALU_zero), .ALU_result_in(ALU_result), .reg_read_data2_in(muxB_out), .ID_EX_register_rd_in(EX_register_rd), .RegWrite_out(EX_MEM_RegWrite), 
    .MemtoReg_out(EX_MEM_MemtoReg), .Branch_out(EX_MEM_Branch), .MemRead_out(EX_MEM_MemRead), .MemWrite_out(EX_MEM_MemWrite), .Jump_out(EX_MEM_Jump),  
    .jump_addr_out(EX_MEM_jump_addr), .branch_addr_out(EX_MEM_branch_addr), .ALU_zero_out(EX_MEM_ALU_zero), .ALU_result_out(EX_MEM_ALU_result), 
    .reg_read_data2_out(EX_MEM_reg_read_data2), .EX_MEM_register_rd_out(EX_MEM_register_rd));

    // Read/write data memory
    wire [31:0] dm_read_data;
    data_memory u19 ( .clk(clk), .reset(reset), .MemRead(EX_MEM_MemRead), .MemWrite(EX_MEM_MemWrite),.addr(EX_MEM_ALU_result[7:0]), .write_data(EX_MEM_reg_read_data2), .read_data(dm_read_data));
    and (Branch_taken, EX_MEM_Branch, EX_MEM_ALU_zero);

    // Determine branch or jump instruction - if branch/jump set PCSrc and determine PC val 
    // wire [31:0] branch_jump_addr;
    determine_jump_or_branch u20 (.Jump(EX_MEM_Jump), .Branch_taken(Branch_taken), .branch_addr(EX_MEM_branch_addr), .jump_addr(EX_MEM_jump_addr), .PCSrc(PCSrc), .addr_out(branch_jump_addr));

    // MEM/WB state registers
    wire MEM_WB_RegWrite, MEM_WB_MemtoReg;
    wire [31:0] MEM_WB_dm_read_data, MEM_WB_dm_read_addr;
    MEM_WB_reg u21 (.clk(clk), .reset(reset), .RegWrite_in(EX_MEM_RegWrite), .MemtoReg_in(EX_MEM_MemtoReg), .dm_read_data_in(dm_read_data), .dm_read_addr_in(EX_MEM_ALU_result), 
    .EX_MEM_register_rd_in(EX_MEM_register_rd), .RegWrite_out(MEM_WB_RegWrite), .MemtoReg_out(MEM_WB_MemtoReg),  .dm_read_data_out(MEM_WB_dm_read_data), 
    .dm_read_addr_out(MEM_WB_dm_read_addr), .MEM_WB_register_rd_out(MEM_WB_register_rd));
    mux_N_bit #(32) u22 (.in0(MEM_WB_dm_read_addr), .in1(MEM_WB_dm_read_data), .select(MEM_WB_MemtoReg), .mux_out(reg_write_data));

    // Generate forwarding control signals 
    forwarding_unit u23 (.EX_MEM_RegWrite(EX_MEM_RegWrite), .MEM_WB_RegWrite(MEM_WB_RegWrite), .IF_ID_register_rs(IF_ID_instruction_out[25:21]),.IF_ID_register_rt(IF_ID_instruction_out[20:16]),
    .ID_EX_register_rs(ID_EX_register_rs), .ID_EX_register_rt(ID_EX_register_rt), .EX_MEM_register_rd(EX_MEM_register_rd), .MEM_WB_register_rd(MEM_WB_register_rd), 
    .ForwardA(ForwardA), .ForwardB(ForwardB));

    // Detect lw instruction hazard and generate lw stall control accordingly
    lw_stall_unit u24 (.ID_EX_MemRead(ID_EX_MemRead), .ID_EX_register_rt(ID_EX_register_rt), .IF_ID_register_rs(IF_ID_instruction_out[25:21]), .IF_ID_register_rt(IF_ID_instruction_out[20:16]),
    .PCWrite(PCWrite), .IF_ID_write(IF_ID_write), .ID_flush_lw_stall(ID_flush_lw_stall));
    branch_and_jump_hazard_unit u25 (.MEM_PCSrc(PCSrc), .IF_flush(IF_flush), .ID_flush_branch(ID_flush_branch), .EX_flush(EX_flush));

endmodule


module pipelined_processor_tb;

    // Inputs
    reg clk; 
    reg reset;

    // Outputs
    wire [31:0] read_data1;

    pipelined_proc u0 (.clk(clk), .reset(reset), .read_data1(read_data1));

    /////////////////////////////////////////////////////////////////
    // Uncomment lines from this block to check outputs at any stage
    // Initialize the 32-bit Program Counter Register
    /////////////////////////////////////////////////////////////////
/*
    wire [31:0] pc_out;
    program_counter #(.N(32)) u0 (.clk(clk), .reset(reset), .PCWrite(PCWrite), .pc_in(pc_in), .pc_out(pc_out)); // PCWrite

    // Fetch the instruction corresponding to the PC address stored in instruction memory
    wire [31:0] instruction;
    instruction_memory u1 (.reset(reset), .read_addr(pc_out), .instruction(instruction));

    // PC = PC + 4, The PC adder is implemented as 32-bit MIPS ALU with ALU control hard wired to ADD, input B to 4 
    wire [31:0] pc_inc4;
    wire carry_out;
    wire zero; 
    ALU_32_bit u2 (.ALU_ctrl(4'b0010), .A(pc_out), .B(32'b0100), .result(pc_inc4), .carry_out(carry_out), .zero(zero));

    // N-bit MUX to select the PC updated depending on the instruction (branch/jump --> PC + offset, other --> PC + 4)
    wire [31:0] branch_jump_addr;
    wire PCsrc;
    mux_N_bit #(.N(32)) u3 (.in0(pc_inc4), .in1(branch_jump_addr), .select(PCSrc), .mux_out(pc_out));

    // IF/ID stage 
    wire [31:0] IF_ID_pc_out;
    wire [31:0] IF_ID_instruction_out;
    IF_ID_reg u4 (.clk(clk), .reset(reset), .IF_ID_write(IF_ID_write), .IF_flush(IF_flush), .pc_inc4_in(pc_inc4), .instruction_in(instruction), .pc_inc4_out(IF_ID_pc_out), .instruction_out(IF_ID_instruction_out));

    // Read/write register file
    wire RegWrite;
    wire [4:0] read_addr1;
    wire [4:0] MEM_WB_register_rd;
    wire [31:0] reg_write_data;
    wire [31:0] read_data1;
    wire [31:0] read_data2;
    register_file u5 (.clk(clk), .reset(reset), .RegWrite(RegWrite), .read_addr1(read_addr1), .read_addr2(IF_ID_instruction_out[20:16]), .write_addr(MEM_WB_register_rd), .write_data(reg_write_data), .read_data1(read_data1), .read_data2(read_data2));

    // Sign extend immediate operand
    wire [31:0] imm_sign_extended;
    sign_extender u6 (.in(IF_ID_instruction_out[15:0]), .out(imm_sign_extended));

    // If instruction is jump, get jump address from instruction format
    wire [27:0] jump_target;
    left_shifter_jump u7 (.in(IF_ID_instruction_out[25:0]), .out(jump_target));
    wire [31:0] jump_addr;
    assign jump_addr = {IF_ID_pc_out[31:28], jump_target}; 

    // Generate control signals
    wire RegDst; 
    wire Jump; 
    wire Branch; 
    wire MemRead; 
    wire MemtoReg; 
    wire MemWrite; 
    wire ALUSrc; 
    // wire RegWrite;
    wire [1:0] ALU_op;
    main_control u8 (.op_code(IF_ID_instruction_out[31:26]),.RegDst(RegDst), .Jump(Jump), .Branch(Branch), .MemRead(MemRead), .MemtoReg(MemtoReg), .MemWrite(MemWrite), .ALUSrc(ALUSrc), .RegWrite(RegWrite), .ALU_op(ALU_op));

    // ID/EX stage
    wire ID_EX_RegDst, ID_EX_Jump, ID_EX_Branch, ID_EX_MemRead, ID_EX_MemtoReg, ID_EX_MemWrite, ID_EX_ALUSrc, ID_EX_RegWrite;
    wire [1:0] ID_EX_ALUOp;
    wire [31:0] ID_EX_jump_addr;
    wire [31:0] ID_EX_pc_inc4, ID_EX_reg_read_data1, ID_EX_reg_read_data2;
    wire [31:0] ID_EX_imm_sign_extended;
    wire [4:0] ID_EX_register_rs, ID_EX_register_rt, ID_EX_register_rd;
    wire [5:0] ID_EX_funct, ID_EX_opcode;
    ID_EX_reg u9 (.clk(clk), .reset(reset), .ID_flush_lw_stall(ID_flush_lw_stall), .ID_flush_branch(ID_flush_branch), .RegWrite_in(RegWrite), .MemtoReg_in(MemtoReg), .Branch_in(Branch), .MemRead_in(MemRead), .MemWrite_in(MemWrite), .Jump_in(Jump), 
    .RegDst_in(RegDst), .ALUSrc_in(ALUSrc), .ALUOp_in(ALU_op), .jump_addr_in(jump_addr), .pc_inc4_in(IF_ID_pc_out), .IF_ID_register_rs_in(IF_ID_instruction_out[25:21]), .IF_ID_register_rt_in(IF_ID_instruction_out[20:16]), 
    .IF_ID_register_rd_in(IF_ID_instruction_out[15:11]), .IF_ID_funct_in(IF_ID_instruction_out[5:0]), .IF_ID_opcode_in(IF_ID_instruction_out[31:26]), .RegWrite_out(ID_EX_RegWrite), .MemtoReg_out(ID_EX_MemtoReg), 
    .Branch_out(ID_EX_Branch), .MemRead_out(ID_EX_MemRead), .MemWrite_out(ID_EX_MemWrite), .Jump_out(ID_EX_Jump), .reg_read_data1_in(read_data1), .reg_read_data2_in(read_data2), .imm_sign_extended_in(imm_sign_extended),
    .RegDst_out(ID_EX_RegDst), .ALUSrc_out(ID_EX_ALUSrc), .ALUOp_out(ID_EX_ALUOp), .jump_addr_out(ID_EX_jump_addr), .pc_inc4_out(ID_EX_pc_inc4),.reg_read_data1_out(ID_EX_reg_read_data1), .reg_read_data2_out(ID_EX_reg_read_data2), 
    .imm_sign_extended_out(ID_EX_imm_sign_extended), .IF_ID_register_rs_out(ID_EX_register_rs), .IF_ID_register_rt_out(ID_EX_register_rt), .IF_ID_register_rd_out(ID_EX_register_rd), .IF_ID_funct_out(ID_EX_funct), 
    .IF_ID_opcode_out(ID_EX_opcode));
 
    // Mux selects reg
    wire [4:0] EX_register_rd;
    mux_N_bit #(.N(5)) u10 (.in0(ID_EX_register_rt), .in1(ID_EX_register_rd), .select(ID_EX_RegDst), .mux_out(EX_register_rd));

    // ALU control
    wire [3:0] ALU_ctrl;
    ALU_control u11 (.ALU_op(ID_EX_ALUOp), .funct(ID_EX_funct), .op_code(ID_EX_opcode), .ALU_ctrl(ALU_ctrl));

    // Determine ALU inputs
    wire [31:0] muxA_out, muxB_out;
    wire [1:0] ForwardA, ForwardB;
    wire [31:0] EX_MEM_ALU_result;
    mux_N_bit_3to1 #(.N(32)) u12 (.in0(ID_EX_reg_read_data1), .in1(reg_write_data), .in2(EX_MEM_ALU_result), .select(ForwardA), .mux_out(muxA_out)); 
    mux_N_bit_3to1 #(.N(32)) u13 (.in0(ID_EX_reg_read_data2), .in1(reg_write_data), .in2(EX_MEM_ALU_result), .select(ForwardB), .mux_out(muxB_out)); 

    wire [31:0] after_ALUSrc;
    mux_N_bit #(.N(32)) u14 (.in0(muxB_out), .in1(ID_EX_imm_sign_extended), .select(ID_EX_ALUSrc), .mux_out(after_ALUSrc));

    // ALU ops
    wire [31:0] ALU_result;
    wire ALU_zero, ALU_carry_out;
    ALU_32_bit u15 (.ALU_ctrl(ALU_ctrl), .A(muxA_out), .B(after_ALUSrc), .result(ALU_result), .carry_out(ALU_carry_out), .zero(ALU_zero));

    // PC = PC + 4 + branch wd offset - implemented as 32-bit MIPS ALU with ALU control wired to ADD, input B to shifted branch offset 
    wire [31:0] after_shift;
    left_shifter_branch u16 (.in(ID_EX_imm_sign_extended), .out(after_shift));
    wire [31:0] branch_addr;
    ALU_32_bit u17 (.ALU_ctrl(4'b0010), .A(ID_EX_pc_inc4), .B(after_shift), .result(branch_addr), .carry_out(carry_out), .zero(zero));

    // EX/MEM reg
    wire [4:0] EX_MEM_register_rd;
    wire EX_MEM_RegWrite, EX_MEM_MemtoReg, EX_MEM_Branch, EX_MEM_MemRead, EX_MEM_MemWrite, EX_MEM_Jump;
    wire [31:0] EX_MEM_jump_addr, EX_MEM_branch_addr;
    wire EX_MEM_ALU_zero;
    wire [31:0] EX_MEM_reg_read_data2;

    EX_MEM_reg u18 (.clk(clk), .reset(reset), .EX_flush(EX_flush), .RegWrite_in(ID_EX_RegWrite), .MemtoReg_in(ID_EX_MemtoReg), .Branch_in(ID_EX_Branch), 
    .MemRead_in(ID_EX_MemRead), .MemWrite_in(ID_EX_MemWrite), .Jump_in(ID_EX_Jump), .jump_addr_in(ID_EX_jump_addr), .branch_addr_in(branch_addr),
    .ALU_zero_in(ALU_zero), .ALU_result_in(ALU_result), .reg_read_data2_in(muxB_out), .ID_EX_register_rd_in(EX_register_rd), .RegWrite_out(EX_MEM_RegWrite), 
    .MemtoReg_out(EX_MEM_MemtoReg), .Branch_out(EX_MEM_Branch), .MemRead_out(EX_MEM_MemRead), .MemWrite_out(EX_MEM_MemWrite), .Jump_out(EX_MEM_Jump),  
    .jump_addr_out(EX_MEM_jump_addr), .branch_addr_out(EX_MEM_branch_addr), .ALU_zero_out(EX_MEM_ALU_zero), .ALU_result_out(EX_MEM_ALU_result), 
    .reg_read_data2_out(EX_MEM_reg_read_data2), .EX_MEM_register_rd_out(EX_MEM_register_rd));


    // Read/write data memory
    wire [31:0] dm_read_data;
    data_memory u19 ( .clk(clk), .reset(reset), .MemRead(EX_MEM_MemRead), .MemWrite(EX_MEM_MemWrite),.addr(EX_MEM_ALU_result[7:0]), .write_data(EX_MEM_reg_read_data2), .read_data(dm_read_data));
    and (Branch_taken, EX_MEM_Branch, EX_MEM_ALU_zero);

    // Determine branch or jump instruction - if branch/jump set PCSrc and determine PC val 
    // wire [31:0] branch_jump_addr;
    determine_jump_or_branch u20 (.Jump(EX_MEM_Jump), .Branch_taken(Branch_taken), .branch_addr(EX_MEM_branch_addr), .jump_addr(EX_MEM_jump_addr), .PCSrc(PCSrc), .addr_out(branch_jump_addr));


    // MEM/WB state registers
    wire MEM_WB_RegWrite, MEM_WB_MemtoReg;
    wire [31:0] MEM_WB_dm_read_data, MEM_WB_dm_read_addr;
    MEM_WB_reg u21 (.clk(clk), .reset(reset), .RegWrite_in(EX_MEM_RegWrite), .MemtoReg_in(EX_MEM_MemtoReg), .dm_read_data_in(dm_read_data), .dm_read_addr_in(EX_MEM_ALU_result), 
    .EX_MEM_register_rd_in(EX_MEM_register_rd), .RegWrite_out(MEM_WB_RegWrite), .MemtoReg_out(MEM_WB_MemtoReg),  .dm_read_data_out(MEM_WB_dm_read_data), 
    .dm_read_addr_out(MEM_WB_dm_read_addr), .MEM_WB_register_rd_out(MEM_WB_register_rd));

    mux_N_bit #(32) u22 (.in0(MEM_WB_dm_read_addr), .in1(MEM_WB_dm_read_data), .select(MEM_WB_MemtoReg), .mux_out(reg_write_data));

    // Generate forwarding control signals 
    forwarding_unit u23 (.EX_MEM_RegWrite(EX_MEM_RegWrite), .MEM_WB_RegWrite(MEM_WB_RegWrite), .IF_ID_register_rs(IF_ID_instruction_out[25:21]),.IF_ID_register_rt(IF_ID_instruction_out[20:16]),
    .ID_EX_register_rs(ID_EX_register_rs), .ID_EX_register_rt(ID_EX_register_rt), .EX_MEM_register_rd(EX_MEM_register_rd), .MEM_WB_register_rd(MEM_WB_register_rd), 
    .ForwardA(ForwardA), .ForwardB(ForwardB));

    // Detect lw instruction hazard and generate lw stall control accordingly
    lw_stall_unit u24 (.ID_EX_MemRead(ID_EX_MemRead), .ID_EX_register_rt(ID_EX_register_rt), .IF_ID_register_rs(IF_ID_instruction_out[25:21]), .IF_ID_register_rt(IF_ID_instruction_out[20:16]),
    .PCWrite(PCWrite), .IF_ID_write(IF_ID_write), .ID_flush_lw_stall(ID_flush_lw_stall));

    branch_and_jump_hazard_unit u25 (.MEM_PCSrc(PCSrc), .IF_flush(IF_flush), .ID_flush_branch(ID_flush_branch), .EX_flush(EX_flush));
*/
    always
        #5 clk = ~clk;
    initial
    begin
        clk = 0; 
        reset = 1;

        #5 reset = 0;
 
        #300 $finish;
    end
endmodule
