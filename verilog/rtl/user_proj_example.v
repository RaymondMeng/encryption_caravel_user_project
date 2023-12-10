// SPDX-FileCopyrightText: 2020 Efabless Corporation
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// SPDX-License-Identifier: Apache-2.0

`default_nettype none
/*
 *-------------------------------------------------------------
 *
 * user_proj_example
 *
 * This is an example of a (trivially simple) user project,
 * showing how the user project can connect to the logic
 * analyzer, the wishbone bus, and the I/O pads.
 *
 * This project generates an integer count, which is output
 * on the user area GPIO pads (digital output only).  The
 * wishbone connection allows the project to be controlled
 * (start and stop) from the management SoC program.
 *
 * See the testbenches in directory "mprj_counter" for the
 * example programs that drive this user project.  The three
 * testbenches are "io_ports", "la_test1", and "la_test2".
 *
 *-------------------------------------------------------------
 */

module user_proj_example #(
    parameter BITS = 16
)(
`ifdef USE_POWER_PINS
    inout vdd,	// User area 1 1.8V supply
    inout vss,	// User area 1 digital ground
`endif

    // Wishbone Slave ports (WB MI A)
    input wb_clk_i,
    input wb_rst_i,
    input wbs_stb_i,
    input wbs_cyc_i,
    input wbs_we_i, //1:write 0:read
    input [3:0] wbs_sel_i,
    input [31:0] wbs_dat_i,
    input [31:0] wbs_adr_i, //wbs reg offset address
    output wbs_ack_o,
    output [31:0] wbs_dat_o,

    // Logic Analyzer Signals
    input  [63:0] la_data_in,
    output [63:0] la_data_out,
    input  [63:0] la_oenb,

    // IOs
    input  [BITS-1:0] io_in,
    output [BITS-1:0] io_out,
    output [BITS-1:0] io_oeb,

    // IRQ
    output [2:0] irq
);
    //wire clk;
    //wire rst;

    //wire [BITS-1:0] rdata; 
    //wire [BITS-1:0] wdata;
    //wire [BITS-1:0] count;

    //wire valid;
    //wire [3:0] wstrb;
    //wire [BITS-1:0] la_write;

    // WB MI A
    //assign valid = wbs_cyc_i && wbs_stb_i; 
    //assign wstrb = wbs_sel_i & {4{wbs_we_i}}; //select which byte can be wrote
    //assign wbs_dat_o = {{(32-BITS){1'b0}}, rdata};
    //assign wdata = wbs_dat_i[BITS-1:0];

    // IO
    //assign io_out = count;
    //assign io_oeb = {(BITS){rst}};

    //IO
    assign io_oeb = {(BITS){wb_rst_i}};

    // IRQ
    assign irq = 3'b000;	// Unused

    // LA
    assign la_data_out = {{(64-BITS){1'b0}}, io_out};
    // Assuming LA probes [61:46] are for controlling the count register  
    //assign la_write = ~la_oenb[61:62-BITS] & ~{BITS{valid}};
    // Assuming LA probes [63:62] are for controlling the count clk & reset  
    //assign clk = (~la_oenb[62]) ? la_data_in[62]: wb_clk_i;
    //assign rst = (~la_oenb[63]) ? la_data_in[63]: wb_rst_i;

    DES_WB DES_WB_inst(
    .clk(wb_clk_i),
    .rst_n(~wb_rst_i),
    .wbs_stb_i(wbs_stb_i),
    .wbs_cyc_i(wbs_cyc_i),
    .wbs_we_i(wbs_we_i), //1:write 0:read
    .wbs_sel_i(wbs_sel_i),
    .wbs_dat_i(wbs_dat_i),
    .wbs_adr_i(wbs_adr_i), //wbs reg offset address
    .wbs_ack_o(wbs_ack_o),
    .wbs_dat_o(wbs_dat_o),
    .io_out(io_out)
    );

    // counter #(
    //     .BITS(BITS)
    // ) counter(
    //     .clk(clk),
    //     .reset(rst),
    //     .ready(wbs_ack_o),
    //     .valid(valid),
    //     .rdata(rdata),
    //     .wdata(wbs_dat_i[BITS-1:0]),
    //     .wstrb(wstrb),
    //     .la_write(la_write),
    //     .la_input(la_data_in[61:62-BITS]),
    //     .count(count)
    // );

endmodule

// module counter #(
//     parameter BITS = 16
// )(
//     input clk,
//     input reset,
//     input valid,
//     input [3:0] wstrb,
//     input [BITS-1:0] wdata,
//     input [BITS-1:0] la_write,
//     input [BITS-1:0] la_input,
//     output reg ready,
//     output reg [BITS-1:0] rdata,
//     output reg [BITS-1:0] count
// );

//     always @(posedge clk) begin
//         if (reset) begin
//             count <= 0;
//             ready <= 0;
//         end else begin
//             ready <= 1'b0;
//             if (~|la_write) begin
//                 count <= count + 1;
//             end
//             if (valid && !ready) begin //read valid but not ready to output
//                 ready <= 1'b1; //ready to output 
//                 rdata <= count;
//                 if (wstrb[0]) count[7:0]   <= wdata[7:0];
//                 if (wstrb[1]) count[15:8]  <= wdata[15:8];
//             end else if (|la_write) begin //if logic analyze write
//                 count <= la_write & la_input;
//             end
//         end
//     end

// endmodule

module DES_WB(
    input clk,
    input rst_n,
    input wbs_stb_i,
    input wbs_cyc_i,
    input wbs_we_i, //1:write 0:read
    input [3:0] wbs_sel_i,
    input [31:0] wbs_dat_i,
    input [31:0] wbs_adr_i, //wbs reg offset address
    output wbs_ack_o,
    output [31:0] wbs_dat_o,
    output [15:0] io_out
    );

wire valid;
wire [3:0] wstrb;
wire [31:0] wdata;
reg [31:0] rdata;
wire dat_valid;
reg ready; //ready to output
wire wbs_rst_n;

//————————————————————————————————————————
// 31~24  |  23~16  |  15~8  |    7~0    |
//unused     MODE     START     FINISH 
reg [31:0] CFG_REG;
reg [31:0] RECEIVE_H32, RECEIVE_L32;
reg [31:0] KEY_H32, KEY_L32;
wire [31:0] TRANSMIT_H32, TRANSMIT_L32;
wire [63:0] key_din;
wire [63:0] din;

wire mode, start;
reg finish;

assign valid = wbs_cyc_i && wbs_stb_i; //master request valid
assign wstrb = wbs_sel_i & {4{wbs_we_i}}; //select which byte can be wrote
assign wbs_dat_o = rdata;
assign wdata = wbs_dat_i[31:0];
assign wbs_ack_o = ready; //ready to ack
assign mode = CFG_REG[16];
assign start = CFG_REG[8];
assign wbs_rst_n = rst_n;

always @(posedge clk) begin
    if (wbs_rst_n == 1'b0) begin //wbs sync
        ready <= 1'b0;
        CFG_REG <= {31'd0, finish};
        RECEIVE_H32 <= 'd0;
        RECEIVE_L32 <= 'd0;
        KEY_H32 <= 'd0;
        KEY_L32 <= 'd0;
        rdata <= 'd0;
    end
    else begin
        if (valid & ~ready) begin   //思路应该是首先按地址分情况讨论，然后在该地址上按sel使能字节
            CFG_REG[0] <= finish;
            if (wbs_we_i) begin //write
                ready <= 1'b1;
                case (wbs_adr_i)
                    32'h0: CFG_REG[23:8] <= {{8{wstrb[2]}} & wdata[23:16], {8{wstrb[1]}} & wdata[15:8]}; //写入的时候需要考虑写入哪个字节
                    32'hc: RECEIVE_H32 <= wdata;
                    32'h10: RECEIVE_L32 <= wdata;
                    32'h14: KEY_H32 <= wdata; 
                    32'h18: KEY_L32 <= wdata;
                endcase
            end
            else if (!wbs_we_i) begin //read
                ready <= 1'b1;
                case (wbs_adr_i)
                    32'h0:  rdata <= CFG_REG; //读取的时候直接32位，在soc中用户自己截取字节
                    32'h4:  rdata <= TRANSMIT_H32;
                    32'h8:  rdata <= TRANSMIT_L32;
                    32'hc:  rdata <= RECEIVE_H32;
                    32'h10: rdata <= RECEIVE_L32;
                    32'h14: rdata <= KEY_H32;
                    32'h18: rdata <= KEY_L32;
                endcase
            end        
        end
        else begin
            ready <= 1'b0;
            CFG_REG <= CFG_REG;
            RECEIVE_H32 <= RECEIVE_H32;
            RECEIVE_L32 <= RECEIVE_L32;
            KEY_H32 <= KEY_H32;
            KEY_L32 <= KEY_L32;
        end
    end
end

assign key_din = {KEY_H32, KEY_L32};
assign din = {RECEIVE_H32, RECEIVE_L32};
//assign finish = start ? (dat_valid ? 1'b1 : finish) : 1'b0; 
assign io_out = TRANSMIT_L32[15:0];

always @(posedge clk) begin
    if (start) begin
        if (dat_valid) begin
            finish <= 1'b1;
        end
        else begin
            finish <= finish;
        end
    end
    else begin
        finish <= 1'b0;
    end
end

DES_top DES_top_inst(
    .clk(clk),
    .rst_n(rst_n),
    .mode(mode), //0:加密 1:解密
    .key_din(key_din),
    .start(start), //1:start
    .din(din),
    .dout({TRANSMIT_H32, TRANSMIT_L32}),
    .dat_valid(dat_valid)
);

endmodule

module DES_top (
    input      [63:0] din,
    input             clk,
    input             start,
    input             rst_n,
    input             mode, //0:加密 1:解密
    input      [63:0] key_din,
    output reg [63:0] dout,
    output            dat_valid
);

wire [4:0]  cnt_out;
reg         cnt_end;
wire [31:0] f_out;
wire [31:0] R_dat_out, L_dat_out;
wire [47:0] round_key_out;
reg  [31:0] L_init, R_init;
// wire [63:0] plain_text, cipher_text;
reg  [63:0] Permutation_init_din, Permutation_inverse_din;
wire [63:0] Permutation_init_dout, Permutation_inverse_dout;
reg  [4:0]  keygen_cnt;
reg  [4:0]  cnt;
reg         start_d;
reg         cnt_start;
wire        start_valid;


reg  [1:0] state, next_state;
localparam [1:0] IDLE = 2'b00, ENCRY = 2'b01, DECRY = 2'b11;

always @(posedge clk or negedge rst_n) begin
    if (rst_n == 1'b0) begin
        state <= IDLE;
    end
    else begin
        state <= next_state;
    end
end

always @(*) begin
    case (state)
        IDLE: next_state = mode ? DECRY : ENCRY;
        DECRY: next_state = mode ? DECRY : ENCRY;
        ENCRY: next_state = mode ? DECRY : ENCRY; 
        default: next_state = IDLE;
    endcase
end

always @(*) begin
    if (state == DECRY && cnt_start) begin
        keygen_cnt = 'd17 - cnt_out;
    end
    else if (state == ENCRY && cnt_start)begin
        keygen_cnt = cnt_out;
    end
    else begin
        keygen_cnt = 'd0;
    end
end

always @(*) begin
    Permutation_init_din = din;
    Permutation_inverse_din = {R_dat_out, L_dat_out}; //注意最后的p变换LR的位置反过来
    {L_init, R_init} = Permutation_init_dout;
end

always @(posedge clk or negedge rst_n) begin
    if (rst_n == 1'b0)
        dout <= 'd0;
    else begin
        if(dat_valid)
            dout <= Permutation_inverse_dout;
        else
            dout <= dout;
    end 
end

assign start_valid = start & ~start_d;
always @(posedge clk) begin
    start_d <= start;
end

always @(posedge clk or negedge rst_n) begin
    if (rst_n == 1'b0) begin
        cnt <= 'd0;
        cnt_end <= 1'b0;
    end
    else begin
        if (cnt_start == 1'b1) begin
            if(cnt < 'd17) begin
                cnt <= cnt + 1'b1;
                cnt_end <= (cnt == 'd16);
            end
            else begin
                cnt_end <= 1'b1;
                cnt <= cnt;
            end
        end
        else begin
            cnt_end <= 1'b0;
            cnt <= 'd0;
        end
    end
end
assign cnt_out = cnt;
//assign cnt_start = cnt_end ? 1'b0 : ((start_d == 1'b1 && cnt_end == 1'b0) ? 1'b1 : cnt_start);
always @(posedge clk or negedge rst_n) begin
    if (rst_n == 1'b0) begin
        cnt_start <= 1'b0;
    end
    else begin
        if (cnt_end) begin
            cnt_start <= 1'b0;
        end
        else if (start_valid == 1'b1 && cnt_end == 1'b0) begin
            cnt_start <= 1'b1;
        end
        else begin
            cnt_start <= cnt_start;
        end
    end 
end

// assign Permutation_init_din = (state == DECRY) ? {L_dat_out, R_dat_out} : ((state == ENCRY) ? plain_text : 'd0);
// assign Permutation_init_dout = ()

Permutation_init Permutation_init_inst(
    .dat_in(Permutation_init_din),
    .dat_out(Permutation_init_dout)
);

Round round_inst(
    .R_dat(R_dat_out),
    .key_dat(round_key_out),
    .f_out(f_out)
);

mux mux_inst(
    .clk(clk),
    .rst_n(rst_n),
    .f_out(f_out),
    .L_init(L_init),
    .R_init(R_init),
    .cnt(cnt_out),
    .R_dat(R_dat_out),
    .L_dat(L_dat_out),
    .lst_valid(dat_valid)
);

Permutation_inverse Permutation_inverse_inst(
    .dat_in(Permutation_inverse_din),
    .dat_out(Permutation_inverse_dout)
);

keygen keygen_inst(
    .cnt(keygen_cnt),
    .key(key_din),
    .round_key(round_key_out)
    );

endmodule

module Permutation_init(
    input  [63:0] dat_in,
    output [63:0] dat_out
    );

assign dat_out = {dat_in[6], dat_in[14], dat_in[22], dat_in[30], dat_in[38], dat_in[46], dat_in[54], dat_in[62], dat_in[4], dat_in[12], dat_in[20], dat_in[28], dat_in[36], dat_in[44], dat_in[52], dat_in[60], dat_in[2], dat_in[10], dat_in[18], dat_in[26], dat_in[34], dat_in[42], dat_in[50], dat_in[58], dat_in[0], dat_in[8], dat_in[16], dat_in[24], dat_in[32], dat_in[40], dat_in[48], dat_in[56], dat_in[7], dat_in[15], dat_in[23], dat_in[31], dat_in[39], dat_in[47], dat_in[55], dat_in[63], dat_in[5], dat_in[13], dat_in[21], dat_in[29], dat_in[37], dat_in[45], dat_in[53], dat_in[61], dat_in[3], dat_in[11], dat_in[19], dat_in[27], dat_in[35], dat_in[43], dat_in[51], dat_in[59], dat_in[1], dat_in[9], dat_in[17], dat_in[25], dat_in[33], dat_in[41], dat_in[49], dat_in[57] };

endmodule

module Round(
    input      [31:0] R_dat,
    input      [47:0] key_dat,
    output     [31:0] f_out
    );

wire [47:0] extension_out;
wire [47:0] xor_out;
wire [31:0] s_box_out;
wire [31:0] round_p_out;

extension extension_inst(.dat_in(R_dat), .dat_out(extension_out));

assign xor_out = extension_out ^ key_dat;

s_box s_box_inst(.dat_in(xor_out), .dat_out(s_box_out));

round_p round_p_inst(.dat_in(s_box_out), .dat_out(round_p_out));

assign f_out = round_p_out;
// always @(posedge clk) begin
//     f_out <= round_p_out;
// end

endmodule

module extension(
    input  [31:0] dat_in,
    output [47:0] dat_out
    );

assign dat_out = {dat_in[0], dat_in[31:27], dat_in[28:23], dat_in[24:19], dat_in[20:15], dat_in[16:11], dat_in[12:7], dat_in[8:3], dat_in[4:0], dat_in[31]};

endmodule

module s_box(
    input  [47:0] dat_in,
    output [31:0] dat_out
    );

wire [3:0] sb1_out, sb2_out, sb3_out, sb4_out, sb5_out, sb6_out, sb7_out, sb8_out;

sbox1_lut sbox1_lut_inst(.line({dat_in[47], dat_in[42]}), .column(dat_in[46:43]), .dout(sb1_out));
sbox2_lut sbox2_lut_inst(.line({dat_in[41], dat_in[36]}), .column(dat_in[40:37]), .dout(sb2_out));
sbox3_lut sbox3_lut_inst(.line({dat_in[35], dat_in[30]}), .column(dat_in[34:31]), .dout(sb3_out));
sbox4_lut sbox4_lut_inst(.line({dat_in[29], dat_in[24]}), .column(dat_in[28:25]), .dout(sb4_out));
sbox5_lut sbox5_lut_inst(.line({dat_in[23], dat_in[18]}), .column(dat_in[22:19]), .dout(sb5_out));
sbox6_lut sbox6_lut_inst(.line({dat_in[17], dat_in[12]}), .column(dat_in[16:13]), .dout(sb6_out));
sbox7_lut sbox7_lut_inst(.line({dat_in[11], dat_in[6]}), .column(dat_in[10:7]), .dout(sb7_out));
sbox8_lut sbox8_lut_inst(.line({dat_in[5], dat_in[0]}), .column(dat_in[4:1]), .dout(sb8_out));

assign dat_out = {sb1_out, sb2_out, sb3_out, sb4_out, sb5_out, sb6_out, sb7_out, sb8_out};

endmodule

module sbox1_lut(
    input      [1:0] line,
    input      [3:0] column,
    output reg [3:0] dout
    );

always @(*) begin
    case ({line, column})
        6'b000000: dout = 'd14;
        6'b000001: dout = 'd4;
        6'b000010: dout = 'd13;
        6'b000011: dout = 'd1;
        6'b000100: dout = 'd2;
        6'b000101: dout = 'd15;
        6'b000110: dout = 'd11;
        6'b000111: dout = 'd8;
        6'b001000: dout = 'd3;
        6'b001001: dout = 'd10;
        6'b001010: dout = 'd6;
        6'b001011: dout = 'd12;
        6'b001100: dout = 'd5;
        6'b001101: dout = 'd9;
        6'b001110: dout = 'd0;
        6'b001111: dout = 'd7;
        6'b010000: dout = 'd0;
        6'b010001: dout = 'd15;
        6'b010010: dout = 'd7;
        6'b010011: dout = 'd4;
        6'b010100: dout = 'd14;
        6'b010101: dout = 'd2;
        6'b010110: dout = 'd13;
        6'b010111: dout = 'd1;
        6'b011000: dout = 'd10;
        6'b011001: dout = 'd6;
        6'b011010: dout = 'd12;
        6'b011011: dout = 'd11;
        6'b011100: dout = 'd9;
        6'b011101: dout = 'd5;
        6'b011110: dout = 'd3;
        6'b011111: dout = 'd8;
        6'b100000: dout = 'd4;
        6'b100001: dout = 'd1;
        6'b100010: dout = 'd14;
        6'b100011: dout = 'd8;
        6'b100100: dout = 'd13;
        6'b100101: dout = 'd6;
        6'b100110: dout = 'd2;
        6'b100111: dout = 'd11;
        6'b101000: dout = 'd15;
        6'b101001: dout = 'd12;
        6'b101010: dout = 'd9;
        6'b101011: dout = 'd7;
        6'b101100: dout = 'd3;
        6'b101101: dout = 'd10;
        6'b101110: dout = 'd5;
        6'b101111: dout = 'd0;
        6'b110000: dout = 'd15;
        6'b110001: dout = 'd12;
        6'b110010: dout = 'd8;
        6'b110011: dout = 'd2;
        6'b110100: dout = 'd4;
        6'b110101: dout = 'd9;
        6'b110110: dout = 'd1;
        6'b110111: dout = 'd7;
        6'b111000: dout = 'd5;
        6'b111001: dout = 'd11;
        6'b111010: dout = 'd3;
        6'b111011: dout = 'd14;
        6'b111100: dout = 'd10;
        6'b111101: dout = 'd0;
        6'b111110: dout = 'd6;
        6'b111111: dout = 'd13;
    endcase
end

endmodule

module sbox2_lut(
    input      [1:0] line,
    input      [3:0] column,
    output reg [3:0] dout
);

always @(*) begin
    case ({line, column})
        6'b000000: dout = 'd15;
        6'b000001: dout = 'd1;
        6'b000010: dout = 'd8;
        6'b000011: dout = 'd14;
        6'b000100: dout = 'd6;
        6'b000101: dout = 'd11;
        6'b000110: dout = 'd3;
        6'b000111: dout = 'd4;
        6'b001000: dout = 'd9;
        6'b001001: dout = 'd7;
        6'b001010: dout = 'd2;
        6'b001011: dout = 'd13;
        6'b001100: dout = 'd12;
        6'b001101: dout = 'd0;
        6'b001110: dout = 'd5;
        6'b001111: dout = 'd10;
        6'b010000: dout = 'd3;
        6'b010001: dout = 'd13;
        6'b010010: dout = 'd4;
        6'b010011: dout = 'd7;
        6'b010100: dout = 'd15;
        6'b010101: dout = 'd2;
        6'b010110: dout = 'd8;
        6'b010111: dout = 'd14;
        6'b011000: dout = 'd12;
        6'b011001: dout = 'd0;
        6'b011010: dout = 'd1;
        6'b011011: dout = 'd10;
        6'b011100: dout = 'd6;
        6'b011101: dout = 'd9;
        6'b011110: dout = 'd11;
        6'b011111: dout = 'd5;
        6'b100000: dout = 'd0;
        6'b100001: dout = 'd14;
        6'b100010: dout = 'd7;
        6'b100011: dout = 'd11;
        6'b100100: dout = 'd10;
        6'b100101: dout = 'd4;
        6'b100110: dout = 'd13;
        6'b100111: dout = 'd1;
        6'b101000: dout = 'd5;
        6'b101001: dout = 'd8;
        6'b101010: dout = 'd12;
        6'b101011: dout = 'd6;
        6'b101100: dout = 'd9;
        6'b101101: dout = 'd3;
        6'b101110: dout = 'd2;
        6'b101111: dout = 'd15;
        6'b110000: dout = 'd13;
        6'b110001: dout = 'd8;
        6'b110010: dout = 'd10;
        6'b110011: dout = 'd1;
        6'b110100: dout = 'd3;
        6'b110101: dout = 'd15;
        6'b110110: dout = 'd4;
        6'b110111: dout = 'd2;
        6'b111000: dout = 'd11;
        6'b111001: dout = 'd6;
        6'b111010: dout = 'd7;
        6'b111011: dout = 'd12;
        6'b111100: dout = 'd0;
        6'b111101: dout = 'd5;
        6'b111110: dout = 'd14;
        6'b111111: dout = 'd9;
    endcase
end

endmodule

module sbox3_lut(
    input      [1:0] line,
    input      [3:0] column,
    output reg [3:0] dout
);

always @(*) begin
    case ({line, column})
        6'b000000: dout = 'd10;
        6'b000001: dout = 'd0;
        6'b000010: dout = 'd9;
        6'b000011: dout = 'd14;
        6'b000100: dout = 'd6;
        6'b000101: dout = 'd3;
        6'b000110: dout = 'd15;
        6'b000111: dout = 'd5;
        6'b001000: dout = 'd1;
        6'b001001: dout = 'd13;
        6'b001010: dout = 'd12;
        6'b001011: dout = 'd7;
        6'b001100: dout = 'd11;
        6'b001101: dout = 'd4;
        6'b001110: dout = 'd2;
        6'b001111: dout = 'd8;
        6'b010000: dout = 'd13;
        6'b010001: dout = 'd7;
        6'b010010: dout = 'd0;
        6'b010011: dout = 'd9;
        6'b010100: dout = 'd3;
        6'b010101: dout = 'd4;
        6'b010110: dout = 'd6;
        6'b010111: dout = 'd10;
        6'b011000: dout = 'd2;
        6'b011001: dout = 'd8;
        6'b011010: dout = 'd5;
        6'b011011: dout = 'd14;
        6'b011100: dout = 'd12;
        6'b011101: dout = 'd11;
        6'b011110: dout = 'd15;
        6'b011111: dout = 'd1;
        6'b100000: dout = 'd13;
        6'b100001: dout = 'd6;
        6'b100010: dout = 'd4;
        6'b100011: dout = 'd9;
        6'b100100: dout = 'd8;
        6'b100101: dout = 'd15;
        6'b100110: dout = 'd3;
        6'b100111: dout = 'd0;
        6'b101000: dout = 'd11;
        6'b101001: dout = 'd1;
        6'b101010: dout = 'd2;
        6'b101011: dout = 'd12;
        6'b101100: dout = 'd5;
        6'b101101: dout = 'd10;
        6'b101110: dout = 'd14;
        6'b101111: dout = 'd7;
        6'b110000: dout = 'd1;
        6'b110001: dout = 'd10;
        6'b110010: dout = 'd13;
        6'b110011: dout = 'd0;
        6'b110100: dout = 'd6;
        6'b110101: dout = 'd9;
        6'b110110: dout = 'd8;
        6'b110111: dout = 'd7;
        6'b111000: dout = 'd4;
        6'b111001: dout = 'd15;
        6'b111010: dout = 'd14;
        6'b111011: dout = 'd3;
        6'b111100: dout = 'd11;
        6'b111101: dout = 'd5;
        6'b111110: dout = 'd2;
        6'b111111: dout = 'd12;
    endcase
end

endmodule

module sbox4_lut(
    input      [1:0] line,
    input      [3:0] column,
    output reg [3:0] dout
);

always @(*) begin
    case ({line, column})
        6'b000000: dout = 'd7;
        6'b000001: dout = 'd13;
        6'b000010: dout = 'd14;
        6'b000011: dout = 'd3;
        6'b000100: dout = 'd0;
        6'b000101: dout = 'd6;
        6'b000110: dout = 'd9;
        6'b000111: dout = 'd10;
        6'b001000: dout = 'd1;
        6'b001001: dout = 'd2;
        6'b001010: dout = 'd8;
        6'b001011: dout = 'd5;
        6'b001100: dout = 'd11;
        6'b001101: dout = 'd12;
        6'b001110: dout = 'd4;
        6'b001111: dout = 'd15;
        6'b010000: dout = 'd13;
        6'b010001: dout = 'd8;
        6'b010010: dout = 'd11;
        6'b010011: dout = 'd5;
        6'b010100: dout = 'd6;
        6'b010101: dout = 'd15;
        6'b010110: dout = 'd0;
        6'b010111: dout = 'd3;
        6'b011000: dout = 'd4;
        6'b011001: dout = 'd7;
        6'b011010: dout = 'd2;
        6'b011011: dout = 'd12;
        6'b011100: dout = 'd1;
        6'b011101: dout = 'd10;
        6'b011110: dout = 'd14;
        6'b011111: dout = 'd9;
        6'b100000: dout = 'd10;
        6'b100001: dout = 'd6;
        6'b100010: dout = 'd9;
        6'b100011: dout = 'd0;
        6'b100100: dout = 'd12;
        6'b100101: dout = 'd11;
        6'b100110: dout = 'd7;
        6'b100111: dout = 'd13;
        6'b101000: dout = 'd15;
        6'b101001: dout = 'd1;
        6'b101010: dout = 'd3;
        6'b101011: dout = 'd14;
        6'b101100: dout = 'd5;
        6'b101101: dout = 'd2;
        6'b101110: dout = 'd8;
        6'b101111: dout = 'd4;
        6'b110000: dout = 'd3;
        6'b110001: dout = 'd15;
        6'b110010: dout = 'd0;
        6'b110011: dout = 'd6;
        6'b110100: dout = 'd10;
        6'b110101: dout = 'd1;
        6'b110110: dout = 'd13;
        6'b110111: dout = 'd8;
        6'b111000: dout = 'd9;
        6'b111001: dout = 'd4;
        6'b111010: dout = 'd5;
        6'b111011: dout = 'd11;
        6'b111100: dout = 'd12;
        6'b111101: dout = 'd7;
        6'b111110: dout = 'd2;
        6'b111111: dout = 'd14;
    endcase
end

endmodule

module sbox5_lut(
    input      [1:0] line,
    input      [3:0] column,
    output reg [3:0] dout
);

always @(*) begin
    case ({line, column})
        6'b000000: dout = 'd2;
        6'b000001: dout = 'd12;
        6'b000010: dout = 'd4;
        6'b000011: dout = 'd1;
        6'b000100: dout = 'd7;
        6'b000101: dout = 'd10;
        6'b000110: dout = 'd11;
        6'b000111: dout = 'd6;
        6'b001000: dout = 'd8;
        6'b001001: dout = 'd5;
        6'b001010: dout = 'd3;
        6'b001011: dout = 'd15;
        6'b001100: dout = 'd13;
        6'b001101: dout = 'd0;
        6'b001110: dout = 'd14;
        6'b001111: dout = 'd9;
        6'b010000: dout = 'd14;
        6'b010001: dout = 'd11;
        6'b010010: dout = 'd2;
        6'b010011: dout = 'd12;
        6'b010100: dout = 'd4;
        6'b010101: dout = 'd7;
        6'b010110: dout = 'd13;
        6'b010111: dout = 'd1;
        6'b011000: dout = 'd5;
        6'b011001: dout = 'd0;
        6'b011010: dout = 'd15;
        6'b011011: dout = 'd10;
        6'b011100: dout = 'd3;
        6'b011101: dout = 'd9;
        6'b011110: dout = 'd8;
        6'b011111: dout = 'd6;
        6'b100000: dout = 'd4;
        6'b100001: dout = 'd2;
        6'b100010: dout = 'd1;
        6'b100011: dout = 'd11;
        6'b100100: dout = 'd10;
        6'b100101: dout = 'd13;
        6'b100110: dout = 'd7;
        6'b100111: dout = 'd8;
        6'b101000: dout = 'd15;
        6'b101001: dout = 'd9;
        6'b101010: dout = 'd12;
        6'b101011: dout = 'd5;
        6'b101100: dout = 'd6;
        6'b101101: dout = 'd3;
        6'b101110: dout = 'd0;
        6'b101111: dout = 'd14;
        6'b110000: dout = 'd11;
        6'b110001: dout = 'd8;
        6'b110010: dout = 'd12;
        6'b110011: dout = 'd7;
        6'b110100: dout = 'd1;
        6'b110101: dout = 'd14;
        6'b110110: dout = 'd2;
        6'b110111: dout = 'd13;
        6'b111000: dout = 'd6;
        6'b111001: dout = 'd15;
        6'b111010: dout = 'd0;
        6'b111011: dout = 'd9;
        6'b111100: dout = 'd10;
        6'b111101: dout = 'd4;
        6'b111110: dout = 'd5;
        6'b111111: dout = 'd3;
    endcase
end

endmodule

module sbox6_lut(
    input      [1:0] line,
    input      [3:0] column,
    output reg [3:0] dout
);

always @(*) begin
    case ({line, column})
        6'b000000: dout = 'd12;
        6'b000001: dout = 'd1;
        6'b000010: dout = 'd10;
        6'b000011: dout = 'd15;
        6'b000100: dout = 'd9;
        6'b000101: dout = 'd2;
        6'b000110: dout = 'd6;
        6'b000111: dout = 'd8;
        6'b001000: dout = 'd0;
        6'b001001: dout = 'd13;
        6'b001010: dout = 'd3;
        6'b001011: dout = 'd4;
        6'b001100: dout = 'd14;
        6'b001101: dout = 'd7;
        6'b001110: dout = 'd5;
        6'b001111: dout = 'd11;
        6'b010000: dout = 'd10;
        6'b010001: dout = 'd15;
        6'b010010: dout = 'd4;
        6'b010011: dout = 'd2;
        6'b010100: dout = 'd7;
        6'b010101: dout = 'd12;
        6'b010110: dout = 'd9;
        6'b010111: dout = 'd5;
        6'b011000: dout = 'd6;
        6'b011001: dout = 'd1;
        6'b011010: dout = 'd13;
        6'b011011: dout = 'd14;
        6'b011100: dout = 'd0;
        6'b011101: dout = 'd11;
        6'b011110: dout = 'd3;
        6'b011111: dout = 'd8;
        6'b100000: dout = 'd9;
        6'b100001: dout = 'd14;
        6'b100010: dout = 'd15;
        6'b100011: dout = 'd5;
        6'b100100: dout = 'd2;
        6'b100101: dout = 'd8;
        6'b100110: dout = 'd12;
        6'b100111: dout = 'd3;
        6'b101000: dout = 'd7;
        6'b101001: dout = 'd0;
        6'b101010: dout = 'd4;
        6'b101011: dout = 'd10;
        6'b101100: dout = 'd1;
        6'b101101: dout = 'd13;
        6'b101110: dout = 'd11;
        6'b101111: dout = 'd6;
        6'b110000: dout = 'd4;
        6'b110001: dout = 'd3;
        6'b110010: dout = 'd2;
        6'b110011: dout = 'd12;
        6'b110100: dout = 'd9;
        6'b110101: dout = 'd5;
        6'b110110: dout = 'd15;
        6'b110111: dout = 'd10;
        6'b111000: dout = 'd11;
        6'b111001: dout = 'd14;
        6'b111010: dout = 'd1;
        6'b111011: dout = 'd7;
        6'b111100: dout = 'd6;
        6'b111101: dout = 'd0;
        6'b111110: dout = 'd8;
        6'b111111: dout = 'd13;
    endcase
end

endmodule

module sbox7_lut(
    input      [1:0] line,
    input      [3:0] column,
    output reg [3:0] dout
);

always @(*) begin
    case ({line, column})
        6'b000000: dout = 'd4;
        6'b000001: dout = 'd11;
        6'b000010: dout = 'd2;
        6'b000011: dout = 'd14;
        6'b000100: dout = 'd15;
        6'b000101: dout = 'd0;
        6'b000110: dout = 'd8;
        6'b000111: dout = 'd13;
        6'b001000: dout = 'd3;
        6'b001001: dout = 'd12;
        6'b001010: dout = 'd9;
        6'b001011: dout = 'd7;
        6'b001100: dout = 'd5;
        6'b001101: dout = 'd10;
        6'b001110: dout = 'd6;
        6'b001111: dout = 'd1;
        6'b010000: dout = 'd13;
        6'b010001: dout = 'd0;
        6'b010010: dout = 'd11;
        6'b010011: dout = 'd7;
        6'b010100: dout = 'd4;
        6'b010101: dout = 'd9;
        6'b010110: dout = 'd1;
        6'b010111: dout = 'd10;
        6'b011000: dout = 'd14;
        6'b011001: dout = 'd3;
        6'b011010: dout = 'd5;
        6'b011011: dout = 'd12;
        6'b011100: dout = 'd2;
        6'b011101: dout = 'd15;
        6'b011110: dout = 'd8;
        6'b011111: dout = 'd6;
        6'b100000: dout = 'd1;
        6'b100001: dout = 'd4;
        6'b100010: dout = 'd11;
        6'b100011: dout = 'd13;
        6'b100100: dout = 'd12;
        6'b100101: dout = 'd3;
        6'b100110: dout = 'd7;
        6'b100111: dout = 'd14;
        6'b101000: dout = 'd10;
        6'b101001: dout = 'd15;
        6'b101010: dout = 'd6;
        6'b101011: dout = 'd8;
        6'b101100: dout = 'd0;
        6'b101101: dout = 'd5;
        6'b101110: dout = 'd9;
        6'b101111: dout = 'd2;
        6'b110000: dout = 'd6;
        6'b110001: dout = 'd11;
        6'b110010: dout = 'd13;
        6'b110011: dout = 'd8;
        6'b110100: dout = 'd1;
        6'b110101: dout = 'd4;
        6'b110110: dout = 'd10;
        6'b110111: dout = 'd7;
        6'b111000: dout = 'd9;
        6'b111001: dout = 'd5;
        6'b111010: dout = 'd0;
        6'b111011: dout = 'd15;
        6'b111100: dout = 'd14;
        6'b111101: dout = 'd2;
        6'b111110: dout = 'd3;
        6'b111111: dout = 'd12;
    endcase
end

endmodule

module sbox8_lut(
    input      [1:0] line,
    input      [3:0] column,
    output reg [3:0] dout
);

always @(*) begin
    case ({line, column})
        6'b000000: dout = 'd13;
        6'b000001: dout = 'd2;
        6'b000010: dout = 'd8;
        6'b000011: dout = 'd4;
        6'b000100: dout = 'd6;
        6'b000101: dout = 'd15;
        6'b000110: dout = 'd11;
        6'b000111: dout = 'd1;
        6'b001000: dout = 'd10;
        6'b001001: dout = 'd9;
        6'b001010: dout = 'd3;
        6'b001011: dout = 'd14;
        6'b001100: dout = 'd5;
        6'b001101: dout = 'd0;
        6'b001110: dout = 'd12;
        6'b001111: dout = 'd7;
        6'b010000: dout = 'd1;
        6'b010001: dout = 'd15;
        6'b010010: dout = 'd13;
        6'b010011: dout = 'd8;
        6'b010100: dout = 'd10;
        6'b010101: dout = 'd3;
        6'b010110: dout = 'd7;
        6'b010111: dout = 'd4;
        6'b011000: dout = 'd12;
        6'b011001: dout = 'd5;
        6'b011010: dout = 'd6;
        6'b011011: dout = 'd11;
        6'b011100: dout = 'd0;
        6'b011101: dout = 'd14;
        6'b011110: dout = 'd9;
        6'b011111: dout = 'd2;
        6'b100000: dout = 'd7;
        6'b100001: dout = 'd11;
        6'b100010: dout = 'd4;
        6'b100011: dout = 'd1;
        6'b100100: dout = 'd9;
        6'b100101: dout = 'd12;
        6'b100110: dout = 'd14;
        6'b100111: dout = 'd2;
        6'b101000: dout = 'd0;
        6'b101001: dout = 'd6;
        6'b101010: dout = 'd10;
        6'b101011: dout = 'd13;
        6'b101100: dout = 'd15;
        6'b101101: dout = 'd3;
        6'b101110: dout = 'd5;
        6'b101111: dout = 'd8;
        6'b110000: dout = 'd2;
        6'b110001: dout = 'd1;
        6'b110010: dout = 'd14;
        6'b110011: dout = 'd7;
        6'b110100: dout = 'd4;
        6'b110101: dout = 'd10;
        6'b110110: dout = 'd8;
        6'b110111: dout = 'd13;
        6'b111000: dout = 'd15;
        6'b111001: dout = 'd12;
        6'b111010: dout = 'd9;
        6'b111011: dout = 'd0;
        6'b111100: dout = 'd3;
        6'b111101: dout = 'd5;
        6'b111110: dout = 'd6;
        6'b111111: dout = 'd11;
    endcase
end

endmodule

module round_p(
    input  [31:0] dat_in,
    output [31:0] dat_out
    );

assign dat_out = {dat_in[16], dat_in[25], dat_in[12], dat_in[11], dat_in[3], dat_in[20], dat_in[4], dat_in[15], dat_in[31], dat_in[17], dat_in[9], dat_in[6], dat_in[27], dat_in[14], dat_in[1], dat_in[22], dat_in[30], dat_in[24], dat_in[8], dat_in[18], dat_in[0], dat_in[5], dat_in[29], dat_in[23], dat_in[13], dat_in[19], dat_in[2], dat_in[26], dat_in[10], dat_in[21], dat_in[28], dat_in[7]};

endmodule

module mux(
    input             clk,
    input             rst_n,
    input      [31:0] f_out,
    input      [31:0] L_init,
    input      [31:0] R_init,
    input      [4:0]  cnt,
    output reg [31:0] R_dat,
    output reg [31:0] L_dat,
    output            lst_valid
    );


//加上R0 L0总共17个参数
always @(posedge clk or negedge rst_n) begin
    if (rst_n == 1'b0) begin
        R_dat <= 'd0;
        L_dat <= 'd0;
    end
    else begin
        if (cnt == 'd0) begin
            R_dat <= R_init;
            L_dat  <= L_init;
        end
        else if (cnt > 'd0 && cnt < 'd17) begin
            R_dat <= f_out ^ L_dat;
            L_dat <= R_dat;
        end
        else begin
            R_dat <= R_dat;
            L_dat <= L_dat;
        end
    end
end

assign lst_valid = (cnt == 'd17) ? 1'b1 : 1'b0;

// always @(posedge clk) begin
//     lst_valid <= lst_valid_d;
// end

endmodule

module Permutation_inverse(
    input  [63:0] dat_in,
    output [63:0] dat_out
    );

assign dat_out = {dat_in[24], dat_in[56], dat_in[16], dat_in[48], dat_in[8], dat_in[40], dat_in[0], dat_in[32], dat_in[25], dat_in[57], dat_in[17], dat_in[49], dat_in[9], dat_in[41], dat_in[1], dat_in[33], dat_in[26], dat_in[58], dat_in[18], dat_in[50], dat_in[10], dat_in[42], dat_in[2], dat_in[34], dat_in[27], dat_in[59], dat_in[19], dat_in[51], dat_in[11], dat_in[43], dat_in[3], dat_in[35], dat_in[28], dat_in[60], dat_in[20], dat_in[52], dat_in[12], dat_in[44], dat_in[4], dat_in[36], dat_in[29], dat_in[61], dat_in[21], dat_in[53], dat_in[13], dat_in[45], dat_in[5], dat_in[37], dat_in[30], dat_in[62], dat_in[22], dat_in[54], dat_in[14], dat_in[46], dat_in[6], dat_in[38], dat_in[31], dat_in[63], dat_in[23], dat_in[55], dat_in[15], dat_in[47], dat_in[7], dat_in[39] };

endmodule

module keygen(
    input  [4:0]  cnt,
    input  [63:0] key,
    output [47:0] round_key
    );

wire [55:0] key_dat;
reg [55:0] key_shift;
//除去校验位 pc1
assign key_dat = {key[7], key[15], key[23], key[31], key[39], key[47], key[55], key[63], key[6], key[14], key[22], key[30], key[38], key[46], key[54], key[62], key[5], key[13], key[21], key[29], key[37], key[45], key[53], key[61], key[4], key[12], key[20], key[28], key[1], key[9], key[17], key[25], key[33], key[41], key[49], key[57], key[2], key[10], key[18], key[26], key[34], key[42], key[50], key[58], key[3], key[11], key[19], key[27], key[35], key[43], key[51], key[59], key[36], key[44], key[52], key[60]};

always @(*) begin
    case (cnt)
        'd1: key_shift = {key_dat[54:28], key_dat[55], key_dat[26:0], key_dat[27]};
        'd2: key_shift = {key_dat[53:28], key_dat[55:54], key_dat[25:0], key_dat[27:26]};
        'd3: key_shift = {key_dat[51:28], key_dat[55:52], key_dat[23:0], key_dat[27:24]};
        'd4: key_shift = {key_dat[49:28], key_dat[55:50], key_dat[21:0], key_dat[27:22]};
        'd5: key_shift = {key_dat[47:28], key_dat[55:48], key_dat[19:0], key_dat[27:20]};
        'd6: key_shift = {key_dat[45:28], key_dat[55:46], key_dat[17:0], key_dat[27:18]};
        'd7: key_shift = {key_dat[43:28], key_dat[55:44], key_dat[15:0], key_dat[27:16]};
        'd8: key_shift = {key_dat[41:28], key_dat[55:42], key_dat[13:0], key_dat[27:14]};
        'd9: key_shift = {key_dat[40:28], key_dat[55:41], key_dat[12:0], key_dat[27:13]};
        'd10: key_shift = {key_dat[38:28], key_dat[55:39], key_dat[10:0], key_dat[27:11]};
        'd11: key_shift = {key_dat[36:28], key_dat[55:37], key_dat[8:0], key_dat[27:9]};
        'd12: key_shift = {key_dat[34:28], key_dat[55:35], key_dat[6:0], key_dat[27:7]};
        'd13: key_shift = {key_dat[32:28], key_dat[55:33], key_dat[4:0], key_dat[27:5]};
        'd14: key_shift = {key_dat[30:28], key_dat[55:31], key_dat[2:0], key_dat[27:3]};
        'd15: key_shift = {key_dat[28], key_dat[55:29], key_dat[0], key_dat[27:1]};
        'd16: key_shift = key_dat;
        default: key_shift = 'd0;
    endcase
end

//置换选择2 pc2 todo
assign round_key = {key_shift[42], key_shift[39], key_shift[45], key_shift[32], key_shift[55], key_shift[51], key_shift[53], key_shift[28], key_shift[41], key_shift[50], key_shift[35], key_shift[46], key_shift[33], key_shift[37], key_shift[44], key_shift[52], key_shift[30], key_shift[48], key_shift[40], key_shift[49], key_shift[29], key_shift[36], key_shift[43], key_shift[54], key_shift[15], key_shift[4], key_shift[25], key_shift[19], key_shift[9], key_shift[1], key_shift[26], key_shift[16], key_shift[5], key_shift[11], key_shift[23], key_shift[8], key_shift[12], key_shift[7], key_shift[17], key_shift[0], key_shift[22], key_shift[3], key_shift[10], key_shift[14], key_shift[6], key_shift[20], key_shift[27], key_shift[24]};


endmodule


`default_nettype wire
