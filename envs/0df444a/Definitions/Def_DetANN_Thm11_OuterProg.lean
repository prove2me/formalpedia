-- Prove2me | Definitions.Def_DetANN_Thm11_OuterProg
-- name    : DetANN_Thm11_OuterProg
-- status  : Definition
-- author  : @milia
-- created : 2026-11-23T21:56:31.284616+00:00
-- url     : https://prove2.me/theorems/91aff925-5e74-4384-8012-ddff3085077a
-- title:
--   The outer preprocessing and query programs of the composed data structure of Theorem 1.1 (§7.4)
-- statement:
--   For an inner pair of programs and natural parameters $n_3,c_0,C_b,K,C_p,X_3$, the programs
--   $$\mathrm{outerPre}(\mathrm{Pre}_3,n_3,c_0,C_b,K,C_p,X_3),\qquad \mathrm{outerQry}(\mathrm{Qry}_3,n_3,c_0,C_b,K,C_p,X_3)$$
--   are the preprocessing and query programs of the composed data structure of §7.4 on the PNormReg machine.
--
--   **Structure.** Each program is a main part followed by a subroutine.
--   - The main part has 1612 instructions for preprocessing and 255 for queries.
--   - The subroutine zeroes the real and pointer registers $300,\dots,300+n_3-1$ and then runs a relocated copy (`PNormRegLib.reloc`) of the inner program, whose halt returns to the main part.
--   - The main parts contain relocated copies of the construction program $\mathrm{pre}(c_0,0)$ and the evaluation program $\mathrm{ev}(0)$ of Theorem 3.2 (definitions `DetANN_Supplement_PreProg` and `DetANN_Supplement_EvProg`).
--
--   **Preprocessing** of $P:[n]\to\mathbb R^d$ with input parameter $\varepsilon$:
--   1. If $n\le1$, halt.
--   2. Compute $d'=2^k\ge d$ (the least such power of two), $\tau=\varepsilon^2/10^6$, $\delta=\varepsilon/100$, and $\ell=\mathrm{walkLen}\,\varepsilon$.
--   3. Build integer tables: the row bases $1+id$, the neighbour lists of the Lemma 7.1 graph on $[d']$, and the endpoints $\mathrm{walkEnd}(v,w)$ of all $16^\ell$ walks from every vertex $v$.
--   4. In a window $W_T$ of radius $R_T$, centred beyond the input and the tables, write the input layout of the zero-padded points with parameter $\tau$, and run $\mathrm{pre}$ there. This computes the number of repetitions $L$ and the greedy signs of the balanced blocks.
--   5. With $m=16^\ell L$, lay out windows $W_v$ ($v<d'$) of radius $R_3$. For each point $P_i$, run $\mathrm{ev}$ in $W_T$ on the padded point and copy $A_{\mathrm{walkEnd}(v,w)}(\bar P_i)$ into $W_v$. Then $W_v$ holds the input layout of the superblock projections $\mathcal A_vP\subset\mathbb R^m$ with parameter $\delta$.
--   6. Run the inner preprocessing in every $W_v$, and store the parameters in integer cells $2,\dots,14$.
--
--   **Query** $q\in\mathbb R^d$:
--   1. If $n\le1$, answer $0$.
--   2. Write the padded $q$ into the query cells of $W_T$ and run $\mathrm{ev}$.
--   3. For every $v$, write $\mathcal A_v\bar q$ into the query cells of $W_v$ and run the inner query, which returns a candidate $x_v$.
--   4. Answer the first candidate with the smallest $\|q-P_{x_v}\|^2$.
--
--   These are the programs of the machine part of Theorem 1.1 (theorem `outer_composition`). The parameters $C_b$, $K$, $C_p$ and $X_3$ stand for the constants of the inner structure (an integer bound $C\le C_b$, the exponent, the constant $C'$, and the literal bound), and $c_0$ is the rational constant in the choice of $L$.
--
--   **Formalization note.** The program text was generated mechanically. The register maps are listed in the module header.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' for the machine part of DetANN.theorem_1_1 (Feng, Indyk, STOC 2027 submission, Theorem 1.1, p.2; the construction of §7.4, p.19). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg

/-!
# Theorem 1.1: the outer programs of the composed data structure (§7.4)

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §7.4, p.19.

`outerPre Pre₃ n3 c0 Cb K Cp X3` and `outerQry Qry₃ n3 c0 Cb K Cp X3` are the preprocessing and
query programs of the composed structure. Each is a main part followed by a subroutine: the
registers `300 … 300 + n3 − 1` (real and pointer) are zeroed, and then the inner program (`Pre₃`
or `Qry₃`, a Lemma 3.3 structure) runs as a relocated copy (`PNormRegLib.reloc`) whose `halt`
returns to a fixed label of the main part. The main parts contain relocated copies of milestone 21's
`pre (c0 : ℚ) 0` (registers from 100) and `ev 0` (registers from 200) at fixed positions.

**Preprocessing**, from the input layout of `P : Fin n → ℝ^d` with parameter `ε`:
1. If `n ≤ 1`, halt.
2. Compute `d' = 2^kk` (the least power of two `≥ d`), `τ = ε²/10⁶`, `δ = ε/100`, and `ℓ`, the least
   integer with `θ₀^ℓ ≤ ε/200` (`θ₀ = 5√2/8`, so `ℓ = walkLen ε`).
3. Build integer tables from cell 64:
   - row bases `1 + i·d`;
   - the Lemma 7.1 neighbour lists of `Fin d'`;
   - the walk endpoints `walkEnd` of all `16^ℓ` walks from every vertex (the least significant base-16
     digit is the first step).
4. Window `W_T`: radius `R_T = Y_T·2^T̄`, with `T̄ ≥ B_T` (a bound on the time of `pre` plus `n + 2`
   runs of `ev`), centred beyond the input and the tables. It receives the input layout of the
   zero-padded points with parameter `τ`. Then `pre` runs in it.
5. With `L` (written by `pre` at virtual integer cell 0) and `m = 16^ℓ·L`, windows `W_v` (`v < d'`)
   of radius `R₃ = Y₃·2^T̄₃` follow, where `T̄₃` bounds Lemma 3.3's preprocessing plus query time for
   `n` points in `ℝ^m`. Each gets the header `δ`, `n`, `m`.
6. For each point `i`: `ev` runs in `W_T` on the padded `P_i`, and `A_{walkEnd(v,w)}(pad P_i)` is
   copied to `W_v` at virtual cells `1 + i·m + w·L + ℓ`. So `W_v` holds exactly the input layout of
   the superblock projections `𝒜_v P` with parameter `δ`.
7. For each `v`, the inner preprocessing runs in `W_v`. Finally the parameters are stored in integer
   cells `2 … 14`.

**Query** `q` (real cells `−1 − c`):
1. If `n ≤ 1`, answer `0`.
2. Write `q` into `W_T`'s query cells and run `ev`.
3. For each `v`: write the superblock projection of the padded `q` into `W_v`'s query cells, run the
   inner query, and read its answer `x_v` (pointer `300`). Keep the first `x_v` with the strictly
   smallest `‖q − P x_v‖²`.

Pointers: `0` zero, `1` one, `2` two, `3` n, `4` d, `5` dp, `6` kk, `7` ell, `8` W16, `9` i, `10` h, `11` m2, `12` u, `13` s, `14` top, `15` rbB, `16` a, `17` XB, `18` YB, `19` x, `20` w, `21` nbB, `22` nbAB, `23` v, `24` nbp, `25` y, `26` b, `27` x2, `28` y2, `29` x21, `30` y21, `31` nx, `32` ny, `33` t1, `34` t2, `35` digB, `36` wB, `37` wp, `38` c, `39` cur, `40` wLB, `41` E, `42` YT, `43` e, `44` Tb, `45` RT, `46` bT, `47` rp, `48` src, `49` dst, `50` tmpT, `51` L, `52` m, `53` Y3, `54` K, `55` j, `56` R3, `57` b0, `58` step, `59` bv, `60` ri, `61` l, `62` tmpV. Reals: `0` eps, `1` zr, `2` tau, `3` c, `4` del, `5` thr, `6` t, `7` th, `8` u, `9` nr, `10` dr, `11` kr, `12` x, `13` p, `14` B, `15` y, `16` z, `17` mr, `18` s, `19` g, `20` hh, `21` sh.
-/

namespace DetANN.Thm11

open PNormReg PNormRegLib DetANN.Supplement.Thm32

noncomputable section

/-- Zero the real registers `roff … roff + nR − 1` and the pointer registers `qoff … qoff + nQ − 1`. -/
def zeroRegs (roff qoff nR nQ : ℕ) : Program :=
  (List.range nR).map (fun i => Instr.core (.const (roff + i) (0 : ℝ))) ++
    (List.range nQ).map (fun i => Instr.core (.pset (qoff + i) 0))

/-- `opre`, instructions 0–59. -/
def opre0 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pset 1 (1)),  -- 0
    .core (.pset 2 (2)),  -- 1
    .integerLoad 3 0,  -- 2
    .integerLoad 4 1,  -- 3
    .core (.load 0 0),  -- 4
    .core (.const 1 (0 : ℝ)),  -- 5
    .core (.pjle 3 1 1611),  -- 6
    .core (.pset 5 (1)),  -- 7
    .core (.pset 6 (0)),  -- 8
    .core (.pjle 4 5 13),  -- 9 PAD
    .pointerAdd 5 5 5,  -- 10
    .core (.pinc 6),  -- 11
    .core (.pjle 0 0 9),  -- 12
    .core (.mul 2 0 0),  -- 13 PADD
    .core (.const 3 (1 / 1000000 : ℝ)),  -- 14
    .core (.mul 2 2 3),  -- 15
    .core (.const 3 (1 / 100 : ℝ)),  -- 16
    .core (.mul 4 0 3),  -- 17
    .core (.const 3 (1 / 200 : ℝ)),  -- 18
    .core (.mul 5 0 3),  -- 19
    .core (.const 6 (1 : ℝ)),  -- 20
    .core (.const 3 (2 : ℝ)),  -- 21
    .sqrt 7 3,  -- 22
    .core (.const 3 (5 : ℝ)),  -- 23
    .core (.mul 7 7 3),  -- 24
    .core (.const 3 (1 / 8 : ℝ)),  -- 25
    .core (.mul 7 7 3),  -- 26
    .core (.pset 7 (0)),  -- 27
    .core (.sub 8 6 5),  -- 28 WL
    .core (.jle 8 33),  -- 29
    .core (.mul 6 6 7),  -- 30
    .core (.pinc 7),  -- 31
    .core (.pjle 0 0 28),  -- 32
    .core (.pset 8 (1)),  -- 33 WLD
    .core (.pset 9 (0)),  -- 34
    .core (.pjle 7 9 42),  -- 35 W16
    .pointerAdd 8 8 8,  -- 36
    .pointerAdd 8 8 8,  -- 37
    .pointerAdd 8 8 8,  -- 38
    .pointerAdd 8 8 8,  -- 39
    .core (.pinc 9),  -- 40
    .core (.pjle 0 0 35),  -- 41
    .core (.pset 10 (0)),  -- 42 W16D
    .core (.pset 11 (1)),  -- 43
    .pointerAdd 12 10 10,  -- 44 HH
    .core (.pinc 12),  -- 45
    .core (.pinc 12),  -- 46
    .core (.pjle 12 6 49),  -- 47
    .core (.pjle 0 0 52),  -- 48
    .core (.pinc 10),  -- 49 HHI
    .pointerAdd 11 11 11,  -- 50
    .core (.pjle 0 0 44),  -- 51
    .pointerAdd 12 10 10,  -- 52 HHD
    .pointerSub 13 6 12,  -- 53
    .core (.pinc 13),  -- 54
    .core (.pset 14 (64)),  -- 55
    .core (.pcopy 15 14),  -- 56
    .pointerAdd 14 14 3,  -- 57
    .core (.pset 16 (1)),  -- 58
    .core (.pset 9 (0)) ]  -- 59

/-- `opre`, instructions 60–119. -/
def opre1 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pjle 3 9 66),  -- 60 RB
    .pointerAdd 12 15 9,  -- 61
    .integerStore 12 16,  -- 62
    .pointerAdd 16 16 4,  -- 63
    .core (.pinc 9),  -- 64
    .core (.pjle 0 0 60),  -- 65
    .core (.pcopy 17 14),  -- 66 RBD
    .pointerAdd 14 14 11,  -- 67
    .core (.pcopy 18 14),  -- 68
    .pointerAdd 14 14 11,  -- 69
    .core (.pset 12 (0)),  -- 70
    .core (.pset 19 (0)),  -- 71
    .core (.pset 16 (0)),  -- 72
    .core (.pjle 11 19 86),  -- 73 XT
    .pointerAdd 20 17 19,  -- 74
    .integerStore 20 16,  -- 75
    .pointerAdd 20 18 19,  -- 76
    .integerStore 20 12,  -- 77
    .core (.pset 9 (0)),  -- 78
    .core (.pjle 11 9 83),  -- 79 XS
    .pointerAdd 16 16 13,  -- 80
    .core (.pinc 9),  -- 81
    .core (.pjle 0 0 79),  -- 82
    .pointerAdd 12 12 13,  -- 83 XSD
    .core (.pinc 19),  -- 84
    .core (.pjle 0 0 73),  -- 85
    .core (.pcopy 21 14),  -- 86 XTD
    .core (.pset 20 (16)),  -- 87
    .core (.pset 9 (0)),  -- 88
    .core (.pjle 5 9 93),  -- 89 NBS
    .pointerAdd 14 14 20,  -- 90
    .core (.pinc 9),  -- 91
    .core (.pjle 0 0 89),  -- 92
    .core (.pcopy 22 14),  -- 93 NBSD
    .pointerAdd 14 14 5,  -- 94
    .core (.pset 23 (0)),  -- 95
    .core (.pset 19 (0)),  -- 96
    .core (.pcopy 24 21),  -- 97
    .core (.pjle 11 19 360),  -- 98 VX
    .core (.pset 25 (0)),  -- 99
    .core (.pjle 11 25 358),  -- 100 VY
    .core (.pset 26 (0)),  -- 101
    .core (.pjle 13 26 356),  -- 102 VB
    .pointerAdd 20 22 23,  -- 103
    .integerStore 20 24,  -- 104
    .pointerAdd 27 19 19,  -- 105
    .pointerAdd 28 25 25,  -- 106
    .core (.pcopy 29 27),  -- 107
    .core (.pinc 29),  -- 108
    .core (.pcopy 30 28),  -- 109
    .core (.pinc 30),  -- 110
    .pointerAdd 31 19 28,  -- 111
    .core (.pcopy 32 25),  -- 112
    .core (.pjle 11 31 115),  -- 113 N113A
    .core (.pjle 0 0 117),  -- 114
    .pointerSub 31 31 11,  -- 115 N113S
    .core (.pjle 0 0 113),  -- 116
    .core (.pjle 0 31 120),  -- 117 N113B
    .pointerAdd 31 31 11,  -- 118
    .core (.pjle 0 0 117) ]  -- 119

/-- `opre`, instructions 120–179. -/
def opre2 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pjle 11 32 122),  -- 120 N113D N120A
    .core (.pjle 0 0 124),  -- 121
    .pointerSub 32 32 11,  -- 122 N120S
    .core (.pjle 0 0 120),  -- 123
    .core (.pjle 0 32 127),  -- 124 N120B
    .pointerAdd 32 32 11,  -- 125
    .core (.pjle 0 0 124),  -- 126
    .pointerAdd 20 17 31,  -- 127 N120D
    .integerLoad 33 20,  -- 128
    .pointerAdd 20 18 32,  -- 129
    .integerLoad 34 20,  -- 130
    .pointerAdd 33 33 34,  -- 131
    .core (.pset 20 (0)),  -- 132
    .pointerAdd 20 20 24,  -- 133
    .integerStore 20 33,  -- 134
    .core (.pcopy 34 33),  -- 135
    .core (.pjle 13 1 138),  -- 136
    .core (.pinc 34),  -- 137
    .core (.pset 20 (8)),  -- 138 NB0
    .pointerAdd 20 20 24,  -- 139
    .integerStore 20 34,  -- 140
    .pointerSub 31 19 28,  -- 141
    .core (.pcopy 32 25),  -- 142
    .core (.pjle 11 31 145),  -- 143 N143A
    .core (.pjle 0 0 147),  -- 144
    .pointerSub 31 31 11,  -- 145 N143S
    .core (.pjle 0 0 143),  -- 146
    .core (.pjle 0 31 150),  -- 147 N143B
    .pointerAdd 31 31 11,  -- 148
    .core (.pjle 0 0 147),  -- 149
    .core (.pjle 11 32 152),  -- 150 N143D N150A
    .core (.pjle 0 0 154),  -- 151
    .pointerSub 32 32 11,  -- 152 N150S
    .core (.pjle 0 0 150),  -- 153
    .core (.pjle 0 32 157),  -- 154 N150B
    .pointerAdd 32 32 11,  -- 155
    .core (.pjle 0 0 154),  -- 156
    .pointerAdd 20 17 31,  -- 157 N150D
    .integerLoad 33 20,  -- 158
    .pointerAdd 20 18 32,  -- 159
    .integerLoad 34 20,  -- 160
    .pointerAdd 33 33 34,  -- 161
    .core (.pset 20 (1)),  -- 162
    .pointerAdd 20 20 24,  -- 163
    .integerStore 20 33,  -- 164
    .core (.pcopy 34 33),  -- 165
    .core (.pjle 13 1 168),  -- 166
    .core (.pinc 34),  -- 167
    .core (.pset 20 (9)),  -- 168 NB1
    .pointerAdd 20 20 24,  -- 169
    .integerStore 20 34,  -- 170
    .pointerAdd 31 19 30,  -- 171
    .core (.pcopy 32 25),  -- 172
    .core (.pjle 11 31 175),  -- 173 N173A
    .core (.pjle 0 0 177),  -- 174
    .pointerSub 31 31 11,  -- 175 N173S
    .core (.pjle 0 0 173),  -- 176
    .core (.pjle 0 31 180),  -- 177 N173B
    .pointerAdd 31 31 11,  -- 178
    .core (.pjle 0 0 177) ]  -- 179

/-- `opre`, instructions 180–239. -/
def opre3 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pjle 11 32 182),  -- 180 N173D N180A
    .core (.pjle 0 0 184),  -- 181
    .pointerSub 32 32 11,  -- 182 N180S
    .core (.pjle 0 0 180),  -- 183
    .core (.pjle 0 32 187),  -- 184 N180B
    .pointerAdd 32 32 11,  -- 185
    .core (.pjle 0 0 184),  -- 186
    .pointerAdd 20 17 31,  -- 187 N180D
    .integerLoad 33 20,  -- 188
    .pointerAdd 20 18 32,  -- 189
    .integerLoad 34 20,  -- 190
    .pointerAdd 33 33 34,  -- 191
    .core (.pset 20 (2)),  -- 192
    .pointerAdd 20 20 24,  -- 193
    .integerStore 20 33,  -- 194
    .core (.pcopy 34 33),  -- 195
    .core (.pjle 13 1 198),  -- 196
    .core (.pinc 34),  -- 197
    .core (.pset 20 (10)),  -- 198 NB2
    .pointerAdd 20 20 24,  -- 199
    .integerStore 20 34,  -- 200
    .pointerSub 31 19 30,  -- 201
    .core (.pcopy 32 25),  -- 202
    .core (.pjle 11 31 205),  -- 203 N203A
    .core (.pjle 0 0 207),  -- 204
    .pointerSub 31 31 11,  -- 205 N203S
    .core (.pjle 0 0 203),  -- 206
    .core (.pjle 0 31 210),  -- 207 N203B
    .pointerAdd 31 31 11,  -- 208
    .core (.pjle 0 0 207),  -- 209
    .core (.pjle 11 32 212),  -- 210 N203D N210A
    .core (.pjle 0 0 214),  -- 211
    .pointerSub 32 32 11,  -- 212 N210S
    .core (.pjle 0 0 210),  -- 213
    .core (.pjle 0 32 217),  -- 214 N210B
    .pointerAdd 32 32 11,  -- 215
    .core (.pjle 0 0 214),  -- 216
    .pointerAdd 20 17 31,  -- 217 N210D
    .integerLoad 33 20,  -- 218
    .pointerAdd 20 18 32,  -- 219
    .integerLoad 34 20,  -- 220
    .pointerAdd 33 33 34,  -- 221
    .core (.pset 20 (3)),  -- 222
    .pointerAdd 20 20 24,  -- 223
    .integerStore 20 33,  -- 224
    .core (.pcopy 34 33),  -- 225
    .core (.pjle 13 1 228),  -- 226
    .core (.pinc 34),  -- 227
    .core (.pset 20 (11)),  -- 228 NB3
    .pointerAdd 20 20 24,  -- 229
    .integerStore 20 34,  -- 230
    .core (.pcopy 31 19),  -- 231
    .pointerAdd 32 25 27,  -- 232
    .core (.pjle 11 31 235),  -- 233 N233A
    .core (.pjle 0 0 237),  -- 234
    .pointerSub 31 31 11,  -- 235 N233S
    .core (.pjle 0 0 233),  -- 236
    .core (.pjle 0 31 240),  -- 237 N233B
    .pointerAdd 31 31 11,  -- 238
    .core (.pjle 0 0 237) ]  -- 239

/-- `opre`, instructions 240–299. -/
def opre4 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pjle 11 32 242),  -- 240 N233D N240A
    .core (.pjle 0 0 244),  -- 241
    .pointerSub 32 32 11,  -- 242 N240S
    .core (.pjle 0 0 240),  -- 243
    .core (.pjle 0 32 247),  -- 244 N240B
    .pointerAdd 32 32 11,  -- 245
    .core (.pjle 0 0 244),  -- 246
    .pointerAdd 20 17 31,  -- 247 N240D
    .integerLoad 33 20,  -- 248
    .pointerAdd 20 18 32,  -- 249
    .integerLoad 34 20,  -- 250
    .pointerAdd 33 33 34,  -- 251
    .core (.pset 20 (4)),  -- 252
    .pointerAdd 20 20 24,  -- 253
    .integerStore 20 33,  -- 254
    .core (.pcopy 34 33),  -- 255
    .core (.pjle 13 1 258),  -- 256
    .core (.pinc 34),  -- 257
    .core (.pset 20 (12)),  -- 258 NB4
    .pointerAdd 20 20 24,  -- 259
    .integerStore 20 34,  -- 260
    .core (.pcopy 31 19),  -- 261
    .pointerSub 32 25 27,  -- 262
    .core (.pjle 11 31 265),  -- 263 N263A
    .core (.pjle 0 0 267),  -- 264
    .pointerSub 31 31 11,  -- 265 N263S
    .core (.pjle 0 0 263),  -- 266
    .core (.pjle 0 31 270),  -- 267 N263B
    .pointerAdd 31 31 11,  -- 268
    .core (.pjle 0 0 267),  -- 269
    .core (.pjle 11 32 272),  -- 270 N263D N270A
    .core (.pjle 0 0 274),  -- 271
    .pointerSub 32 32 11,  -- 272 N270S
    .core (.pjle 0 0 270),  -- 273
    .core (.pjle 0 32 277),  -- 274 N270B
    .pointerAdd 32 32 11,  -- 275
    .core (.pjle 0 0 274),  -- 276
    .pointerAdd 20 17 31,  -- 277 N270D
    .integerLoad 33 20,  -- 278
    .pointerAdd 20 18 32,  -- 279
    .integerLoad 34 20,  -- 280
    .pointerAdd 33 33 34,  -- 281
    .core (.pset 20 (5)),  -- 282
    .pointerAdd 20 20 24,  -- 283
    .integerStore 20 33,  -- 284
    .core (.pcopy 34 33),  -- 285
    .core (.pjle 13 1 288),  -- 286
    .core (.pinc 34),  -- 287
    .core (.pset 20 (13)),  -- 288 NB5
    .pointerAdd 20 20 24,  -- 289
    .integerStore 20 34,  -- 290
    .core (.pcopy 31 19),  -- 291
    .pointerAdd 32 25 29,  -- 292
    .core (.pjle 11 31 295),  -- 293 N293A
    .core (.pjle 0 0 297),  -- 294
    .pointerSub 31 31 11,  -- 295 N293S
    .core (.pjle 0 0 293),  -- 296
    .core (.pjle 0 31 300),  -- 297 N293B
    .pointerAdd 31 31 11,  -- 298
    .core (.pjle 0 0 297) ]  -- 299

/-- `opre`, instructions 300–359. -/
def opre5 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pjle 11 32 302),  -- 300 N293D N300A
    .core (.pjle 0 0 304),  -- 301
    .pointerSub 32 32 11,  -- 302 N300S
    .core (.pjle 0 0 300),  -- 303
    .core (.pjle 0 32 307),  -- 304 N300B
    .pointerAdd 32 32 11,  -- 305
    .core (.pjle 0 0 304),  -- 306
    .pointerAdd 20 17 31,  -- 307 N300D
    .integerLoad 33 20,  -- 308
    .pointerAdd 20 18 32,  -- 309
    .integerLoad 34 20,  -- 310
    .pointerAdd 33 33 34,  -- 311
    .core (.pset 20 (6)),  -- 312
    .pointerAdd 20 20 24,  -- 313
    .integerStore 20 33,  -- 314
    .core (.pcopy 34 33),  -- 315
    .core (.pjle 13 1 318),  -- 316
    .core (.pinc 34),  -- 317
    .core (.pset 20 (14)),  -- 318 NB6
    .pointerAdd 20 20 24,  -- 319
    .integerStore 20 34,  -- 320
    .core (.pcopy 31 19),  -- 321
    .pointerSub 32 25 29,  -- 322
    .core (.pjle 11 31 325),  -- 323 N323A
    .core (.pjle 0 0 327),  -- 324
    .pointerSub 31 31 11,  -- 325 N323S
    .core (.pjle 0 0 323),  -- 326
    .core (.pjle 0 31 330),  -- 327 N323B
    .pointerAdd 31 31 11,  -- 328
    .core (.pjle 0 0 327),  -- 329
    .core (.pjle 11 32 332),  -- 330 N323D N330A
    .core (.pjle 0 0 334),  -- 331
    .pointerSub 32 32 11,  -- 332 N330S
    .core (.pjle 0 0 330),  -- 333
    .core (.pjle 0 32 337),  -- 334 N330B
    .pointerAdd 32 32 11,  -- 335
    .core (.pjle 0 0 334),  -- 336
    .pointerAdd 20 17 31,  -- 337 N330D
    .integerLoad 33 20,  -- 338
    .pointerAdd 20 18 32,  -- 339
    .integerLoad 34 20,  -- 340
    .pointerAdd 33 33 34,  -- 341
    .core (.pset 20 (7)),  -- 342
    .pointerAdd 20 20 24,  -- 343
    .integerStore 20 33,  -- 344
    .core (.pcopy 34 33),  -- 345
    .core (.pjle 13 1 348),  -- 346
    .core (.pinc 34),  -- 347
    .core (.pset 20 (15)),  -- 348 NB7
    .pointerAdd 20 20 24,  -- 349
    .integerStore 20 34,  -- 350
    .core (.pinc 23),  -- 351
    .core (.pset 20 (16)),  -- 352
    .pointerAdd 24 24 20,  -- 353
    .core (.pinc 26),  -- 354
    .core (.pjle 0 0 102),  -- 355
    .core (.pinc 25),  -- 356 VBD
    .core (.pjle 0 0 100),  -- 357
    .core (.pinc 19),  -- 358 VYD
    .core (.pjle 0 0 98) ]  -- 359

/-- `opre`, instructions 360–419. -/
def opre6 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pcopy 35 14),  -- 360 VXD
    .pointerAdd 14 14 7,  -- 361
    .core (.pcopy 36 14),  -- 362
    .core (.pset 23 (0)),  -- 363
    .core (.pcopy 37 36),  -- 364
    .core (.pjle 5 23 403),  -- 365 WV
    .core (.pset 9 (0)),  -- 366
    .core (.pjle 7 9 372),  -- 367 WZ
    .pointerAdd 20 35 9,  -- 368
    .integerStore 20 0,  -- 369
    .core (.pinc 9),  -- 370
    .core (.pjle 0 0 367),  -- 371
    .core (.pset 38 (0)),  -- 372 WZD
    .core (.pjle 8 38 401),  -- 373 WW
    .core (.pcopy 39 23),  -- 374
    .core (.pset 9 (0)),  -- 375
    .core (.pjle 7 9 385),  -- 376 WS
    .pointerAdd 20 35 9,  -- 377
    .integerLoad 33 20,  -- 378
    .pointerAdd 20 22 39,  -- 379
    .integerLoad 34 20,  -- 380
    .pointerAdd 20 34 33,  -- 381
    .integerLoad 39 20,  -- 382
    .core (.pinc 9),  -- 383
    .core (.pjle 0 0 376),  -- 384
    .integerStore 37 39,  -- 385 WSD
    .core (.pinc 37),  -- 386
    .core (.pinc 38),  -- 387
    .core (.pset 9 (0)),  -- 388
    .core (.pjle 7 9 400),  -- 389 WI
    .pointerAdd 20 35 9,  -- 390
    .integerLoad 33 20,  -- 391
    .core (.pinc 33),  -- 392
    .core (.pset 34 (16)),  -- 393
    .core (.pjle 34 33 397),  -- 394
    .integerStore 20 33,  -- 395
    .core (.pjle 0 0 400),  -- 396
    .integerStore 20 0,  -- 397 WIC
    .core (.pinc 9),  -- 398
    .core (.pjle 0 0 389),  -- 399
    .core (.pjle 0 0 373),  -- 400 WWX
    .core (.pinc 23),  -- 401 WWD
    .core (.pjle 0 0 365),  -- 402
    .core (.pcopy 14 37),  -- 403 WVD
    .core (.pcopy 40 14),  -- 404
    .pointerAdd 14 14 5,  -- 405
    .core (.pset 41 (1)),  -- 406
    .core (.pset 9 (0)),  -- 407
    .core (.pjle 3 9 412),  -- 408 EE
    .pointerAdd 41 41 4,  -- 409
    .core (.pinc 9),  -- 410
    .core (.pjle 0 0 408),  -- 411
    .core (.pjle 14 41 414),  -- 412 EED
    .core (.pcopy 41 14),  -- 413
    .core (.pinc 41),  -- 414 EEX
    .pointerAdd 42 3 5,  -- 415
    .core (.pinc 42),  -- 416
    .core (.pset 12 (2)),  -- 417
    .pointerAdd 42 42 12,  -- 418
    .pointerReal 9 3 ]  -- 419

/-- `opre`, instructions 420–479. -/
def opre7 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .pointerReal 10 5,  -- 420
    .pointerReal 11 6,  -- 421
    .core (.const 3 (2 : ℝ)),  -- 422
    .core (.mul 12 3 9),  -- 423
    .core (.mul 12 12 10),  -- 424
    .core (.div 12 12 2),  -- 425
    .core (.const 13 (1 : ℝ)),  -- 426
    .core (.pset 43 13),  -- 427
    .core (.pset 9 (0)),  -- 428
    .core (.pjle 43 9 433),  -- 429 BTP
    .core (.mul 13 13 12),  -- 430
    .core (.pinc 9),  -- 431
    .core (.pjle 0 0 429),  -- 432
    .core (.const 3 ((35123696 * (2 * (1 + 6 * c0)) ^ 13 : ℕ) : ℝ)),  -- 433 BTPD
    .core (.mul 14 3 13),  -- 434
    .core (.pset 12 (2)),  -- 435
    .pointerAdd 12 12 3,  -- 436
    .pointerReal 15 12,  -- 437
    .core (.const 3 ((82 * (1 + 6 * c0) : ℕ) : ℝ)),  -- 438
    .core (.mul 15 15 3),  -- 439
    .core (.mul 15 15 9),  -- 440
    .core (.mul 15 15 10),  -- 441
    .core (.const 3 (1 : ℝ)),  -- 442
    .core (.add 16 11 3),  -- 443
    .core (.mul 15 15 16),  -- 444
    .core (.mul 16 2 2),  -- 445
    .core (.div 15 15 16),  -- 446
    .core (.add 14 14 15),  -- 447
    .core (.pset 44 (1)),  -- 448
    .pointerReal 12 44,  -- 449 TB0
    .core (.sub 8 14 12),  -- 450
    .core (.jle 8 454),  -- 451
    .pointerAdd 44 44 44,  -- 452
    .core (.pjle 0 0 449),  -- 453
    .core (.pcopy 45 42),  -- 454 TB0D
    .core (.pset 9 (0)),  -- 455
    .core (.pjle 44 9 460),  -- 456 RD0
    .pointerAdd 45 45 45,  -- 457
    .core (.pinc 9),  -- 458
    .core (.pjle 0 0 456),  -- 459
    .pointerAdd 46 41 45,  -- 460 RD0D
    .pointerAdd 20 46 0,  -- 461
    .core (.store 20 2),  -- 462
    .integerStore 20 3,  -- 463
    .pointerAdd 20 46 1,  -- 464
    .integerStore 20 5,  -- 465
    .core (.pset 9 (0)),  -- 466
    .core (.pset 47 (1)),  -- 467
    .core (.pjle 3 9 485),  -- 468 TI
    .pointerAdd 20 15 9,  -- 469
    .integerLoad 48 20,  -- 470
    .pointerAdd 49 46 47,  -- 471
    .pointerAdd 49 49 9,  -- 472
    .core (.pset 38 (0)),  -- 473
    .core (.pjle 4 38 481),  -- 474 TC
    .pointerAdd 20 48 38,  -- 475
    .core (.load 12 20),  -- 476
    .pointerAdd 20 49 38,  -- 477
    .core (.store 20 12),  -- 478
    .core (.pinc 38) ]  -- 479

/-- `opre`, instructions 480–484. -/
def opre8 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pjle 0 0 474),  -- 480
    .core (.pinc 9),  -- 481 TCD
    .pointerAdd 47 47 5,  -- 482
    .pointerSub 47 47 1,  -- 483
    .core (.pjle 0 0 468) ]  -- 484

/-- `opre`, instructions 1299–1358. -/
def opre9 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .integerLoad 51 46,  -- 1299
    .core (.pset 52 (0)),  -- 1300
    .core (.pset 9 (0)),  -- 1301
    .core (.pjle 8 9 1306),  -- 1302 MM
    .pointerAdd 52 52 51,  -- 1303
    .core (.pinc 9),  -- 1304
    .core (.pjle 0 0 1302),  -- 1305
    .core (.pset 9 (0)),  -- 1306 MMD
    .core (.pset 16 (0)),  -- 1307
    .core (.pjle 5 9 1314),  -- 1308 WLT
    .pointerAdd 20 40 9,  -- 1309
    .integerStore 20 16,  -- 1310
    .pointerAdd 16 16 51,  -- 1311
    .core (.pinc 9),  -- 1312
    .core (.pjle 0 0 1308),  -- 1313
    .pointerAdd 53 3 52,  -- 1314 WLTD
    .core (.pinc 53),  -- 1315
    .core (.pset 12 (X3 : ℤ)),  -- 1316
    .pointerAdd 53 53 12,  -- 1317
    .pointerReal 9 3,  -- 1318
    .pointerReal 17 52,  -- 1319
    .core (.add 18 9 17),  -- 1320
    .core (.const 3 ((Cb : ℕ) : ℝ)),  -- 1321
    .core (.div 19 3 4),  -- 1322
    .core (.div 20 9 4),  -- 1323
    .core (.mul 21 18 20),  -- 1324
    .core (.const 13 (1 : ℝ)),  -- 1325
    .core (.pset 54 (K : ℤ)),  -- 1326
    .core (.pset 9 (0)),  -- 1327
    .core (.pjle 54 9 1337),  -- 1328 B3K
    .core (.mul 13 13 21),  -- 1329
    .core (.pset 55 (0)),  -- 1330
    .core (.pjle 52 55 1335),  -- 1331 B3M
    .core (.mul 13 13 19),  -- 1332
    .core (.pinc 55),  -- 1333
    .core (.pjle 0 0 1331),  -- 1334
    .core (.pinc 9),  -- 1335 B3MD
    .core (.pjle 0 0 1328),  -- 1336
    .core (.const 3 ((Cp : ℕ) : ℝ)),  -- 1337 B3KD
    .core (.mul 14 3 13),  -- 1338
    .core (.mul 15 17 17),  -- 1339
    .core (.mul 15 15 20),  -- 1340
    .core (.mul 15 15 20),  -- 1341
    .core (.mul 15 15 3),  -- 1342
    .core (.add 14 14 15),  -- 1343
    .core (.pset 44 (1)),  -- 1344
    .pointerReal 12 44,  -- 1345 TB1
    .core (.sub 8 14 12),  -- 1346
    .core (.jle 8 1350),  -- 1347
    .pointerAdd 44 44 44,  -- 1348
    .core (.pjle 0 0 1345),  -- 1349
    .core (.pcopy 56 53),  -- 1350 TB1D
    .core (.pset 9 (0)),  -- 1351
    .core (.pjle 44 9 1356),  -- 1352 RD1
    .pointerAdd 56 56 56,  -- 1353
    .core (.pinc 9),  -- 1354
    .core (.pjle 0 0 1352),  -- 1355
    .pointerAdd 57 46 45,  -- 1356 RD1D
    .core (.pinc 57),  -- 1357
    .pointerAdd 57 57 56 ]  -- 1358

/-- `opre`, instructions 1359–1389. -/
def opre10 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .pointerAdd 58 56 56,  -- 1359
    .core (.pinc 58),  -- 1360
    .core (.pset 23 (0)),  -- 1361
    .core (.pcopy 59 57),  -- 1362
    .core (.pjle 5 23 1371),  -- 1363 HD
    .core (.store 59 4),  -- 1364
    .integerStore 59 3,  -- 1365
    .pointerAdd 20 59 1,  -- 1366
    .integerStore 20 52,  -- 1367
    .core (.pinc 23),  -- 1368
    .pointerAdd 59 59 58,  -- 1369
    .core (.pjle 0 0 1363),  -- 1370
    .core (.pset 9 (0)),  -- 1371 HDD
    .core (.pset 60 (1)),  -- 1372
    .core (.pjle 3 9 1578),  -- 1373 PI
    .pointerAdd 20 15 9,  -- 1374
    .integerLoad 48 20,  -- 1375
    .core (.pset 38 (0)),  -- 1376
    .core (.pjle 5 38 1389),  -- 1377 QC
    .core (.pjle 4 38 1382),  -- 1378
    .pointerAdd 20 48 38,  -- 1379
    .core (.load 12 20),  -- 1380
    .core (.pjle 0 0 1383),  -- 1381
    .core (.const 12 (0 : ℝ)),  -- 1382 QZ
    .core (.pset 20 (-1)),  -- 1383 QS
    .pointerSub 20 20 38,  -- 1384
    .pointerAdd 20 20 46,  -- 1385
    .core (.store 20 12),  -- 1386
    .core (.pinc 38),  -- 1387
    .core (.pjle 0 0 1377),  -- 1388
    .core (.pset 200 (0)) ]  -- 1389 QCD

/-- `opre`, instructions 1550–1609. -/
def opre11 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pset 23 (0)),  -- 1550
    .core (.pcopy 59 57),  -- 1551
    .core (.pcopy 37 36),  -- 1552
    .core (.pjle 5 23 1575),  -- 1553 SV
    .core (.pset 38 (0)),  -- 1554
    .pointerAdd 49 59 60,  -- 1555
    .core (.pjle 8 38 1572),  -- 1556 SW
    .integerLoad 33 37,  -- 1557
    .pointerAdd 20 40 33,  -- 1558
    .integerLoad 48 20,  -- 1559
    .pointerAdd 48 48 46,  -- 1560
    .core (.pset 61 (0)),  -- 1561
    .core (.pjle 51 61 1569),  -- 1562 SL
    .pointerAdd 20 48 61,  -- 1563
    .core (.load 12 20),  -- 1564
    .core (.store 49 12),  -- 1565
    .core (.pinc 49),  -- 1566
    .core (.pinc 61),  -- 1567
    .core (.pjle 0 0 1562),  -- 1568
    .core (.pinc 37),  -- 1569 SLD
    .core (.pinc 38),  -- 1570
    .core (.pjle 0 0 1556),  -- 1571
    .core (.pinc 23),  -- 1572 SWD
    .pointerAdd 59 59 58,  -- 1573
    .core (.pjle 0 0 1553),  -- 1574
    .core (.pinc 9),  -- 1575 SVD
    .pointerAdd 60 60 52,  -- 1576
    .core (.pjle 0 0 1373),  -- 1577
    .core (.pset 23 (0)),  -- 1578 PID
    .core (.pcopy 59 57),  -- 1579
    .core (.pjle 5 23 1585),  -- 1580 IP
    .core (.pjle 0 0 1612),  -- 1581
    .core (.pinc 23),  -- 1582 RET3
    .pointerAdd 59 59 58,  -- 1583
    .core (.pjle 0 0 1580),  -- 1584
    .core (.pset 20 (2)),  -- 1585 IPD
    .integerStore 20 3,  -- 1586
    .core (.pset 20 (3)),  -- 1587
    .integerStore 20 4,  -- 1588
    .core (.pset 20 (4)),  -- 1589
    .integerStore 20 5,  -- 1590
    .core (.pset 20 (5)),  -- 1591
    .integerStore 20 51,  -- 1592
    .core (.pset 20 (6)),  -- 1593
    .integerStore 20 52,  -- 1594
    .core (.pset 20 (7)),  -- 1595
    .integerStore 20 8,  -- 1596
    .core (.pset 20 (8)),  -- 1597
    .integerStore 20 7,  -- 1598
    .core (.pset 20 (9)),  -- 1599
    .integerStore 20 46,  -- 1600
    .core (.pset 20 (10)),  -- 1601
    .integerStore 20 57,  -- 1602
    .core (.pset 20 (11)),  -- 1603
    .integerStore 20 58,  -- 1604
    .core (.pset 20 (12)),  -- 1605
    .integerStore 20 36,  -- 1606
    .core (.pset 20 (13)),  -- 1607
    .integerStore 20 40,  -- 1608
    .core (.pset 20 (14)) ]  -- 1609

/-- `opre`, instructions 1610–1611. -/
def opre12 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .integerStore 20 15,  -- 1610
    .halt ]  -- 1611 HALT

/-- `oqry`, instructions 0–36. -/
def oqry0 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pset 1 (1)),  -- 0
    .integerLoad 3 0,  -- 1
    .core (.pjle 3 1 253),  -- 2
    .core (.pset 20 (3)),  -- 3
    .integerLoad 4 20,  -- 4
    .core (.pset 20 (4)),  -- 5
    .integerLoad 5 20,  -- 6
    .core (.pset 20 (5)),  -- 7
    .integerLoad 51 20,  -- 8
    .core (.pset 20 (6)),  -- 9
    .integerLoad 52 20,  -- 10
    .core (.pset 20 (7)),  -- 11
    .integerLoad 8 20,  -- 12
    .core (.pset 20 (8)),  -- 13
    .integerLoad 7 20,  -- 14
    .core (.pset 20 (9)),  -- 15
    .integerLoad 46 20,  -- 16
    .core (.pset 20 (10)),  -- 17
    .integerLoad 57 20,  -- 18
    .core (.pset 20 (11)),  -- 19
    .integerLoad 58 20,  -- 20
    .core (.pset 20 (12)),  -- 21
    .integerLoad 36 20,  -- 22
    .core (.pset 20 (13)),  -- 23
    .integerLoad 40 20,  -- 24
    .core (.pset 20 (14)),  -- 25
    .integerLoad 15 20,  -- 26
    .core (.pset 38 (0)),  -- 27
    .core (.pjle 4 38 36),  -- 28 QQ
    .core (.pset 20 (-1)),  -- 29
    .pointerSub 20 20 38,  -- 30
    .core (.load 12 20),  -- 31
    .pointerAdd 20 20 46,  -- 32
    .core (.store 20 12),  -- 33
    .core (.pinc 38),  -- 34
    .core (.pjle 0 0 28),  -- 35
    .core (.pset 200 (0)) ]  -- 36 QQD

/-- `oqry`, instructions 197–254. -/
def oqry1 (c0 Cb K Cp X3 : ℕ) : Program :=
  [ .core (.pset 23 (0)),  -- 197
    .core (.pcopy 59 57),  -- 198
    .core (.pcopy 37 36),  -- 199
    .core (.pset 63 (1)),  -- 200
    .core (.pset 64 (0)),  -- 201
    .core (.pjle 5 23 251),  -- 202 QV
    .core (.pset 38 (0)),  -- 203
    .core (.pset 49 (-1)),  -- 204
    .pointerAdd 49 49 59,  -- 205
    .core (.pjle 8 38 222),  -- 206 QW
    .integerLoad 33 37,  -- 207
    .pointerAdd 20 40 33,  -- 208
    .integerLoad 48 20,  -- 209
    .pointerAdd 48 48 46,  -- 210
    .core (.pset 61 (0)),  -- 211
    .core (.pjle 51 61 219),  -- 212 QL
    .pointerAdd 20 48 61,  -- 213
    .core (.load 12 20),  -- 214
    .core (.store 49 12),  -- 215
    .core (.pdec 49),  -- 216
    .core (.pinc 61),  -- 217
    .core (.pjle 0 0 212),  -- 218
    .core (.pinc 37),  -- 219 QLD
    .core (.pinc 38),  -- 220
    .core (.pjle 0 0 206),  -- 221
    .core (.pjle 0 0 255),  -- 222 QWD
    .core (.pcopy 19 300),  -- 223 RETQ
    .pointerAdd 20 15 19,  -- 224
    .integerLoad 48 20,  -- 225
    .core (.const 18 (0 : ℝ)),  -- 226
    .core (.pset 38 (0)),  -- 227
    .core (.pjle 4 38 239),  -- 228 QD
    .pointerAdd 20 48 38,  -- 229
    .core (.load 12 20),  -- 230
    .core (.pset 20 (-1)),  -- 231
    .pointerSub 20 20 38,  -- 232
    .core (.load 15 20),  -- 233
    .core (.sub 12 12 15),  -- 234
    .core (.mul 12 12 12),  -- 235
    .core (.add 18 18 12),  -- 236
    .core (.pinc 38),  -- 237
    .core (.pjle 0 0 228),  -- 238
    .core (.pjle 63 0 244),  -- 239 QDD
    .core (.pset 63 (0)),  -- 240
    .core (.add 22 18 1),  -- 241
    .core (.pcopy 64 19),  -- 242
    .core (.pjle 0 0 248),  -- 243
    .core (.sub 8 22 18),  -- 244 QCMP
    .core (.jle 8 248),  -- 245
    .core (.add 22 18 1),  -- 246
    .core (.pcopy 64 19),  -- 247
    .core (.pinc 23),  -- 248 QN
    .pointerAdd 59 59 58,  -- 249
    .core (.pjle 0 0 202),  -- 250
    .core (.pcopy 0 64),  -- 251 QVD
    .halt,  -- 252
    .core (.pset 0 (0)),  -- 253 QSMALL
    .halt ]  -- 254

/-- The main part of the outer preprocessing program (1612 instructions). -/
def outerPreMain (c0 Cb K Cp X3 : ℕ) : Program :=
  opre0 c0 Cb K Cp X3 ++
    opre1 c0 Cb K Cp X3 ++
    opre2 c0 Cb K Cp X3 ++
    opre3 c0 Cb K Cp X3 ++
    opre4 c0 Cb K Cp X3 ++
    opre5 c0 Cb K Cp X3 ++
    opre6 c0 Cb K Cp X3 ++
    opre7 c0 Cb K Cp X3 ++
    opre8 c0 Cb K Cp X3 ++
    reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++
    opre9 c0 Cb K Cp X3 ++
    opre10 c0 Cb K Cp X3 ++
    reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++
    opre11 c0 Cb K Cp X3 ++
    opre12 c0 Cb K Cp X3

/-- The outer preprocessing program. -/
def outerPre (Pre₃ : Program) (n3 c0 Cb K Cp X3 : ℕ) : Program :=
  outerPreMain c0 Cb K Cp X3 ++
    (zeroRegs 300 300 n3 n3 ++ reloc ⟨1612 + 2 * n3, 300, 300, 59, 62, 1582⟩ Pre₃)

/-- The main part of the outer query program (255 instructions). -/
def outerQryMain (c0 Cb K Cp X3 : ℕ) : Program :=
  oqry0 c0 Cb K Cp X3 ++
    reloc ⟨37, 200, 200, 46, 50, 197⟩ (ev 0) ++
    oqry1 c0 Cb K Cp X3

/-- The outer query program. -/
def outerQry (Qry₃ : Program) (n3 c0 Cb K Cp X3 : ℕ) : Program :=
  outerQryMain c0 Cb K Cp X3 ++
    (zeroRegs 300 300 n3 n3 ++ reloc ⟨255 + 2 * n3, 300, 300, 59, 62, 223⟩ Qry₃)

end

end DetANN.Thm11


