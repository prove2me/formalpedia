-- Prove2me | Definitions.Def_DetANN_Supplement_PreProg
-- name    : DetANN_Supplement_PreProg
-- status  : Definition
-- author  : @milia
-- created : 2026-11-21T03:39:10.7696+00:00
-- url     : https://prove2.me/theorems/8c1efcd4-a0dd-4e7c-bce2-7aded1c3ef89
-- title:
--   The construction program of the signed Hadamard blocks
-- statement:
--   A program $\mathrm{pre}(q,o)$ of the real RAM `PNormReg_Machine` (407 instructions, absolute jump targets $o+\ell$), with a rational parameter $q$. It is the preprocessing half of Theorem 3.2 (§6.1, p.14): from the points $P_0,\dots,P_{n-1}\in\mathbb R^{d}$, $d=2^k$, and $\tau$, it chooses the $Ld$ signs $\xi$ of the signed Hadamard blocks greedily by the conditional expectation of Lemma 6.2.
--
--   It is the concatenation $\mathrm{preA}(o)\mathbin{+\!\!+}\mathrm{fw}(o+41)\mathbin{+\!\!+}\mathrm{preB}_0(o)\mathbin{+\!\!+}\dots\mathbin{+\!\!+}\mathrm{preB}_6(o)$, where $\mathrm{fw}$ is the FWHT block of definition `DetANN_Supplement_EvProg`. In order, it:
--   1. reads $n$, $d$ (integer cells 0, 1) and $\tau$ (real cell 0), writes the strides $2^u$ to integer cells $2+u$, and builds the Sylvester columns $H e_r$ by running $\mathrm{fw}$ on unit vectors;
--   2. appends the differences $P_i-P_j$ ($i<j$) to a table, skipping those already present;
--   3. computes $p_0$, the least $p$ with $8Nd\le4^p$ ($N$ the table size), and $L$, the least power of two with $q\,p_0\le L\tau^2$, by counting loops; allocates its arrays; writes the factorials $i!$, $i\le4p_0$; sets all signs to $-1$;
--   4. for each sign in turn, keeps the value $+1$ or $-1$ for which its subroutine `EVAL` (the truncated power series of `lemma62Expr`) is smaller (ties go to $+1$), then writes $L$ to integer cell 0 and halts.
--
--   The signs are stored at the real cells $-d-1-k$, $k<Ld$, the layout read by $\mathrm{ev}$. The register map is listed in the file header.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a proof of DetANN.Supplement.theorem_3_2 (Feng, Indyk, STOC 2027 submission, Theorem 3.2, p.7; the construction of §6.1, p.14, and Lemma 6.2). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_Supplement_EvProg

/-!
# Milestone 21 (`DetANN.Supplement.theorem_3_2`): the construction program `Pre`

`pre q off` constructs the signs of Theorem 3.2 greedily. It reuses the FWHT block `fw`
(definition `DetANN_Supplement_EvProg`) for the Hadamard columns; `q` is the rational constant of the
repetition count `L` (the least power of two with `L·τ² ≥ q·p₀`).

Pointers: `0` zero, `1` one, `2` two, `3` d, `4` cnt, `5` t, `6` ta, `7` h, `8` h2, `9` s, `10` i, `11` a, `12` b, `13` fb, `14` L, `15` Sb, `16` l, `17` ib, `18` r, `19` idx, `20` j, `21` o, `22` n, `23` top, `24` Hb, `25` col, `26` Db, `27` Dend, `28` Dc, `29` pi, `30` pj, `31` c, `32` e, `33` X, `34` p0, `35` pw, `36` P2, `37` P21, `38` K, `39` K1, `40` Fb, `41` Cb, `42` Tb, `43` PNb, `44` Gb, `45` TGb, `46` Eb, `47` LD, `48` k, `49` ak, `50` ret, `51` v, `52` hc, `53` m, `54` par, `55` m1, `56` kk, `57` kk1, `58` i2. Reals: `0` x, `1` y, `2` u, `3` w, `4` sc, `5` tau, `6` zero, `7` one, `8` mone, `9` q, `10` tg, `11` t2, `12` Et, `13` tot, `14` nv, `15` mn, `16` Lr, `17` bs, `18` coef, `19` F, `20` tm, `21` h, `22` av, `23` s, `24` at.
-/

namespace DetANN.Supplement.Thm32

open PNormReg

/-- Pre, part before the transform (labels absolute in `pre`). -/
def preA (q : ℚ) (off : ℕ) : Program :=
  [ .core (.pset 1 (1)),  -- 0
    .core (.pset 2 (2)),  -- 1
    .integerLoad 22 0,  -- 2
    .integerLoad 3 1,  -- 3
    .core (.load 5 0),  -- 4
    .core (.const 6 (0 : ℝ)),  -- 5
    .core (.const 7 (1 : ℝ)),  -- 6
    .core (.const 8 (-1 : ℝ)),  -- 7
    .core (.pset 23 (1)),  -- 8
    .core (.pset 10 (0)),  -- 9
    .core (.pjle 22 10 (off + 14)),  -- 10 TOP
    .pointerAdd 23 23 3,  -- 11
    .core (.pinc 10),  -- 12
    .core (.pjle 0 0 (off + 10)),  -- 13
    .core (.pset 7 (1)),  -- 14 TOPD
    .core (.pset 4 (0)),  -- 15
    .core (.pset 6 (2)),  -- 16
    .core (.pjle 3 7 (off + 23)),  -- 17 ST
    .integerStore 6 7,  -- 18
    .core (.pinc 6),  -- 19
    .core (.pinc 4),  -- 20
    .pointerAdd 7 7 7,  -- 21
    .core (.pjle 0 0 (off + 17)),  -- 22
    .core (.pcopy 24 23),  -- 23 STD
    .core (.pset 10 (0)),  -- 24
    .core (.pjle 3 10 (off + 29)),  -- 25 HT
    .pointerAdd 23 23 3,  -- 26
    .core (.pinc 10),  -- 27
    .core (.pjle 0 0 (off + 25)),  -- 28
    .core (.pset 18 (0)),  -- 29 HTD
    .core (.pcopy 25 24),  -- 30
    .core (.pjle 3 18 (off + 67)),  -- 31 HC
    .core (.pset 10 (0)),  -- 32
    .core (.pjle 3 10 (off + 38)),  -- 33 HZ
    .pointerAdd 11 25 10,  -- 34
    .core (.store 11 6),  -- 35
    .core (.pinc 10),  -- 36
    .core (.pjle 0 0 (off + 33)),  -- 37
    .pointerAdd 11 25 18,  -- 38 HZD
    .core (.store 11 7),  -- 39
    .core (.pcopy 13 25) ]  -- 40

/-- Pre, instructions 64–114. -/
def preB0 (q : ℚ) (off : ℕ) : Program :=
  [ .pointerAdd 25 25 3,  -- 64 FWRET
    .core (.pinc 18),  -- 65
    .core (.pjle 0 0 (off + 31)),  -- 66
    .core (.pcopy 26 23),  -- 67 HCD
    .core (.pcopy 27 23),  -- 68
    .core (.pset 28 (0)),  -- 69
    .core (.pset 10 (0)),  -- 70
    .core (.pset 29 (1)),  -- 71
    .core (.pjle 22 10 (off + 114)),  -- 72 DI
    .core (.pcopy 20 10),  -- 73
    .core (.pinc 20),  -- 74
    .pointerAdd 30 29 3,  -- 75
    .core (.pjle 22 20 (off + 111)),  -- 76 DJ
    .core (.pset 31 (0)),  -- 77
    .core (.pjle 3 31 (off + 88)),  -- 78 W
    .pointerAdd 11 29 31,  -- 79
    .core (.load 0 11),  -- 80
    .pointerAdd 11 30 31,  -- 81
    .core (.load 1 11),  -- 82
    .core (.sub 0 0 1),  -- 83
    .pointerAdd 11 27 31,  -- 84
    .core (.store 11 0),  -- 85
    .core (.pinc 31),  -- 86
    .core (.pjle 0 0 (off + 78)),  -- 87
    .core (.pcopy 32 26),  -- 88 WD
    .core (.pjle 27 32 (off + 106)),  -- 89 E
    .core (.pset 31 (0)),  -- 90
    .core (.pjle 3 31 (off + 108)),  -- 91 C
    .pointerAdd 11 32 31,  -- 92
    .core (.load 0 11),  -- 93
    .pointerAdd 11 27 31,  -- 94
    .core (.load 1 11),  -- 95
    .core (.sub 2 0 1),  -- 96
    .core (.jle 2 (off + 99)),  -- 97
    .core (.pjle 0 0 (off + 104)),  -- 98
    .core (.sub 2 1 0),  -- 99 CK2
    .core (.jle 2 (off + 102)),  -- 100
    .core (.pjle 0 0 (off + 104)),  -- 101
    .core (.pinc 31),  -- 102 CEQ
    .core (.pjle 0 0 (off + 91)),  -- 103
    .pointerAdd 32 32 3,  -- 104 EN
    .core (.pjle 0 0 (off + 89)),  -- 105
    .pointerAdd 27 27 3,  -- 106 NEWV
    .core (.pinc 28),  -- 107
    .core (.pinc 20),  -- 108 DUP
    .pointerAdd 30 30 3,  -- 109
    .core (.pjle 0 0 (off + 76)),  -- 110
    .core (.pinc 10),  -- 111 DJD
    .pointerAdd 29 29 3,  -- 112
    .core (.pjle 0 0 (off + 72)),  -- 113
    .core (.pcopy 23 27) ]  -- 114 DID

/-- Pre, instructions 115–187. -/
def preB1 (q : ℚ) (off : ℕ) : Program :=
  [ .core (.pset 33 (0)),  -- 115
    .core (.pset 10 (0)),  -- 116
    .core (.pjle 28 10 (off + 121)),  -- 117 X
    .pointerAdd 33 33 3,  -- 118
    .core (.pinc 10),  -- 119
    .core (.pjle 0 0 (off + 117)),  -- 120
    .pointerAdd 33 33 33,  -- 121 XD
    .pointerAdd 33 33 33,  -- 122
    .pointerAdd 33 33 33,  -- 123
    .core (.pset 34 (0)),  -- 124
    .core (.pset 35 (1)),  -- 125
    .core (.pjle 33 35 (off + 131)),  -- 126 P
    .pointerAdd 35 35 35,  -- 127
    .pointerAdd 35 35 35,  -- 128
    .core (.pinc 34),  -- 129
    .core (.pjle 0 0 (off + 126)),  -- 130
    .pointerAdd 36 34 34,  -- 131 PD
    .core (.pcopy 37 36),  -- 132
    .core (.pinc 37),  -- 133
    .pointerAdd 38 36 36,  -- 134
    .core (.pcopy 39 38),  -- 135
    .core (.pinc 39),  -- 136
    .pointerReal 0 34,  -- 137
    .core (.const 9 ((q : ℚ) : ℝ)),  -- 138
    .core (.mul 10 9 0),  -- 139
    .core (.mul 11 5 5),  -- 140
    .core (.pset 14 (1)),  -- 141
    .pointerReal 0 14,  -- 142 LL
    .core (.mul 2 0 11),  -- 143
    .core (.sub 2 10 2),  -- 144
    .core (.jle 2 (off + 148)),  -- 145
    .pointerAdd 14 14 14,  -- 146
    .core (.pjle 0 0 (off + 142)),  -- 147
    .core (.pcopy 40 23),  -- 148 LD
    .pointerAdd 23 23 39,  -- 149
    .core (.pcopy 41 23),  -- 150
    .pointerAdd 23 23 39,  -- 151
    .core (.pcopy 42 23),  -- 152
    .pointerAdd 23 23 39,  -- 153
    .core (.pcopy 43 23),  -- 154
    .pointerAdd 23 23 37,  -- 155
    .core (.pcopy 44 23),  -- 156
    .pointerAdd 23 23 37,  -- 157
    .core (.pcopy 45 23),  -- 158
    .pointerAdd 23 23 37,  -- 159
    .core (.pcopy 46 23),  -- 160
    .pointerAdd 23 23 37,  -- 161
    .core (.store 40 7),  -- 162
    .core (.pset 10 (1)),  -- 163
    .core (.pjle 39 10 (off + 174)),  -- 164 FT
    .pointerReal 1 10,  -- 165
    .pointerAdd 11 40 10,  -- 166
    .core (.pdec 11),  -- 167
    .core (.load 0 11),  -- 168
    .core (.mul 0 0 1),  -- 169
    .core (.pinc 11),  -- 170
    .core (.store 11 0),  -- 171
    .core (.pinc 10),  -- 172
    .core (.pjle 0 0 (off + 164)),  -- 173
    .core (.pset 15 (-1)),  -- 174 FTD
    .pointerSub 15 15 3,  -- 175
    .core (.pset 47 (0)),  -- 176
    .core (.pset 10 (0)),  -- 177
    .core (.pjle 14 10 (off + 182)),  -- 178 LDL
    .pointerAdd 47 47 3,  -- 179
    .core (.pinc 10),  -- 180
    .core (.pjle 0 0 (off + 178)),  -- 181
    .core (.pset 48 (0)),  -- 182 LDD
    .core (.pjle 47 48 (off + 188)),  -- 183 SI
    .pointerSub 11 15 48,  -- 184
    .core (.store 11 8),  -- 185
    .core (.pinc 48),  -- 186
    .core (.pjle 0 0 (off + 183)) ]  -- 187

/-- Pre, instructions 188–240. -/
def preB2 (q : ℚ) (off : ℕ) : Program :=
  [ .core (.pset 48 (0)),  -- 188 SID
    .core (.pjle 47 48 (off + 204)),  -- 189 G
    .pointerSub 49 15 48,  -- 190
    .core (.store 49 7),  -- 191
    .core (.pset 50 (0)),  -- 192
    .core (.pjle 0 0 (off + 206)),  -- 193
    .core (.add 12 13 6),  -- 194 R0
    .core (.store 49 8),  -- 195
    .core (.pset 50 (1)),  -- 196
    .core (.pjle 0 0 (off + 206)),  -- 197
    .core (.sub 2 12 13),  -- 198 R1
    .core (.jle 2 (off + 201)),  -- 199
    .core (.pjle 0 0 (off + 202)),  -- 200
    .core (.store 49 7),  -- 201 SETT
    .core (.pinc 48),  -- 202 GN
    .core (.pjle 0 0 (off + 189)),  -- 203
    .integerStore 0 14,  -- 204 GD
    .halt,  -- 205
    .core (.const 13 (0 : ℝ)),  -- 206 EVAL
    .core (.pcopy 51 26),  -- 207
    .core (.pjle 27 51 (off + 405)),  -- 208 EV
    .core (.const 14 (0 : ℝ)),  -- 209
    .core (.pset 31 (0)),  -- 210
    .core (.pjle 3 31 (off + 218)),  -- 211 EN2
    .pointerAdd 11 51 31,  -- 212
    .core (.load 0 11),  -- 213
    .core (.mul 0 0 0),  -- 214
    .core (.add 14 14 0),  -- 215
    .core (.pinc 31),  -- 216
    .core (.pjle 0 0 (off + 211)),  -- 217
    .core (.sub 15 6 14),  -- 218 END2
    .core (.const 0 (1 : ℝ)),  -- 219
    .core (.pset 5 (0)),  -- 220
    .core (.pjle 37 5 (off + 227)),  -- 221 PN
    .pointerAdd 11 43 5,  -- 222
    .core (.store 11 0),  -- 223
    .core (.mul 0 0 15),  -- 224
    .core (.pinc 5),  -- 225
    .core (.pjle 0 0 (off + 221)),  -- 226
    .pointerReal 16 14,  -- 227 PND
    .core (.mul 17 16 5),  -- 228
    .core (.mul 17 17 14),  -- 229
    .core (.const 0 (1 : ℝ)),  -- 230
    .core (.pset 5 (0)),  -- 231
    .core (.pjle 36 5 (off + 236)),  -- 232 BP
    .core (.mul 0 0 17),  -- 233
    .core (.pinc 5),  -- 234
    .core (.pjle 0 0 (off + 232)),  -- 235
    .core (.div 18 7 0),  -- 236 BPD
    .pointerAdd 11 40 36,  -- 237
    .core (.load 1 11),  -- 238
    .core (.mul 18 18 1),  -- 239
    .core (.pset 20 (0)) ]  -- 240

/-- Pre, instructions 241–281. -/
def preB3 (q : ℚ) (off : ℕ) : Program :=
  [ .core (.pjle 3 20 (off + 403)),  -- 241 EJ
    .core (.pset 5 (0)),  -- 242
    .core (.pjle 37 5 (off + 248)),  -- 243 G0
    .pointerAdd 11 44 5,  -- 244
    .core (.store 11 6),  -- 245
    .core (.pinc 5),  -- 246
    .core (.pjle 0 0 (off + 243)),  -- 247
    .core (.store 44 7),  -- 248 G0D
    .core (.pset 16 (0)),  -- 249
    .core (.pset 17 (0)),  -- 250
    .core (.pjle 14 16 (off + 397)),  -- 251 EL
    .core (.const 19 (0 : ℝ)),  -- 252
    .core (.pset 18 (0)),  -- 253
    .pointerAdd 52 24 20,  -- 254
    .core (.pjle 3 18 (off + 271)),  -- 255 EF
    .pointerAdd 19 17 18,  -- 256
    .core (.const 20 (0 : ℝ)),  -- 257
    .core (.pjle 19 48 (off + 260)),  -- 258
    .core (.pjle 0 0 (off + 267)),  -- 259
    .core (.load 21 52),  -- 260 EFX
    .pointerAdd 11 51 18,  -- 261
    .core (.load 0 11),  -- 262
    .core (.mul 20 21 0),  -- 263
    .pointerSub 11 15 19,  -- 264
    .core (.load 0 11),  -- 265
    .core (.mul 20 20 0),  -- 266
    .core (.add 19 19 20),  -- 267 EFA
    .core (.pinc 18),  -- 268
    .pointerAdd 52 52 3,  -- 269
    .core (.pjle 0 0 (off + 255)),  -- 270
    .core (.const 0 (1 : ℝ)),  -- 271 EFD
    .core (.pset 5 (0)),  -- 272
    .core (.pjle 39 5 (off + 282)),  -- 273 C0
    .pointerAdd 11 40 5,  -- 274
    .core (.load 1 11),  -- 275
    .core (.div 1 0 1),  -- 276
    .pointerAdd 11 41 5,  -- 277
    .core (.store 11 1),  -- 278
    .core (.mul 0 0 19),  -- 279
    .core (.pinc 5),  -- 280
    .core (.pjle 0 0 (off + 273)) ]  -- 281

/-- Pre, instructions 282–329. -/
def preB4 (q : ℚ) (off : ℕ) : Program :=
  [ .core (.pset 18 (0)),  -- 282 C0D
    .pointerAdd 52 24 20,  -- 283
    .core (.pjle 3 18 (off + 330)),  -- 284 ER
    .pointerAdd 19 17 18,  -- 285
    .core (.const 22 (0 : ℝ)),  -- 286
    .core (.pjle 19 48 (off + 292)),  -- 287
    .core (.load 21 52),  -- 288
    .pointerAdd 11 51 18,  -- 289
    .core (.load 0 11),  -- 290
    .core (.mul 22 21 0),  -- 291
    .core (.pset 53 (0)),  -- 292 ERA
    .core (.pjle 39 53 (off + 319)),  -- 293 EM
    .core (.const 23 (0 : ℝ)),  -- 294
    .core (.const 24 (1 : ℝ)),  -- 295
    .core (.pset 5 (0)),  -- 296
    .core (.pset 54 (0)),  -- 297
    .core (.pcopy 55 53),  -- 298
    .core (.pinc 55),  -- 299
    .core (.pjle 55 5 (off + 315)),  -- 300 ET
    .core (.pjle 54 0 (off + 303)),  -- 301
    .core (.pjle 0 0 (off + 311)),  -- 302
    .pointerAdd 11 40 5,  -- 303 ETE
    .core (.load 1 11),  -- 304
    .core (.div 1 24 1),  -- 305
    .pointerSub 11 53 5,  -- 306
    .pointerAdd 11 41 11,  -- 307
    .core (.load 0 11),  -- 308
    .core (.mul 1 1 0),  -- 309
    .core (.add 23 23 1),  -- 310
    .core (.mul 24 24 22),  -- 311 ETN
    .core (.pinc 5),  -- 312
    .pointerSub 54 1 54,  -- 313
    .core (.pjle 0 0 (off + 300)),  -- 314
    .pointerAdd 11 42 53,  -- 315 ETD
    .core (.store 11 23),  -- 316
    .core (.pinc 53),  -- 317
    .core (.pjle 0 0 (off + 293)),  -- 318
    .core (.pset 5 (0)),  -- 319 EMD
    .core (.pjle 39 5 (off + 327)),  -- 320 CP
    .pointerAdd 11 42 5,  -- 321
    .core (.load 0 11),  -- 322
    .pointerAdd 11 41 5,  -- 323
    .core (.store 11 0),  -- 324
    .core (.pinc 5),  -- 325
    .core (.pjle 0 0 (off + 320)),  -- 326
    .core (.pinc 18),  -- 327 CPD
    .pointerAdd 52 52 3,  -- 328
    .core (.pjle 0 0 (off + 284)) ]  -- 329

/-- Pre, instructions 330–396. -/
def preB5 (q : ℚ) (off : ℕ) : Program :=
  [ .core (.pset 56 (0)),  -- 330 ERD
    .core (.pjle 37 56 (off + 366)),  -- 331 EK
    .core (.const 23 (0 : ℝ)),  -- 332
    .core (.pset 10 (0)),  -- 333
    .core (.pcopy 57 56),  -- 334
    .core (.pinc 57),  -- 335
    .core (.pjle 57 10 (off + 359)),  -- 336 EI
    .pointerAdd 11 40 56,  -- 337
    .core (.load 0 11),  -- 338
    .pointerAdd 11 40 10,  -- 339
    .core (.load 1 11),  -- 340
    .core (.div 0 0 1),  -- 341
    .pointerSub 12 56 10,  -- 342
    .pointerAdd 11 40 12,  -- 343
    .core (.load 1 11),  -- 344
    .core (.div 0 0 1),  -- 345
    .pointerAdd 11 43 12,  -- 346
    .core (.load 1 11),  -- 347
    .core (.mul 0 0 1),  -- 348
    .pointerAdd 58 10 10,  -- 349
    .pointerAdd 11 40 58,  -- 350
    .core (.load 1 11),  -- 351
    .core (.mul 0 0 1),  -- 352
    .pointerAdd 11 41 58,  -- 353
    .core (.load 1 11),  -- 354
    .core (.mul 0 0 1),  -- 355
    .core (.add 23 23 0),  -- 356
    .core (.pinc 10),  -- 357
    .core (.pjle 0 0 (off + 336)),  -- 358
    .pointerAdd 11 40 56,  -- 359 EID
    .core (.load 1 11),  -- 360
    .core (.div 23 23 1),  -- 361
    .pointerAdd 11 46 56,  -- 362
    .core (.store 11 23),  -- 363
    .core (.pinc 56),  -- 364
    .core (.pjle 0 0 (off + 331)),  -- 365
    .core (.pset 53 (0)),  -- 366 EKD
    .core (.pjle 37 53 (off + 386)),  -- 367 GM
    .core (.const 23 (0 : ℝ)),  -- 368
    .core (.pset 5 (0)),  -- 369
    .core (.pcopy 55 53),  -- 370
    .core (.pinc 55),  -- 371
    .core (.pjle 55 5 (off + 382)),  -- 372 GT
    .pointerAdd 11 44 5,  -- 373
    .core (.load 0 11),  -- 374
    .pointerSub 12 53 5,  -- 375
    .pointerAdd 11 46 12,  -- 376
    .core (.load 1 11),  -- 377
    .core (.mul 0 0 1),  -- 378
    .core (.add 23 23 0),  -- 379
    .core (.pinc 5),  -- 380
    .core (.pjle 0 0 (off + 372)),  -- 381
    .pointerAdd 11 45 53,  -- 382 GTD
    .core (.store 11 23),  -- 383
    .core (.pinc 53),  -- 384
    .core (.pjle 0 0 (off + 367)),  -- 385
    .core (.pset 5 (0)),  -- 386 GMD
    .core (.pjle 37 5 (off + 394)),  -- 387 GC
    .pointerAdd 11 45 5,  -- 388
    .core (.load 0 11),  -- 389
    .pointerAdd 11 44 5,  -- 390
    .core (.store 11 0),  -- 391
    .core (.pinc 5),  -- 392
    .core (.pjle 0 0 (off + 387)),  -- 393
    .core (.pinc 16),  -- 394 GCD
    .pointerAdd 17 17 3,  -- 395
    .core (.pjle 0 0 (off + 251)) ]  -- 396

/-- Pre, instructions 397–406. -/
def preB6 (q : ℚ) (off : ℕ) : Program :=
  [ .pointerAdd 11 44 36,  -- 397 ELD
    .core (.load 0 11),  -- 398
    .core (.mul 0 0 18),  -- 399
    .core (.add 13 13 0),  -- 400
    .core (.pinc 20),  -- 401
    .core (.pjle 0 0 (off + 241)),  -- 402
    .pointerAdd 51 51 3,  -- 403 EVN
    .core (.pjle 0 0 (off + 208)),  -- 404
    .core (.pjle 50 0 (off + 194)),  -- 405 ERET
    .core (.pjle 0 0 (off + 198)) ]  -- 406

/-- The construction program. -/
def pre (q : ℚ) (off : ℕ) : Program := preA q off ++ fw (off + 41) ++ (preB0 q off ++ preB1 q off ++ preB2 q off ++ preB3 q off ++ preB4 q off ++ preB5 q off ++ preB6 q off)

end DetANN.Supplement.Thm32


