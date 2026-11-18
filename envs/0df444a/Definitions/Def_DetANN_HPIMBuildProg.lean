-- Prove2me | Definitions.Def_DetANN_HPIMBuildProg
-- name    : DetANN_HPIMBuildProg
-- status  : Definition
-- author  : @milia
-- created : 2026-11-17T21:33:02.678096+00:00
-- url     : https://prove2.me/theorems/ee9a652b-6b1b-47d4-b7cd-4308914bf50d
-- title:
--   The BSP construction block program
-- statement:
--   The program of the BSP construction block of `build_block`, on the PNormReg machine (definition `PNormReg_Machine`), and eight helpers used to state its correctness in pieces.
--
--   1. **The program** $\mathrm{bd}(o)$ has 396 instructions with absolute jump targets $o+\ell$, written as a right-associated append of 17 segments. It computes `build pts r c f lo hi` (definition `DetANN_HPIMBuild`) with an explicit worklist.
--      - A *task* is a pair $(p,\sigma)$: a real address $p$ holding a box $[lo,hi]$ ($lo_j$ at $p+j$, $hi_j$ at $p+j+m$) and an integer slot $\sigma$. Processing the task stores into $I[\sigma]$ the address of the subtree built for that box.
--      - Tasks wait on a stack of 3-cell entries $[p,\sigma,\mathrm{link}]$ in integer scratch below pointer 13. Pointer 40 holds the initial top $Z_0$, which marks the empty stack.
--      - Maxima and minima of two reals are computed without branching, as $(a+b\pm\sqrt{(a-b)^2})/2$.
--
--      The segments:
--      - **init** (0–33): the constants, a copy of the root box below pointer 14, the root slot $Z_0-1$ and the first task.
--      - **dispatch** (34–52): pop a task (or go to the end), allocate the near box $q$ below pointer 14, and start the point scan.
--      - **scan** (53–133): for each point, both squared box distances as sums over the coordinates. The first point with $\mathrm{boxDist2}\le r^2$ and $\mathrm{boxMaxDist2}\le(cr)^2$ gives a certified leaf. Otherwise $q$ becomes the bounding box of the near points.
--      - **core box and sides** (134–196): $q$ becomes the core $[\max(a_j-2r,lo_j),\min(b_j+2r,hi_j)]$, and the longest sides $\sigma$ of the core and of the box are computed.
--      - **split** (197–257): the first longest axis $k$, a cut node, the two halves at the midpoint, and two pushed tasks.
--      - **copy-and-set** (258–279): a subroutine that copies the box at pointer 50 to fresh real scratch, overwrites cell $51$ of the copy with real 44, and returns by the code in pointer 58.
--      - **carve** (280–382): on each axis in turn, the low slab and then the high slab are peeled when they are nonempty. Each peel writes a cut node and pushes the slab as a task. At the end the core box is pushed.
--      - **leaf and end** (383–395): a leaf node $[0,p,a]$; at the end, the root is loaded into pointer 17.
--   2. **Helpers.**
--      - `BoxAt s p lo hi`: the box $[lo,hi]$ is stored at real address $p$.
--      - `t1`, `t2`: the $j$-th terms of $\mathrm{boxDist2}$ and $\mathrm{boxMaxDist2}$ for a point; `psum g k` $=\sum_{j<k}g_j$.
--      - `rmax g k` $=\max_{j\le k}g(j)$, and `side lo hi j` $=hi_j-lo_j$ (0 for $j\ge m$).
--      - `Env s pts r c Z0`: the points are stored (`LocalPts`). Real registers 11, 12 hold $r$, $c$. The constant registers hold pointers $40\mapsto Z_0$, $60\mapsto 2m$, $68\mapsto1$, $69\mapsto0$ and reals $40\mapsto r^2$, $41\mapsto(cr)^2$, $49\mapsto2r$, $50\mapsto0$, $53\mapsto2$.
--      - `Fr Q s s' t A`: the run of $t$ steps from $s$ ends at $s'$. Moreover:
--        - the scratch tops (pointers 13, 14) do not grow;
--        - pointer registers below 40 other than 13 and 14, pointer 59 and real registers below 40 are kept;
--        - integer cells outside the new integer scratch and outside $A$ are kept, and so are real cells outside the new real scratch;
--        - every written cell lies in the new scratch or in $A$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). These are pieces of the BSP construction block of DetANN.HPIM.build_block, split out so that each proof fits the verifier's time limit. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMPreBlocks

/-!
# The BSP construction block

The program `bd` of `build_block` on the PNormReg machine: a worklist construction of
`build pts r c f lo hi`. A task is a pair (box address `p`, slot address `sl`); processing it stores the
root address of the subtree for the box `[lo, hi]` at `p` into the integer cell `sl`. Tasks wait on a
stack of 3-cell entries `[p, sl, link]` in integer scratch. Maxima and minima of two reals are computed
without branching, as `(a + b ± √((a - b)²)) / 2`.

Pointers: `40` the initial scratch top `Z0` (empty-stack sentinel), `42` stack pointer, `43` task box
`p`, `44` task slot, `45` point index, `46` coordinate index, `47` point address, `48` near box `q`,
`49` found flag, `50`, `51` source and index of the copy, `52` new node, `53` axis, `54` current box
of the carve, `55` current slot of the carve, `56` new box, `57` temporary, `58` return code of the
copy, `59` root slot, `60` `2m`, `61` leaf answer, `62` slot argument of a push, `68` `1`, `69` `0`.
Reals: `40` `r²`, `41` `(cr)²`, `42`, `43` the two squared distances, `44`–`48`, `54`, `55`
temporaries, `49` `2r`, `50` `0`, `51` `σ` of the tight box, `52` `σ` of the box, `53` `2`.
-/

namespace DetANN.HPIM.BD

open PNormReg

/-- Segment `init`: instructions 0–33. -/
def bd_init (off : ℕ) : Program :=
  [ .core (.pcopy 40 13),  -- 0
    .pointerAdd 60 1 1,  -- 1
    .core (.pset 69 (0)),  -- 2
    .core (.pset 68 (1)),  -- 3
    .core (.mul 40 11 11),  -- 4
    .core (.mul 47 12 11),  -- 5
    .core (.mul 41 47 47),  -- 6
    .core (.add 49 11 11),  -- 7
    .core (.const 50 (0 : ℝ)),  -- 8
    .core (.const 53 (2 : ℝ)),  -- 9
    .pointerSub 14 14 60,  -- 10
    .core (.pcopy 43 14),  -- 11
    .core (.pset 46 (0)),  -- 12
    .core (.pjle 60 46 (off + 20)),  -- 13 ICP
    .pointerAdd 50 17 46,  -- 14
    .core (.load 55 50),  -- 15
    .pointerAdd 50 43 46,  -- 16
    .core (.store 50 55),  -- 17
    .core (.pinc 46),  -- 18
    .core (.pjle 46 46 (off + 13)),  -- 19
    .core (.pdec 13),  -- 20 ICD
    .core (.pcopy 59 13),  -- 21
    .core (.pcopy 44 59),  -- 22
    .core (.pcopy 42 40),  -- 23
    .core (.pdec 13),  -- 24
    .core (.pdec 13),  -- 25
    .core (.pdec 13),  -- 26
    .integerStore 13 43,  -- 27
    .core (.pcopy 57 13),  -- 28
    .core (.pinc 57),  -- 29
    .integerStore 57 44,  -- 30
    .core (.pinc 57),  -- 31
    .integerStore 57 42,  -- 32
    .core (.pcopy 42 13) ]  -- 33

/-- Segment `disp`: instructions 34–52. -/
def bd_disp (off : ℕ) : Program :=
  [ .core (.pjle 40 42 (off + 395)),  -- 34 DISPATCH
    .integerLoad 43 42,  -- 35
    .core (.pcopy 57 42),  -- 36
    .core (.pinc 57),  -- 37
    .integerLoad 44 57,  -- 38
    .core (.pinc 57),  -- 39
    .integerLoad 42 57,  -- 40
    .pointerSub 14 14 60,  -- 41
    .core (.pcopy 48 14),  -- 42
    .core (.pset 49 (0)),  -- 43
    .core (.pset 45 (0)),  -- 44
    .core (.pjle 11 45 (off + 131)),  -- 45 SCAN
    .pointerAdd 57 10 45,  -- 46
    .integerLoad 57 57,  -- 47
    .pointerAdd 57 12 57,  -- 48
    .integerLoad 47 57,  -- 49
    .core (.const 42 (0 : ℝ)),  -- 50
    .core (.const 43 (0 : ℝ)),  -- 51
    .core (.pset 46 (0)) ]  -- 52

/-- Segment `dl`: instructions 53–85. -/
def bd_dl (off : ℕ) : Program :=
  [ .core (.pjle 1 46 (off + 86)),  -- 53 DL
    .pointerAdd 57 47 46,  -- 54
    .core (.load 44 57),  -- 55
    .pointerAdd 57 43 46,  -- 56
    .core (.load 45 57),  -- 57
    .pointerAdd 57 57 1,  -- 58
    .core (.load 46 57),  -- 59
    .core (.sub 47 44 46),  -- 60
    .core (.mul 54 47 47),  -- 61
    .sqrt 54 54,  -- 62
    .core (.add 47 47 54),  -- 63
    .core (.div 47 47 53),  -- 64
    .core (.sub 48 45 44),  -- 65
    .core (.sub 54 48 47),  -- 66
    .core (.mul 54 54 54),  -- 67
    .sqrt 54 54,  -- 68
    .core (.add 48 48 47),  -- 69
    .core (.add 48 48 54),  -- 70
    .core (.div 48 48 53),  -- 71
    .core (.mul 54 48 48),  -- 72
    .core (.add 42 42 54),  -- 73
    .core (.sub 47 44 45),  -- 74
    .core (.sub 48 46 44),  -- 75
    .core (.sub 54 47 48),  -- 76
    .core (.mul 54 54 54),  -- 77
    .sqrt 54 54,  -- 78
    .core (.add 47 47 48),  -- 79
    .core (.add 47 47 54),  -- 80
    .core (.div 47 47 53),  -- 81
    .core (.mul 54 47 47),  -- 82
    .core (.add 43 43 54),  -- 83
    .core (.pinc 46),  -- 84
    .core (.pjle 46 46 (off + 53)) ]  -- 85

/-- Segment `near`: instructions 86–115. -/
def bd_near (off : ℕ) : Program :=
  [ .core (.sub 54 42 40),  -- 86 DD
    .core (.jle 54 (off + 89)),  -- 87
    .core (.pjle 46 46 (off + 126)),  -- 88
    .core (.sub 54 43 41),  -- 89 NEAR
    .core (.jle 54 (off + 128)),  -- 90
    .core (.pset 46 (0)),  -- 91
    .core (.pjle 49 69 (off + 116)),  -- 92
    .core (.pjle 1 46 (off + 126)),  -- 93 UP
    .pointerAdd 57 47 46,  -- 94
    .core (.load 44 57),  -- 95
    .pointerAdd 57 48 46,  -- 96
    .core (.load 45 57),  -- 97
    .core (.sub 54 45 44),  -- 98
    .core (.mul 54 54 54),  -- 99
    .sqrt 54 54,  -- 100
    .core (.add 47 45 44),  -- 101
    .core (.sub 47 47 54),  -- 102
    .core (.div 47 47 53),  -- 103
    .core (.store 57 47),  -- 104
    .pointerAdd 57 57 1,  -- 105
    .core (.load 45 57),  -- 106
    .core (.sub 54 45 44),  -- 107
    .core (.mul 54 54 54),  -- 108
    .sqrt 54 54,  -- 109
    .core (.add 47 45 44),  -- 110
    .core (.add 47 47 54),  -- 111
    .core (.div 47 47 53),  -- 112
    .core (.store 57 47),  -- 113
    .core (.pinc 46),  -- 114
    .core (.pjle 46 46 (off + 93)) ]  -- 115

/-- Segment `fi`: instructions 116–133. -/
def bd_fi (off : ℕ) : Program :=
  [ .core (.pjle 1 46 (off + 125)),  -- 116 FI
    .pointerAdd 57 47 46,  -- 117
    .core (.load 44 57),  -- 118
    .pointerAdd 57 48 46,  -- 119
    .core (.store 57 44),  -- 120
    .pointerAdd 57 57 1,  -- 121
    .core (.store 57 44),  -- 122
    .core (.pinc 46),  -- 123
    .core (.pjle 46 46 (off + 116)),  -- 124
    .core (.pset 49 (1)),  -- 125 FID
    .core (.pinc 45),  -- 126 NEXT
    .core (.pjle 45 45 (off + 45)),  -- 127
    .core (.pcopy 61 45),  -- 128 GOOD
    .core (.pinc 61),  -- 129
    .core (.pjle 61 61 (off + 383)),  -- 130
    .core (.pset 61 (0)),  -- 131 SCD
    .core (.pjle 49 69 (off + 383)),  -- 132
    .core (.pset 46 (0)) ]  -- 133

/-- Segment `tb`: instructions 134–160. -/
def bd_tb (off : ℕ) : Program :=
  [ .core (.pjle 1 46 (off + 161)),  -- 134 TB
    .pointerAdd 57 48 46,  -- 135
    .core (.load 44 57),  -- 136
    .core (.sub 44 44 49),  -- 137
    .pointerAdd 50 43 46,  -- 138
    .core (.load 45 50),  -- 139
    .core (.sub 54 44 45),  -- 140
    .core (.mul 54 54 54),  -- 141
    .sqrt 54 54,  -- 142
    .core (.add 47 44 45),  -- 143
    .core (.add 47 47 54),  -- 144
    .core (.div 47 47 53),  -- 145
    .core (.store 57 47),  -- 146
    .pointerAdd 57 57 1,  -- 147
    .core (.load 44 57),  -- 148
    .core (.add 44 44 49),  -- 149
    .pointerAdd 50 50 1,  -- 150
    .core (.load 45 50),  -- 151
    .core (.sub 54 44 45),  -- 152
    .core (.mul 54 54 54),  -- 153
    .sqrt 54 54,  -- 154
    .core (.add 47 44 45),  -- 155
    .core (.sub 47 47 54),  -- 156
    .core (.div 47 47 53),  -- 157
    .core (.store 57 47),  -- 158
    .core (.pinc 46),  -- 159
    .core (.pjle 46 46 (off + 134)) ]  -- 160

/-- Segment `sg0`: instructions 161–171. -/
def bd_sg0 (off : ℕ) : Program :=
  [ .core (.pcopy 57 48),  -- 161 TBD
    .core (.load 44 57),  -- 162
    .pointerAdd 57 57 1,  -- 163
    .core (.load 45 57),  -- 164
    .core (.sub 51 45 44),  -- 165
    .core (.pcopy 57 43),  -- 166
    .core (.load 44 57),  -- 167
    .pointerAdd 57 57 1,  -- 168
    .core (.load 45 57),  -- 169
    .core (.sub 52 45 44),  -- 170
    .core (.pset 46 (1)) ]  -- 171

/-- Segment `sg`: instructions 172–196. -/
def bd_sg (off : ℕ) : Program :=
  [ .core (.pjle 1 46 (off + 197)),  -- 172 SG
    .pointerAdd 57 48 46,  -- 173
    .core (.load 44 57),  -- 174
    .pointerAdd 57 57 1,  -- 175
    .core (.load 45 57),  -- 176
    .core (.sub 47 45 44),  -- 177
    .core (.sub 54 51 47),  -- 178
    .core (.mul 54 54 54),  -- 179
    .sqrt 54 54,  -- 180
    .core (.add 51 51 47),  -- 181
    .core (.add 51 51 54),  -- 182
    .core (.div 51 51 53),  -- 183
    .pointerAdd 57 43 46,  -- 184
    .core (.load 44 57),  -- 185
    .pointerAdd 57 57 1,  -- 186
    .core (.load 45 57),  -- 187
    .core (.sub 47 45 44),  -- 188
    .core (.sub 54 52 47),  -- 189
    .core (.mul 54 54 54),  -- 190
    .sqrt 54 54,  -- 191
    .core (.add 52 52 47),  -- 192
    .core (.add 52 52 54),  -- 193
    .core (.div 52 52 53),  -- 194
    .core (.pinc 46),  -- 195
    .core (.pjle 46 46 (off + 172)) ]  -- 196

/-- Segment `split`: instructions 197–225. -/
def bd_split (off : ℕ) : Program :=
  [ .core (.add 54 51 51),  -- 197 SGD
    .core (.sub 54 54 52),  -- 198
    .core (.jle 54 (off + 280)),  -- 199
    .core (.pset 53 (0)),  -- 200
    .pointerAdd 57 43 53,  -- 201 LA
    .core (.load 44 57),  -- 202
    .pointerAdd 57 57 1,  -- 203
    .core (.load 45 57),  -- 204
    .core (.sub 47 45 44),  -- 205
    .core (.sub 54 52 47),  -- 206
    .core (.jle 54 (off + 210)),  -- 207
    .core (.pinc 53),  -- 208
    .core (.pjle 53 53 (off + 201)),  -- 209
    .core (.add 44 44 45),  -- 210 LAF
    .core (.div 44 44 53),  -- 211
    .core (.pdec 13),  -- 212
    .core (.pdec 13),  -- 213
    .core (.pdec 13),  -- 214
    .core (.pdec 13),  -- 215
    .core (.pcopy 52 13),  -- 216
    .integerStore 52 68,  -- 217
    .core (.pcopy 57 52),  -- 218
    .core (.pinc 57),  -- 219
    .integerStore 57 43,  -- 220
    .integerStore 44 52,  -- 221
    .core (.pcopy 50 43),  -- 222
    .pointerAdd 51 1 53,  -- 223
    .core (.pset 58 (0)),  -- 224
    .core (.pjle 58 58 (off + 258)) ]  -- 225

/-- Segment `split2`: instructions 226–257. -/
def bd_split2 (off : ℕ) : Program :=
  [ .core (.pcopy 62 52),  -- 226 R0
    .core (.pinc 62),  -- 227
    .core (.pinc 62),  -- 228
    .core (.pdec 13),  -- 229
    .core (.pdec 13),  -- 230
    .core (.pdec 13),  -- 231
    .integerStore 13 56,  -- 232
    .core (.pcopy 57 13),  -- 233
    .core (.pinc 57),  -- 234
    .integerStore 57 62,  -- 235
    .core (.pinc 57),  -- 236
    .integerStore 57 42,  -- 237
    .core (.pcopy 42 13),  -- 238
    .core (.pcopy 50 43),  -- 239
    .core (.pcopy 51 53),  -- 240
    .core (.pset 58 (1)),  -- 241
    .core (.pjle 58 58 (off + 258)),  -- 242
    .core (.pcopy 62 52),  -- 243 R1
    .core (.pinc 62),  -- 244
    .core (.pinc 62),  -- 245
    .core (.pinc 62),  -- 246
    .core (.pdec 13),  -- 247
    .core (.pdec 13),  -- 248
    .core (.pdec 13),  -- 249
    .integerStore 13 56,  -- 250
    .core (.pcopy 57 13),  -- 251
    .core (.pinc 57),  -- 252
    .integerStore 57 62,  -- 253
    .core (.pinc 57),  -- 254
    .integerStore 57 42,  -- 255
    .core (.pcopy 42 13),  -- 256
    .core (.pjle 42 42 (off + 34)) ]  -- 257

/-- Segment `cs`: instructions 258–279. -/
def bd_cs (off : ℕ) : Program :=
  [ .pointerSub 14 14 60,  -- 258 CS
    .core (.pcopy 56 14),  -- 259
    .core (.pset 46 (0)),  -- 260
    .core (.pjle 60 46 (off + 268)),  -- 261 CL
    .pointerAdd 57 50 46,  -- 262
    .core (.load 55 57),  -- 263
    .pointerAdd 57 56 46,  -- 264
    .core (.store 57 55),  -- 265
    .core (.pinc 46),  -- 266
    .core (.pjle 46 46 (off + 261)),  -- 267
    .pointerAdd 57 56 51,  -- 268 CD
    .core (.store 57 44),  -- 269
    .core (.pjle 58 69 (off + 226)),  -- 270
    .core (.pset 57 (1)),  -- 271
    .core (.pjle 58 57 (off + 243)),  -- 272
    .core (.pset 57 (2)),  -- 273
    .core (.pjle 58 57 (off + 304)),  -- 274
    .core (.pset 57 (3)),  -- 275
    .core (.pjle 58 57 (off + 321)),  -- 276
    .core (.pset 57 (4)),  -- 277
    .core (.pjle 58 57 (off + 348)),  -- 278
    .core (.pjle 58 58 (off + 366)) ]  -- 279

/-- Segment `cv`: instructions 280–303. -/
def bd_cv (off : ℕ) : Program :=
  [ .core (.pcopy 54 43),  -- 280 CARVE
    .core (.pcopy 55 44),  -- 281
    .core (.pset 53 (0)),  -- 282
    .core (.pjle 1 53 (off + 372)),  -- 283 CK
    .pointerAdd 57 48 53,  -- 284
    .core (.load 44 57),  -- 285
    .pointerAdd 57 54 53,  -- 286
    .core (.load 45 57),  -- 287
    .core (.sub 54 44 45),  -- 288
    .core (.jle 54 (off + 326)),  -- 289
    .core (.pdec 13),  -- 290
    .core (.pdec 13),  -- 291
    .core (.pdec 13),  -- 292
    .core (.pdec 13),  -- 293
    .core (.pcopy 52 13),  -- 294
    .integerStore 52 68,  -- 295
    .core (.pcopy 57 52),  -- 296
    .core (.pinc 57),  -- 297
    .integerStore 57 54,  -- 298
    .integerStore 55 52,  -- 299
    .core (.pcopy 50 54),  -- 300
    .pointerAdd 51 1 53,  -- 301
    .core (.pset 58 (2)),  -- 302
    .core (.pjle 58 58 (off + 258)) ]  -- 303

/-- Segment `cv2`: instructions 304–325. -/
def bd_cv2 (off : ℕ) : Program :=
  [ .core (.pcopy 62 52),  -- 304 R2
    .core (.pinc 62),  -- 305
    .core (.pinc 62),  -- 306
    .core (.pdec 13),  -- 307
    .core (.pdec 13),  -- 308
    .core (.pdec 13),  -- 309
    .integerStore 13 56,  -- 310
    .core (.pcopy 57 13),  -- 311
    .core (.pinc 57),  -- 312
    .integerStore 57 62,  -- 313
    .core (.pinc 57),  -- 314
    .integerStore 57 42,  -- 315
    .core (.pcopy 42 13),  -- 316
    .core (.pcopy 50 54),  -- 317
    .core (.pcopy 51 53),  -- 318
    .core (.pset 58 (3)),  -- 319
    .core (.pjle 58 58 (off + 258)),  -- 320
    .core (.pcopy 54 56),  -- 321 R3
    .core (.pcopy 55 52),  -- 322
    .core (.pinc 55),  -- 323
    .core (.pinc 55),  -- 324
    .core (.pinc 55) ]  -- 325

/-- Segment `cv3`: instructions 326–347. -/
def bd_cv3 (off : ℕ) : Program :=
  [ .pointerAdd 57 48 53,  -- 326 CH
    .pointerAdd 57 57 1,  -- 327
    .core (.load 44 57),  -- 328
    .pointerAdd 57 54 53,  -- 329
    .pointerAdd 57 57 1,  -- 330
    .core (.load 46 57),  -- 331
    .core (.sub 54 46 44),  -- 332
    .core (.jle 54 (off + 370)),  -- 333
    .core (.pdec 13),  -- 334
    .core (.pdec 13),  -- 335
    .core (.pdec 13),  -- 336
    .core (.pdec 13),  -- 337
    .core (.pcopy 52 13),  -- 338
    .integerStore 52 68,  -- 339
    .core (.pcopy 57 52),  -- 340
    .core (.pinc 57),  -- 341
    .integerStore 57 54,  -- 342
    .integerStore 55 52,  -- 343
    .core (.pcopy 50 54),  -- 344
    .core (.pcopy 51 53),  -- 345
    .core (.pset 58 (4)),  -- 346
    .core (.pjle 58 58 (off + 258)) ]  -- 347

/-- Segment `cv4`: instructions 348–371. -/
def bd_cv4 (off : ℕ) : Program :=
  [ .core (.pcopy 62 52),  -- 348 R4
    .core (.pinc 62),  -- 349
    .core (.pinc 62),  -- 350
    .core (.pinc 62),  -- 351
    .core (.pdec 13),  -- 352
    .core (.pdec 13),  -- 353
    .core (.pdec 13),  -- 354
    .integerStore 13 56,  -- 355
    .core (.pcopy 57 13),  -- 356
    .core (.pinc 57),  -- 357
    .integerStore 57 62,  -- 358
    .core (.pinc 57),  -- 359
    .integerStore 57 42,  -- 360
    .core (.pcopy 42 13),  -- 361
    .core (.pcopy 50 54),  -- 362
    .pointerAdd 51 1 53,  -- 363
    .core (.pset 58 (5)),  -- 364
    .core (.pjle 58 58 (off + 258)),  -- 365
    .core (.pcopy 54 56),  -- 366 R5
    .core (.pcopy 55 52),  -- 367
    .core (.pinc 55),  -- 368
    .core (.pinc 55),  -- 369
    .core (.pinc 53),  -- 370 CN
    .core (.pjle 53 53 (off + 283)) ]  -- 371

/-- Segment `ce`: instructions 372–382. -/
def bd_ce (off : ℕ) : Program :=
  [ .core (.pdec 13),  -- 372 CE
    .core (.pdec 13),  -- 373
    .core (.pdec 13),  -- 374
    .integerStore 13 54,  -- 375
    .core (.pcopy 57 13),  -- 376
    .core (.pinc 57),  -- 377
    .integerStore 57 55,  -- 378
    .core (.pinc 57),  -- 379
    .integerStore 57 42,  -- 380
    .core (.pcopy 42 13),  -- 381
    .core (.pjle 42 42 (off + 34)) ]  -- 382

/-- Segment `leaf`: instructions 383–395. -/
def bd_leaf (off : ℕ) : Program :=
  [ .core (.pdec 13),  -- 383 LEAF
    .core (.pdec 13),  -- 384
    .core (.pdec 13),  -- 385
    .core (.pcopy 52 13),  -- 386
    .integerStore 52 69,  -- 387
    .core (.pcopy 57 52),  -- 388
    .core (.pinc 57),  -- 389
    .integerStore 57 43,  -- 390
    .core (.pinc 57),  -- 391
    .integerStore 57 61,  -- 392
    .integerStore 44 52,  -- 393
    .core (.pjle 42 42 (off + 34)),  -- 394
    .integerLoad 17 59 ]  -- 395 END

/-- Labels: `ICP` 13, `ICD` 20, `DISPATCH` 34, `SCAN` 45, `DL` 53, `DD` 86, `NEAR` 89, `UP` 93, `FI` 116, `FID` 125, `NEXT` 126, `GOOD` 128, `SCD` 131, `TB` 134, `TBD` 161, `SG` 172, `SGD` 197, `LA` 201, `LAF` 210, `R0` 226, `R1` 243, `CS` 258, `CL` 261, `CD` 268, `CARVE` 280, `CK` 283, `R2` 304, `R3` 321, `CH` 326, `R4` 348, `R5` 366, `CN` 370, `CE` 372, `LEAF` 383, `END` 395. -/
def bd (off : ℕ) : Program :=
  bd_init off ++ (bd_disp off ++ (bd_dl off ++ (bd_near off ++ (bd_fi off ++ (bd_tb off ++ (bd_sg0 off ++ (bd_sg off ++ (bd_split off ++ (bd_split2 off ++ (bd_cs off ++ (bd_cv off ++ (bd_cv2 off ++ (bd_cv3 off ++ (bd_cv4 off ++ (bd_ce off ++ (bd_leaf off))))))))))))))))

/-! ## Predicates of the correctness proof

These name the facts that the published step and part lemmas of the block state about machine states. -/

section Aux

open PNormRegLib DetANN DetANN.HPIM

variable {m n : ℕ}

/-- The box `[lo, hi]` is stored at `p`: `lo` at `p + j`, `hi` at `p + j + m`. -/
def BoxAt (s : State) (p : ℤ) (lo hi : Fin m → ℝ) : Prop :=
  ∀ j : Fin m, s.core.mem (p + j) = lo j ∧ s.core.mem (p + j + m) = hi j

/-- The `j`-th terms of the two squared box distances of a point. -/
noncomputable def t1 (lo hi pt : Fin m → ℝ) (j : Fin m) : ℝ := (max (lo j - pt j) (max 0 (pt j - hi j))) ^ 2

/-- See `t1`. -/
noncomputable def t2 (lo hi pt : Fin m → ℝ) (j : Fin m) : ℝ := (max (pt j - lo j) (hi j - pt j)) ^ 2

/-- `∑_{j < k} g j`. -/
noncomputable def psum (g : Fin m → ℝ) (k : ℕ) : ℝ := ∑ j : Fin m, if (j : ℕ) < k then g j else 0

/-- `max_{j ≤ k} g j`. -/
noncomputable def rmax (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => g 0
  | k + 1 => max (rmax g k) (g (k + 1))

/-- The sides of a box, indexed by `ℕ` (`0` past `m`). -/
noncomputable def side (lo hi : Fin m → ℝ) (j : ℕ) : ℝ := if h : j < m then hi ⟨j, h⟩ - lo ⟨j, h⟩ else 0

/-- The constant registers and the point table. -/
def Env (s : State) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 : ℤ) : Prop :=
  LocalPts s pts ∧ s.core.regs 11 = r ∧ s.core.regs 12 = c ∧ s.core.ptrs 40 = Z0 ∧
    s.core.ptrs 60 = 2 * m ∧ s.core.ptrs 68 = 1 ∧ s.core.ptrs 69 = 0 ∧
    s.core.regs 40 = r * r ∧ s.core.regs 41 = (c * r) * (c * r) ∧ s.core.regs 49 = r + r ∧
    s.core.regs 50 = 0 ∧ s.core.regs 53 = 2

/-- The frame of a run from `s` to `s'` in `t` steps: fresh scratch below the old tops, other integer
writes only to cells in `A` (the slots). -/
def Fr (Q : Program) (s s' : State) (t : ℕ) (A : ℤ → Prop) : Prop :=
  run Q s detTape t = s' ∧ s'.work = s.work + t ∧
    s'.core.ptrs 13 ≤ s.core.ptrs 13 ∧ s'.core.ptrs 14 ≤ s.core.ptrs 14 ∧
    (∀ x, x < 40 → x ≠ 13 → x ≠ 14 → s'.core.ptrs x = s.core.ptrs x) ∧ s'.core.ptrs 59 = s.core.ptrs 59 ∧
    (∀ x, x < 40 → s'.core.regs x = s.core.regs x) ∧
    (∀ z, (z < s'.core.ptrs 13 ∨ s.core.ptrs 13 ≤ z) → ¬ A z → s'.integerMemory z = s.integerMemory z) ∧
    (∀ z, (z < s'.core.ptrs 14 ∨ s.core.ptrs 14 ≤ z) → s'.core.mem z = s.core.mem z) ∧
    ∀ w ∈ cellsWritten Q s t,
      (w.1 = false ∧ ((s'.core.ptrs 13 ≤ w.2 ∧ w.2 < s.core.ptrs 13) ∨ A w.2)) ∨
      (w.1 = true ∧ s'.core.ptrs 14 ≤ w.2 ∧ w.2 < s.core.ptrs 14)

end Aux

end DetANN.HPIM.BD


