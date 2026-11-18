-- Prove2me | Definitions.Def_DetANN_HPIMBalProg
-- name    : DetANN_HPIMBalProg
-- status  : Definition
-- author  : @milia
-- created : 2026-11-17T14:17:28.505204+00:00
-- url     : https://prove2.me/theorems/40f6961b-f827-4de8-a77b-ed7bcb7322d8
-- title:
--   The balancing block program
-- statement:
--   The program of the balancing block of `balance_block`, on the PNormReg machine (definition `PNormReg_Machine`), and two helpers used to state its correctness in pieces.
--
--   1. **The program** $\mathrm{bb}(o)$ has 254 instructions, with absolute jump targets $o+\ell$. It is written as $\mathrm{bb}_0\mathbin{+\!\!+}(\mathrm{bb}_1\mathbin{+\!\!+}(\mathrm{bb}_2\mathbin{+\!\!+}\mathrm{bb}_3))$ (instructions 0–63, 64–127, 128–191, 192–253). It runs in four phases:
--      - **walk** (0–48): a preorder walk of the stored BSP tree from pointer 17. Record $k$ gets the kind and the address of the $k$-th node; the pending right children form a linked list through field 4.
--      - **sizes** (49–86): a backward pass that computes subtree sizes, $\mathrm{size}_k=1$ at a leaf and $1+\mathrm{size}_{k+1}+\mathrm{size}_{k+1+\mathrm{size}_{k+1}}$ at a cut, and clears the marks.
--      - **recursion** (87–253): the centroid recursion `CALL`/`RET` with an explicit stack of 4-cell frames (index $j$, centroid, output node, fuel). Each call counts the unmarked components backwards over the subtree interval of $j$ (field 4), returns a leaf when at most one remains or the fuel is 0, and otherwise scans for the first index minimising $\max(c_k,\mathrm{tot}-c_k)$. It then writes a test node with the centroid's box (copied to the real heap), recurses on the centroid's subtree, marks it, and recurses on the rest.
--      - **end** (254): exit.
--   2. **Records.** With $A$ the value of pointer 13, record $k$ lives in integer scratch below $A$, field $f$ at $\mathrm{fa}(A,f,k)=A-5+f-5k$: $0$ kind, $1$ node address, $2$ subtree size, $3$ mark, $4$ component count (DFS link while walking). The frames grow down from $A-5N$.
--   3. **`Consts s A`** says that the constant pointer registers hold $13\mapsto A$, $60\ldots64\mapsto A-5,\ldots,A-1$, $69\mapsto0$ and $70\mapsto-1$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). These are the straight-line pieces of the balancing block of DetANN.HPIM.balance_block, split out so that each proof fits the verifier's time limit. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine

/-! The balancing block: preorder records of the stored BSP, subtree sizes, and the centroid
recursion with a mark array and an explicit frame stack.

Records (integer scratch below `A` = pointer `13`): record `k` holds at `A − 5 + f − 5k` the field
`f`: `0` kind (`I[node]`), `1` node address, `2` subtree size, `3` mark, `4` component count (the
link of the DFS stack while walking). Frames of 4 cells (`j`, centroid, output node, fuel) grow
down from `A − 5N`.

Pointers: `41` `N`, `42` cur, `43` DFS top, `44`, `45` temporaries, `46` loop index, `47` frame
pointer, `48` frame base, `49` fuel, `50` `j`, `51` size, `52` total, `53` best, `54` best score,
`55` output node, `56`–`58` temporaries, `60`–`64` field bases `A − 5 + f`, `67`, `72`, `73`
5×index, `68` record index, `69` zero, `70` `−1`, `71` link, `74` end. Real `40` temporary. -/

namespace DetANN.HPIM.BB

open PNormReg

/-- Instructions 0–63. -/
def bb0 (off : ℕ) : Program :=
  [ .core (.pset 69 (0)),  -- 0
    .core (.pset 70 (-1)),  -- 1
    .core (.pset 56 (5)),  -- 2
    .pointerSub 60 13 56,  -- 3
    .core (.pcopy 61 60),  -- 4
    .core (.pinc 61),  -- 5
    .core (.pcopy 62 61),  -- 6
    .core (.pinc 62),  -- 7
    .core (.pcopy 63 62),  -- 8
    .core (.pinc 63),  -- 9
    .core (.pcopy 64 63),  -- 10
    .core (.pinc 64),  -- 11
    .core (.pset 41 (0)),  -- 12
    .core (.pcopy 42 17),  -- 13
    .core (.pset 43 (-1)),  -- 14
    .pointerAdd 67 41 41,  -- 15 VISIT
    .pointerAdd 67 67 67,  -- 16
    .pointerAdd 67 67 41,  -- 17
    .pointerSub 44 61 67,  -- 18
    .integerStore 44 42,  -- 19
    .integerLoad 45 42,  -- 20
    .pointerSub 44 60 67,  -- 21
    .integerStore 44 45,  -- 22
    .core (.pcopy 68 41),  -- 23
    .core (.pinc 41),  -- 24
    .core (.pjle 45 69 (off + 34)),  -- 25
    .pointerSub 44 64 67,  -- 26
    .integerStore 44 43,  -- 27
    .core (.pcopy 43 68),  -- 28
    .core (.pcopy 44 42),  -- 29
    .core (.pinc 44),  -- 30
    .core (.pinc 44),  -- 31
    .integerLoad 42 44,  -- 32
    .core (.pjle 41 41 (off + 15)),  -- 33
    .core (.pjle 43 70 (off + 48)),  -- 34 POP
    .pointerAdd 67 43 43,  -- 35
    .pointerAdd 67 67 67,  -- 36
    .pointerAdd 67 67 43,  -- 37
    .pointerSub 44 64 67,  -- 38
    .integerLoad 71 44,  -- 39
    .pointerSub 44 61 67,  -- 40
    .integerLoad 44 44,  -- 41
    .core (.pinc 44),  -- 42
    .core (.pinc 44),  -- 43
    .core (.pinc 44),  -- 44
    .integerLoad 42 44,  -- 45
    .core (.pcopy 43 71),  -- 46
    .core (.pjle 41 41 (off + 15)),  -- 47
    .core (.pcopy 46 41),  -- 48 DFSDONE
    .core (.pjle 46 69 (off + 78)),  -- 49 SZ
    .core (.pdec 46),  -- 50
    .pointerAdd 67 46 46,  -- 51
    .pointerAdd 67 67 67,  -- 52
    .pointerAdd 67 67 46,  -- 53
    .pointerSub 44 63 67,  -- 54
    .integerStore 44 69,  -- 55
    .pointerSub 44 60 67,  -- 56
    .integerLoad 45 44,  -- 57
    .core (.pset 56 (1)),  -- 58
    .core (.pjle 45 69 (off + 75)),  -- 59
    .core (.pcopy 57 46),  -- 60
    .core (.pinc 57),  -- 61
    .pointerAdd 72 57 57,  -- 62
    .pointerAdd 72 72 72 ]  -- 63

/-- Instructions 64–127. -/
def bb1 (off : ℕ) : Program :=
  [ .pointerAdd 72 72 57,  -- 64
    .pointerSub 44 62 72,  -- 65
    .integerLoad 58 44,  -- 66
    .pointerAdd 56 56 58,  -- 67
    .pointerAdd 57 57 58,  -- 68
    .pointerAdd 72 57 57,  -- 69
    .pointerAdd 72 72 72,  -- 70
    .pointerAdd 72 72 57,  -- 71
    .pointerSub 44 62 72,  -- 72
    .integerLoad 58 44,  -- 73
    .pointerAdd 56 56 58,  -- 74
    .pointerSub 44 62 67,  -- 75 SZW
    .integerStore 44 56,  -- 76
    .core (.pjle 46 46 (off + 49)),  -- 77
    .pointerAdd 67 41 41,  -- 78 SZDONE
    .pointerAdd 67 67 67,  -- 79
    .pointerAdd 67 67 41,  -- 80
    .pointerSub 48 13 67,  -- 81
    .core (.pcopy 47 48),  -- 82
    .core (.pcopy 49 41),  -- 83
    .core (.pinc 49),  -- 84
    .core (.pset 50 (0)),  -- 85
    .core (.pcopy 17 15),  -- 86
    .core (.pjle 49 69 (off + 216)),  -- 87 CALL
    .pointerAdd 67 50 50,  -- 88
    .pointerAdd 67 67 67,  -- 89
    .pointerAdd 67 67 50,  -- 90
    .pointerSub 44 62 67,  -- 91
    .integerLoad 51 44,  -- 92
    .pointerAdd 46 50 51,  -- 93
    .core (.pjle 46 50 (off + 127)),  -- 94 CNT
    .core (.pdec 46),  -- 95
    .pointerAdd 72 46 46,  -- 96
    .pointerAdd 72 72 72,  -- 97
    .pointerAdd 72 72 46,  -- 98
    .pointerSub 44 63 72,  -- 99
    .integerLoad 45 44,  -- 100
    .core (.pset 56 (1)),  -- 101
    .pointerSub 56 56 45,  -- 102  e := 1 − mark
    .core (.pcopy 56 56),  -- 103  (no-op)
    .pointerSub 44 60 72,  -- 104 CN1
    .integerLoad 45 44,  -- 105
    .core (.pjle 45 69 (off + 124)),  -- 106
    .core (.pcopy 57 46),  -- 107
    .core (.pinc 57),  -- 108
    .pointerAdd 73 57 57,  -- 109
    .pointerAdd 73 73 73,  -- 110
    .pointerAdd 73 73 57,  -- 111
    .pointerSub 44 64 73,  -- 112
    .integerLoad 58 44,  -- 113
    .pointerAdd 56 56 58,  -- 114
    .pointerSub 44 62 73,  -- 115
    .integerLoad 58 44,  -- 116
    .pointerAdd 57 57 58,  -- 117
    .pointerAdd 73 57 57,  -- 118
    .pointerAdd 73 73 73,  -- 119
    .pointerAdd 73 73 57,  -- 120
    .pointerSub 44 64 73,  -- 121
    .integerLoad 58 44,  -- 122
    .pointerAdd 56 56 58,  -- 123
    .pointerSub 44 64 72,  -- 124 CNW
    .integerStore 44 56,  -- 125
    .core (.pjle 46 46 (off + 94)),  -- 126
    .pointerSub 44 64 67 ]  -- 127 CNTDONE

/-- Instructions 128–191. -/
def bb2 (off : ℕ) : Program :=
  [ .integerLoad 52 44,  -- 128
    .core (.pset 56 (1)),  -- 129
    .core (.pjle 52 56 (off + 199)),  -- 130
    .core (.pcopy 54 52),  -- 131
    .core (.pinc 54),  -- 132
    .core (.pcopy 46 50),  -- 133
    .pointerAdd 74 50 51,  -- 134
    .core (.pinc 46),  -- 135 SCAN
    .core (.pjle 74 46 (off + 153)),  -- 136
    .pointerAdd 72 46 46,  -- 137
    .pointerAdd 72 72 72,  -- 138
    .pointerAdd 72 72 46,  -- 139
    .pointerSub 44 63 72,  -- 140
    .integerLoad 45 44,  -- 141
    .core (.pjle 45 69 (off + 144)),  -- 142
    .core (.pjle 46 46 (off + 135)),  -- 143
    .pointerSub 44 64 72,  -- 144 SC1
    .integerLoad 56 44,  -- 145
    .pointerSub 57 52 56,  -- 146
    .core (.pjle 57 56 (off + 149)),  -- 147
    .core (.pcopy 56 57),  -- 148
    .core (.pjle 54 56 (off + 135)),  -- 149 SC2
    .core (.pcopy 54 56),  -- 150
    .core (.pcopy 53 46),  -- 151
    .core (.pjle 46 46 (off + 135)),  -- 152
    .core (.pcopy 55 15),  -- 153 SCANDONE
    .core (.pset 56 (1)),  -- 154
    .integerStore 15 56,  -- 155
    .core (.pcopy 44 15),  -- 156
    .core (.pinc 44),  -- 157
    .integerStore 44 16,  -- 158
    .core (.pinc 44),  -- 159
    .core (.pcopy 57 15),  -- 160
    .core (.pinc 57),  -- 161
    .core (.pinc 57),  -- 162
    .core (.pinc 57),  -- 163
    .core (.pinc 57),  -- 164
    .integerStore 44 57,  -- 165
    .core (.pcopy 15 57),  -- 166
    .pointerAdd 72 53 53,  -- 167
    .pointerAdd 72 72 72,  -- 168
    .pointerAdd 72 72 53,  -- 169
    .pointerSub 44 61 72,  -- 170
    .integerLoad 44 44,  -- 171
    .core (.pinc 44),  -- 172
    .integerLoad 44 44,  -- 173
    .pointerAdd 57 1 1,  -- 174
    .core (.pset 46 (0)),  -- 175
    .core (.pjle 57 46 (off + 183)),  -- 176 COPY
    .pointerAdd 58 44 46,  -- 177
    .core (.load 40 58),  -- 178
    .pointerAdd 58 16 46,  -- 179
    .core (.store 58 40),  -- 180
    .core (.pinc 46),  -- 181
    .core (.pjle 46 46 (off + 176)),  -- 182
    .pointerAdd 16 16 57,  -- 183 COPYDONE
    .core (.pdec 47),  -- 184
    .core (.pdec 47),  -- 185
    .core (.pdec 47),  -- 186
    .core (.pdec 47),  -- 187
    .integerStore 47 50,  -- 188
    .core (.pcopy 44 47),  -- 189
    .core (.pinc 44),  -- 190
    .integerStore 44 53 ]  -- 191

/-- Instructions 192–253. -/
def bb3 (off : ℕ) : Program :=
  [ .core (.pinc 44),  -- 192
    .integerStore 44 55,  -- 193
    .core (.pinc 44),  -- 194
    .integerStore 44 49,  -- 195
    .core (.pdec 49),  -- 196
    .core (.pcopy 50 53),  -- 197
    .core (.pjle 49 49 (off + 87)),  -- 198
    .pointerSub 44 60 67,  -- 199 LEAFOUT
    .integerLoad 45 44,  -- 200
    .core (.pset 56 (0)),  -- 201
    .core (.pjle 45 69 (off + 204)),  -- 202
    .core (.pjle 45 45 (off + 209)),  -- 203
    .pointerSub 44 61 67,  -- 204 LF1
    .integerLoad 44 44,  -- 205
    .core (.pinc 44),  -- 206
    .core (.pinc 44),  -- 207
    .integerLoad 56 44,  -- 208
    .integerStore 15 69,  -- 209 LFW
    .core (.pcopy 44 15),  -- 210
    .core (.pinc 44),  -- 211
    .integerStore 44 56,  -- 212
    .core (.pinc 15),  -- 213
    .core (.pinc 15),  -- 214
    .core (.pjle 15 15 (off + 218)),  -- 215
    .core (.pset 56 (0)),  -- 216 FUEL0
    .core (.pjle 56 56 (off + 209)),  -- 217
    .core (.pjle 48 47 (off + 254)),  -- 218 RET
    .integerLoad 50 47,  -- 219
    .core (.pcopy 44 47),  -- 220
    .core (.pinc 44),  -- 221
    .integerLoad 53 44,  -- 222
    .core (.pinc 44),  -- 223
    .integerLoad 55 44,  -- 224
    .core (.pinc 44),  -- 225
    .integerLoad 49 44,  -- 226
    .core (.pinc 47),  -- 227
    .core (.pinc 47),  -- 228
    .core (.pinc 47),  -- 229
    .core (.pinc 47),  -- 230
    .core (.pcopy 44 55),  -- 231
    .core (.pinc 44),  -- 232
    .core (.pinc 44),  -- 233
    .core (.pinc 44),  -- 234
    .integerStore 44 15,  -- 235
    .pointerAdd 72 53 53,  -- 236
    .pointerAdd 72 72 72,  -- 237
    .pointerAdd 72 72 53,  -- 238
    .pointerSub 44 62 72,  -- 239
    .integerLoad 51 44,  -- 240
    .pointerAdd 74 53 51,  -- 241
    .core (.pcopy 46 53),  -- 242
    .core (.pset 56 (1)),  -- 243
    .core (.pjle 74 46 (off + 252)),  -- 244 MK
    .pointerAdd 72 46 46,  -- 245
    .pointerAdd 72 72 72,  -- 246
    .pointerAdd 72 72 46,  -- 247
    .pointerSub 44 63 72,  -- 248
    .integerStore 44 56,  -- 249
    .core (.pinc 46),  -- 250
    .core (.pjle 46 46 (off + 244)),  -- 251
    .core (.pdec 49),  -- 252 MKDONE
    .core (.pjle 49 49 (off + 87)) ]  -- 253

/-- The balancing block at offset `off` (254 instructions). -/
def bb (off : ℕ) : Program := bb0 off ++ (bb1 off ++ (bb2 off ++ bb3 off))

/-- Field `f` of record `k`. -/
def fa (A f : ℤ) (k : ℕ) : ℤ := A - 5 + f - 5 * (k : ℤ)

/-- The constant registers. -/
def Consts (s : State) (A : ℤ) : Prop :=
  s.core.ptrs 13 = A ∧ s.core.ptrs 60 = A - 5 ∧ s.core.ptrs 61 = A - 4 ∧ s.core.ptrs 62 = A - 3 ∧
    s.core.ptrs 63 = A - 2 ∧ s.core.ptrs 64 = A - 1 ∧ s.core.ptrs 69 = 0 ∧ s.core.ptrs 70 = -1

end DetANN.HPIM.BB


