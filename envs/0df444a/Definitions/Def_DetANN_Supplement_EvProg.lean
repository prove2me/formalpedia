-- Prove2me | Definitions.Def_DetANN_Supplement_EvProg
-- name    : DetANN_Supplement_EvProg
-- status  : Definition
-- author  : @milia
-- created : 2026-11-20T23:50:06.047081+00:00
-- url     : https://prove2.me/theorems/038deab0-52d5-47b5-b2e2-4d08875576b6
-- title:
--   The block evaluation program and the FWHT block
-- statement:
--   Two programs of the real RAM `PNormReg_Machine`, with absolute jump targets $o+\ell$ for an offset $o$. They are the evaluation half of Theorem 3.2 (§6.1, p.14): after preprocessing has chosen the signs $\xi$, they compute all blocks
--   $$(A_j z)_\ell=(Ld)^{-1/2}\sum_{r<d}h_{jr}\,\xi^{(\ell)}_r\,z_r\qquad(j<d,\ \ell<L)$$
--   for the Sylvester–Hadamard matrix $h$ of order $d=2^k$ (definition `DetANN_Sylvester`).
--
--   1. **The FWHT block** $\mathrm{fw}(o)$ (23 instructions) is the in-place fast Walsh–Hadamard transform of the $2^{c}$ reals starting at the real address in pointer 13, where $c$ is pointer 4 and $d=2^c$ is pointer 3. For $t=c-1,\dots,0$ it reads the stride $h=2^t$ from integer cell $2+t$, and for every block start $s\in\{0,2h,4h,\dots\}$ below $d$ and every $i<h$ it replaces the pair $(x,y)$ at offsets $s+i$, $s+i+h$ by $(x+y,\,x-y)$. It exits at $o+23$.
--   2. **The evaluation program** $\mathrm{ev}(o)=\mathrm{evA}(o)\mathbin{+\!\!+}\mathrm{fw}(o+43)\mathbin{+\!\!+}\mathrm{evB}(o)$ (80 instructions):
--      - It reads $L$ from integer cell 0 and $d=2^k$ from integer cell 1, writes the strides $2^u$ ($u<k$) to integer cells $2,3,\dots$, and computes $(Ld)^{-1/2}$ with one `sqrt`.
--      - For each $\ell<L$ it writes $\sigma_{\ell d+r}\,z_r$ to the scratch block starting at real cell $Ld$, where the sign $\sigma_{\ell d+r}$ is the real cell $-d-1-(\ell d+r)$ and the query $z_r$ is the cell $-1-r$. It then transforms the block with the FWHT block and writes $(Ld)^{-1/2}$ times entry $j$ to real cell $j\cdot L+\ell$.
--      - Then it halts.
--
--   Register map: pointers 0 (zero), 1, 2 (the constants 1, 2), 3 ($d$), 4 ($k$), 5–12 (FWHT scratch), 13 (scratch base), 14 ($L$), 15 ($-d-1$), 16 ($\ell$), 17 ($\ell d$), 18–21 (loop scratch); reals 0–3 (FWHT scratch), 4 ($(Ld)^{-1/2}$).
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a proof of DetANN.Supplement.theorem_3_2 (Feng, Indyk, STOC 2027 submission, Theorem 3.2, p.7; the blocks of §6.1, p.14). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure; the fast Walsh–Hadamard transform is the standard in-place butterfly algorithm.

import Mathlib
import Definitions.Def_PNormReg_Machine

/-!
# Milestone 21 (`DetANN.Supplement.theorem_3_2`): the evaluation program `Ev` and the FWHT block

`fw off` is the in-place fast Walsh–Hadamard transform of the `2^cnt` reals starting at the real
address in pointer `13`, with the strides `2^0, …, 2^(cnt-1)` read from the integer cells `2, 3, …`
and used in descending order. `ev off` reads `L` (integer cell `0`) and `d = 2^k` (integer cell `1`),
and for every `ℓ < L` transforms `(S[ℓd + r] · z_r)_r` (signs at real cells `−1 − d − (ℓd + r)`, query
at `−1 − r`) and writes `(Ld)^{−1/2}` times entry `j` to real cell `j·L + ℓ`; then it halts.

Pointers: `0` zero, `1` one, `2` two, `3` d, `4` cnt, `5` t, `6` ta, `7` h, `8` h2, `9` s, `10` i, `11` a, `12` b, `13` fb, `14` L, `15` Sb, `16` l, `17` ib, `18` r, `19` idx, `20` j, `21` o. Reals: `0` x, `1` y, `2` u, `3` w, `4` sc.
-/

namespace DetANN.Supplement.Thm32

open PNormReg

/-- The FWHT block (relative labels: `L` 1, `S` 7, `I` 9, `SN` 21, `D` 23). -/
def fw (off : ℕ) : Program :=
  [ .core (.pcopy 5 4),  -- 0
    .core (.pjle 5 0 (off + 23)),  -- 1 L
    .core (.pdec 5),  -- 2
    .pointerAdd 6 2 5,  -- 3
    .integerLoad 7 6,  -- 4
    .pointerAdd 8 7 7,  -- 5
    .core (.pset 9 (0)),  -- 6
    .core (.pjle 3 9 (off + 1)),  -- 7 S
    .core (.pset 10 (0)),  -- 8
    .core (.pjle 7 10 (off + 21)),  -- 9 I
    .pointerAdd 11 13 9,  -- 10
    .pointerAdd 11 11 10,  -- 11
    .pointerAdd 12 11 7,  -- 12
    .core (.load 0 11),  -- 13
    .core (.load 1 12),  -- 14
    .core (.add 2 0 1),  -- 15
    .core (.sub 3 0 1),  -- 16
    .core (.store 11 2),  -- 17
    .core (.store 12 3),  -- 18
    .core (.pinc 10),  -- 19
    .core (.pjle 0 0 (off + 9)),  -- 20
    .pointerAdd 9 9 8,  -- 21 SN
    .core (.pjle 0 0 (off + 7)) ]  -- 22

/-- Ev, part before the transform (labels absolute in `ev`). -/
def evA (off : ℕ) : Program :=
  [ .core (.pset 1 (1)),  -- 0
    .core (.pset 2 (2)),  -- 1
    .integerLoad 14 0,  -- 2
    .integerLoad 3 1,  -- 3
    .core (.pset 7 (1)),  -- 4
    .core (.pset 4 (0)),  -- 5
    .core (.pset 6 (2)),  -- 6
    .core (.pjle 3 7 (off + 13)),  -- 7 ST
    .integerStore 6 7,  -- 8
    .core (.pinc 6),  -- 9
    .core (.pinc 4),  -- 10
    .pointerAdd 7 7 7,  -- 11
    .core (.pjle 0 0 (off + 7)),  -- 12
    .pointerReal 0 14,  -- 13 STD
    .pointerReal 1 3,  -- 14
    .core (.mul 0 0 1),  -- 15
    .sqrt 0 0,  -- 16
    .core (.const 1 (1 : ℝ)),  -- 17
    .core (.div 4 1 0),  -- 18
    .core (.pset 15 (-1)),  -- 19
    .pointerSub 15 15 3,  -- 20
    .core (.pset 13 (0)),  -- 21
    .core (.pset 10 (0)),  -- 22
    .core (.pjle 14 10 (off + 27)),  -- 23 AB
    .pointerAdd 13 13 3,  -- 24
    .core (.pinc 10),  -- 25
    .core (.pjle 0 0 (off + 23)),  -- 26
    .core (.pset 16 (0)),  -- 27 ABD
    .core (.pset 17 (0)),  -- 28
    .core (.pjle 14 16 (off + 79)),  -- 29 VL
    .core (.pset 18 (0)),  -- 30
    .core (.pjle 3 18 (off + 43)),  -- 31 VR
    .pointerAdd 19 17 18,  -- 32
    .pointerSub 11 15 19,  -- 33
    .core (.load 0 11),  -- 34
    .core (.pset 11 (-1)),  -- 35
    .pointerSub 11 11 18,  -- 36
    .core (.load 1 11),  -- 37
    .core (.mul 0 0 1),  -- 38
    .pointerAdd 11 13 18,  -- 39
    .core (.store 11 0),  -- 40
    .core (.pinc 18),  -- 41
    .core (.pjle 0 0 (off + 31)) ]  -- 42

/-- Ev, part after the transform. -/
def evB (off : ℕ) : Program :=
  [ .core (.pset 20 (0)),  -- 66
    .core (.pcopy 21 16),  -- 67
    .core (.pjle 3 20 (off + 76)),  -- 68 VJ
    .pointerAdd 11 13 20,  -- 69
    .core (.load 0 11),  -- 70
    .core (.mul 0 0 4),  -- 71
    .core (.store 21 0),  -- 72
    .pointerAdd 21 21 14,  -- 73
    .core (.pinc 20),  -- 74
    .core (.pjle 0 0 (off + 68)),  -- 75
    .core (.pinc 16),  -- 76 VJD
    .pointerAdd 17 17 3,  -- 77
    .core (.pjle 0 0 (off + 29)),  -- 78
    .halt ]  -- 79 VD

/-- The evaluation program. -/
def ev (off : ℕ) : Program := evA off ++ fw (off + 43) ++ evB off

end DetANN.Supplement.Thm32


