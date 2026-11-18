-- Prove2me | Definitions.Def_DetANN_HPIMPreProg
-- name    : DetANN_HPIMPreProg
-- status  : Definition
-- author  : @milia
-- created : 2026-11-17T09:26:08.38617+00:00
-- url     : https://prove2.me/theorems/3c52976f-d7db-4a18-bc32-fc6d8248a15e
-- title:
--   The HPIM preprocessing program and its contracts
-- statement:
--   The driver program of `hpim_preprocessing` on the PNormReg machine (definition `PNormReg_Machine`), built around four child blocks (definition `DetANN_HPIMPreBlocks`), and the predicates used to state its correctness in pieces. In a state, $I$ is the integer memory and $R$ the real memory.
--
--   1. **The program.**
--      - `Blocks` holds four block families (median, components, BSP build, balance) and their lengths.
--      - $\mathrm{prog}(B)$ is the concatenation of eight fixed driver segments with the four blocks placed at the offsets $o_0,\dots,o_{14}$, plus the ladder block of `hpim_query_program`.
--      - The labels are NODE, LK, LKE and RETURN.
--      - `Blocks.WF` says that every placed block has its declared length.
--   2. **Child contracts.** `MedOK`, `CompsOK`, `BuildOK` and `BalOK` restate the conclusions of `median_block`, `comps_block`, `build_block` and `balance_block` for the blocks of $B$, with constants $C$. `ChildOK B` bundles the four, with their constants $C_m, C_c, C_b, C_{bal}$.
--   3. **Invariants.**
--      - `GInv` is the global invariant after initialization:
--        - the registers hold $m$, $N$, $\delta$, $1+\delta/4$ and $\lambda$;
--        - $I[1]=m$, $I[2]$ is the root record, and $I[3]=4+N$;
--        - the point-address table $I[4+g]=1+gm$, the power table $I[4+N+t]=2^t$ for $t\le T_0$, and the points in real memory.
--      - `SList s a S` says that the sorted indices of $S$ are stored from $I[a]$.
--      - `NodeEnv` is the node-local register frame: record $v$, list $S_a$, $|S|$, and the scratch tops $Z_n$, $Z_{R,n}$.
--   4. **The node contract** `NodeOK … f` holds for every $S$ with $1\le|S|\le f+1$. Starting at NODE with a well-formed record for $S$, the run reaches RETURN with the invariant and frame intact, and:
--      - the integer and real heaps grow by at most $\mathrm{treePts}(f,S)\cdot K_H$ and $\mathrm{treePts}(f,S)\cdot K_R$;
--      - the work is at most $\mathrm{treePts}(f,S)\cdot K_W$;
--      - it writes only its record, the new heap and bounded scratch windows;
--      - it stores $\mathrm{hpimNode}(Y,\delta,f,S)$ at $v$, stably under changes outside these cells.
--   5. **Budgets.**
--      - The explicit per-node costs are `headW`, `lkW`, `lkH`, `lkR`, `lkD`, `midW`, `kidW` and `Dn`.
--      - The global ladder is $K_G$: the least $k$ with $8N\lambda\le c^{k-1}$, $c=1+\delta/4$. Then $T_{0G}=\lceil\log_2K_G\rceil$, and the root record is $v_{0G}$.
--      - `Budgets` says that given constants $K_W, K_H, K_R, W_I, W_R$ cover every node.
--      - `KWc`, `KHc`, `KRc`, `WbIc` and `WbRc` are concrete choices, and $A=1+C_m+C_c+C_b+C_{bal}$ (`Acon`).
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). These are the intermediate steps of the reduction of DetANN.HPIM.hpim_preprocessing, split so that each proof fits the verifier's time limit. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks

-- ===== PP_Ladder =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth

/-- **The ladder block.** In: real regs `40 = b`, `41 = ρ 0`, `42 = e`. Out: pointer `41 = M`
(one more than the least `k` with `b ≤ ρ k`), pointer `42 = t₀ = clog₂ (M - 1)`. Uses real regs
`41, 43`, pointers `40–43`. Exit: `off + 14`. -/
def ladder (off : ℕ) : Program :=
  [ .core (.pset 40 0),                 -- 0  k := 0
    .core (.sub 43 40 41),              -- 1  tmp := b - r
    .core (.jle 43 (off + 6)),          -- 2  b ≤ r → 6
    .core (.mul 41 41 42),              -- 3  r := r e
    .core (.pinc 40),                   -- 4  k := k + 1
    .core (.pjle 40 40 (off + 1)),      -- 5  → 1
    .core (.pcopy 41 40),               -- 6  M := k
    .core (.pinc 41),                   -- 7  M := k + 1
    .core (.pset 42 0),                 -- 8  t := 0
    .core (.pset 43 1),                 -- 9  w := 1
    .core (.pjle 40 43 (off + 14)),     -- 10 k ≤ w → exit
    .pointerAdd 43 43 43,               -- 11 w := 2 w
    .core (.pinc 42),                   -- 12 t := t + 1
    .core (.pjle 40 40 (off + 10)) ]    -- 13 → 10

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib

end DetANN.HPIM.PP

-- ===== PP_Prog =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth

/-- Driver segment 0 (39 instructions). Labels: CL = off + 14, CLE = off + 18, PAL = off + 26, PAE = off + 32. -/
def seg0 (off : ℕ) : Program :=
  [ .core (.pset 6 (0)),
    .integerLoad 23 6,
    .core (.pset 6 (1)),
    .integerLoad 1 6,
    .core (.pset 6 (0)),
    .core (.load 0 6),
    .core (.const 20 (0 : ℝ)),
    .core (.const 21 (2 : ℝ)),
    .core (.const 22 (4 : ℝ)),
    .core (.div 6 0 22),
    .core (.const 7 (1 : ℝ)),
    .core (.add 1 7 6),
    .core (.pset 5 (0)),
    .core (.pset 6 (1)),
    .core (.pjle 23 6 (off + 18)),
    .pointerAdd 6 6 6,
    .core (.pinc 5),
    .core (.pjle 0 0 (off + 14)),
    .pointerReal 5 5,
    .core (.add 5 5 7),
    .core (.mul 5 22 5),
    .core (.div 2 5 0),
    .core (.pset 12 (4)),
    .core (.pset 6 (1)),
    .core (.pset 3 (0)),
    .core (.pcopy 7 12),
    .core (.pjle 23 3 (off + 32)),
    .integerStore 7 6,
    .pointerAdd 6 6 1,
    .core (.pinc 7),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 26)),
    .core (.pcopy 16 6),
    .core (.const 5 (8 : ℝ)),
    .pointerReal 6 23,
    .core (.mul 40 5 6),
    .core (.mul 40 40 2),
    .core (.div 41 7 1),
    .core (.add 42 1 20) ]

/-- Driver segment 2 (58 instructions). Labels: PWL = off + 6, PWB = off + 8, PWE = off + 13, RSL = off + 17, RSE = off + 22, NODE = off + 39, INNER = off + 54. -/
def seg2 (off RETURN : ℕ) : Program :=
  [ .pointerAdd 9 12 23,
    .core (.pset 6 (3)),
    .integerStore 6 9,
    .core (.pset 3 (0)),
    .core (.pset 6 (1)),
    .core (.pcopy 7 9),
    .core (.pjle 3 42 (off + 8)),
    .core (.pjle 0 0 (off + 13)),
    .integerStore 7 6,
    .pointerAdd 6 6 6,
    .core (.pinc 7),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 6)),
    .core (.pcopy 15 7),
    .core (.pcopy 10 15),
    .core (.pset 3 (0)),
    .core (.pcopy 7 10),
    .core (.pjle 23 3 (off + 22)),
    .integerStore 7 3,
    .core (.pinc 7),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 17)),
    .core (.pcopy 2 7),
    .core (.pset 27 (3)),
    .pointerAdd 6 2 27,
    .integerStore 6 10,
    .core (.pset 27 (7)),
    .pointerAdd 6 2 27,
    .integerStore 6 23,
    .core (.pset 27 (8)),
    .pointerAdd 15 2 27,
    .core (.pset 6 (2)),
    .integerStore 6 2,
    .core (.pset 8 (-10)),
    .core (.pset 6 (0)),
    .integerStore 8 6,
    .core (.pcopy 13 8),
    .core (.pset 14 (0)),
    .core (.pjle 0 0 (off + 39)),
    .core (.pset 27 (3)),
    .pointerAdd 6 2 27,
    .integerLoad 10 6,
    .core (.pset 27 (7)),
    .pointerAdd 6 2 27,
    .integerLoad 11 6,
    .core (.pset 27 (2)),
    .core (.pjle 27 11 (off + 54)),
    .core (.pset 6 (0)),
    .integerStore 2 6,
    .integerLoad 6 10,
    .core (.pcopy 7 2),
    .core (.pinc 7),
    .integerStore 7 6,
    .core (.pjle 0 0 (RETURN)),
    .core (.pset 6 (1)),
    .integerStore 2 6,
    .core (.pcopy 20 13),
    .core (.pcopy 28 14) ]

/-- Driver segment 4 (9 instructions). Labels: . -/
def seg4 (off : ℕ) : Program :=
  [ .core (.div 3 10 21),
    .pointerReal 6 11,
    .core (.mul 40 21 6),
    .core (.mul 40 40 2),
    .core (.mul 40 40 3),
    .core (.div 41 3 21),
    .core (.div 41 41 21),
    .core (.div 41 41 1),
    .core (.add 42 1 20) ]

/-- Driver segment 6 (82 instructions). Labels: LK = off + 22, B1 = off + 25, B2 = off + 33, SMN = off + 43, CMX = off + 44, SMX = off + 47, NX = off + 48, B2E = off + 50, SGS = off + 60, SGN = off + 61, B1E = off + 63, B3 = off + 66, B3E = off + 77. -/
def seg6 (off LKE : ℕ) : Program :=
  [ .core (.pcopy 4 41),
    .core (.pcopy 5 42),
    .core (.pcopy 6 2),
    .core (.pinc 6),
    .integerStore 6 4,
    .core (.pset 27 (6)),
    .pointerAdd 6 2 27,
    .integerStore 6 5,
    .core (.pcopy 18 15),
    .pointerAdd 15 15 4,
    .core (.pset 27 (2)),
    .pointerAdd 6 2 27,
    .integerStore 6 18,
    .core (.pcopy 19 15),
    .pointerAdd 15 15 11,
    .core (.pset 27 (4)),
    .pointerAdd 6 2 27,
    .integerStore 6 19,
    .core (.div 4 3 21),
    .core (.div 4 4 21),
    .core (.div 4 4 1),
    .core (.pset 3 (0)),
    .core (.pjle 4 3 (LKE)),
    .core (.pcopy 29 16),
    .core (.pset 22 (0)),
    .core (.pjle 1 22 (off + 63)),
    .integerLoad 6 10,
    .pointerAdd 6 12 6,
    .integerLoad 6 6,
    .pointerAdd 6 6 22,
    .core (.load 15 6),
    .core (.add 16 15 20),
    .core (.pset 31 (1)),
    .core (.pjle 11 31 (off + 50)),
    .pointerAdd 6 10 31,
    .integerLoad 6 6,
    .pointerAdd 6 12 6,
    .integerLoad 6 6,
    .pointerAdd 6 6 22,
    .core (.load 17 6),
    .core (.sub 5 17 15),
    .core (.jle 5 (off + 43)),
    .core (.pjle 0 0 (off + 44)),
    .core (.add 15 17 20),
    .core (.sub 5 16 17),
    .core (.jle 5 (off + 47)),
    .core (.pjle 0 0 (off + 48)),
    .core (.add 16 17 20),
    .core (.pinc 31),
    .core (.pjle 0 0 (off + 33)),
    .pointerAdd 6 29 22,
    .core (.store 6 15),
    .pointerAdd 6 6 1,
    .core (.store 6 16),
    .core (.sub 5 16 15),
    .core (.pset 27 (0)),
    .core (.pjle 22 27 (off + 60)),
    .core (.sub 6 13 5),
    .core (.jle 6 (off + 60)),
    .core (.pjle 0 0 (off + 61)),
    .core (.add 13 5 20),
    .core (.pinc 22),
    .core (.pjle 0 0 (off + 25)),
    .core (.mul 14 22 4),
    .core (.add 14 13 14),
    .core (.pset 22 (0)),
    .core (.pjle 1 22 (off + 77)),
    .pointerAdd 6 29 22,
    .core (.load 15 6),
    .core (.sub 15 15 14),
    .core (.store 6 15),
    .pointerAdd 6 6 1,
    .core (.load 16 6),
    .core (.add 16 16 14),
    .core (.store 6 16),
    .core (.pinc 22),
    .core (.pjle 0 0 (off + 66)),
    .pointerAdd 16 16 1,
    .pointerAdd 16 16 1,
    .core (.pcopy 17 29),
    .core (.add 11 4 20),
    .core (.add 12 1 20) ]

/-- Driver segment 8 (0 instructions). Labels: . -/
def seg8 (off : ℕ) : Program :=
  [  ]

/-- Driver segment 10 (26 instructions). Labels: LKE = off + 25. -/
def seg10 (off LK : ℕ) : Program :=
  [ .core (.pset 6 (1)),
    .integerStore 15 6,
    .core (.pcopy 7 15),
    .core (.pinc 7),
    .integerStore 7 29,
    .core (.pinc 7),
    .integerStore 7 17,
    .core (.pinc 7),
    .core (.pcopy 6 15),
    .core (.pset 27 (4)),
    .pointerAdd 6 6 27,
    .integerStore 7 6,
    .core (.pset 0 (0)),
    .integerStore 6 0,
    .core (.pinc 6),
    .integerStore 6 0,
    .pointerAdd 6 18 3,
    .integerStore 6 15,
    .core (.pset 27 (6)),
    .pointerAdd 15 15 27,
    .core (.pcopy 13 20),
    .core (.pcopy 14 28),
    .core (.mul 4 4 1),
    .core (.pinc 3),
    .core (.pjle 0 0 (LK)),
    .core (.mul 10 21 3) ]

/-- Driver segment 12 (29 instructions). Labels: RL = off + 3, RT = off + 9, RN = off + 14, RE = off + 16. -/
def seg12 (off : ℕ) : Program :=
  [ .core (.pcopy 25 15),
    .core (.pset 24 (0)),
    .core (.pset 3 (0)),
    .core (.pjle 11 3 (off + 16)),
    .pointerSub 6 20 3,
    .core (.pdec 6),
    .integerLoad 30 6,
    .core (.pjle 3 30 (off + 9)),
    .core (.pjle 0 0 (off + 14)),
    .pointerAdd 6 10 3,
    .integerLoad 7 6,
    .pointerAdd 6 25 24,
    .integerStore 6 7,
    .core (.pinc 24),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 3)),
    .pointerAdd 21 25 24,
    .core (.pset 27 (3)),
    .pointerAdd 6 21 27,
    .integerStore 6 25,
    .core (.pset 27 (7)),
    .pointerAdd 6 21 27,
    .integerStore 6 24,
    .core (.pset 27 (8)),
    .pointerAdd 15 21 27,
    .core (.pset 27 (5)),
    .pointerAdd 6 2 27,
    .integerStore 6 21,
    .core (.add 10 3 20) ]

/-- Driver segment 14 (107 instructions). Labels: KL = off + 1, KNEW = off + 7, K1 = off + 10, K1A = off + 16, K1T = off + 18, K1N = off + 23, K1E = off + 25, K2 = off + 35, K2A = off + 41, K2T = off + 43, K2N = off + 45, K2E = off + 47, KN = off + 76, KE = off + 78, RETURN = off + 82, HALT = off + 106. -/
def seg14 (off NODE : ℕ) : Program :=
  [ .core (.pset 3 (0)),
    .core (.pjle 11 3 (off + 78)),
    .pointerSub 6 20 3,
    .core (.pdec 6),
    .integerLoad 30 6,
    .core (.pjle 3 30 (off + 7)),
    .core (.pjle 0 0 (off + 76)),
    .core (.pcopy 25 15),
    .core (.pset 24 (0)),
    .core (.pcopy 22 3),
    .core (.pjle 11 22 (off + 25)),
    .pointerSub 6 20 22,
    .core (.pdec 6),
    .integerLoad 31 6,
    .core (.pjle 31 3 (off + 16)),
    .core (.pjle 0 0 (off + 23)),
    .core (.pjle 3 31 (off + 18)),
    .core (.pjle 0 0 (off + 23)),
    .pointerAdd 6 10 22,
    .integerLoad 7 6,
    .pointerAdd 6 25 24,
    .integerStore 6 7,
    .core (.pinc 24),
    .core (.pinc 22),
    .core (.pjle 0 0 (off + 10)),
    .pointerAdd 26 25 24,
    .core (.pset 27 (3)),
    .pointerAdd 6 26 27,
    .integerStore 6 25,
    .core (.pset 27 (7)),
    .pointerAdd 6 26 27,
    .integerStore 6 24,
    .core (.pset 27 (8)),
    .pointerAdd 15 26 27,
    .core (.pcopy 22 3),
    .core (.pjle 11 22 (off + 47)),
    .pointerSub 6 20 22,
    .core (.pdec 6),
    .integerLoad 31 6,
    .core (.pjle 31 3 (off + 41)),
    .core (.pjle 0 0 (off + 45)),
    .core (.pjle 3 31 (off + 43)),
    .core (.pjle 0 0 (off + 45)),
    .pointerAdd 6 19 22,
    .integerStore 6 26,
    .core (.pinc 22),
    .core (.pjle 0 0 (off + 35)),
    .pointerSub 6 20 11,
    .core (.pset 27 (10)),
    .pointerSub 6 6 27,
    .core (.pset 7 (1)),
    .core (.pcopy 9 6),
    .integerStore 9 7,
    .core (.pinc 9),
    .integerStore 9 2,
    .core (.pinc 9),
    .integerStore 9 3,
    .core (.pinc 9),
    .integerStore 9 11,
    .core (.pinc 9),
    .integerStore 9 10,
    .core (.pinc 9),
    .integerStore 9 20,
    .core (.pinc 9),
    .integerStore 9 19,
    .core (.pinc 9),
    .integerStore 9 21,
    .core (.pinc 9),
    .integerStore 9 8,
    .core (.pinc 9),
    .integerStore 9 28,
    .core (.pcopy 8 6),
    .core (.pcopy 13 6),
    .core (.pcopy 14 28),
    .core (.pcopy 2 26),
    .core (.pjle 0 0 (NODE)),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 1)),
    .core (.pcopy 2 21),
    .core (.pcopy 13 20),
    .core (.pcopy 14 28),
    .core (.pjle 0 0 (NODE)),
    .integerLoad 6 8,
    .core (.pset 27 (0)),
    .core (.pjle 6 27 (off + 106)),
    .core (.pcopy 9 8),
    .core (.pinc 9),
    .integerLoad 2 9,
    .core (.pinc 9),
    .integerLoad 3 9,
    .core (.pinc 9),
    .integerLoad 11 9,
    .core (.pinc 9),
    .integerLoad 10 9,
    .core (.pinc 9),
    .integerLoad 20 9,
    .core (.pinc 9),
    .integerLoad 19 9,
    .core (.pinc 9),
    .integerLoad 21 9,
    .core (.pinc 9),
    .core (.pinc 9),
    .integerLoad 28 9,
    .core (.pdec 9),
    .integerLoad 8 9,
    .core (.pjle 0 0 (off + 76)),
    .halt ]

/-- The child blocks and their lengths. -/
structure Blocks where
  med : ℕ → Program
  comps : ℕ → Program
  build : ℕ → Program
  bal : ℕ → Program
  Lm : ℕ
  Lc : ℕ
  Lb : ℕ
  Lbal : ℕ

namespace Blocks

/-- Offset of piece 0. -/
def o0 (B : Blocks) : ℕ := 0

/-- Offset of piece 1. -/
def o1 (B : Blocks) : ℕ := 39

/-- Offset of piece 2. -/
def o2 (B : Blocks) : ℕ := 39 + 14

/-- Offset of piece 3. -/
def o3 (B : Blocks) : ℕ := 39 + 14 + 58

/-- Offset of piece 4. -/
def o4 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm

/-- Offset of piece 5. -/
def o5 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9

/-- Offset of piece 6. -/
def o6 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14

/-- Offset of piece 7. -/
def o7 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82

/-- Offset of piece 8. -/
def o8 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb

/-- Offset of piece 9. -/
def o9 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0

/-- Offset of piece 10. -/
def o10 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal

/-- Offset of piece 11. -/
def o11 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26

/-- Offset of piece 12. -/
def o12 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26 + B.Lc

/-- Offset of piece 13. -/
def o13 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26 + B.Lc + 29

/-- Offset of piece 14. -/
def o14 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26 + B.Lc + 29 + B.Lc

def lbl_NODE (B : Blocks) : ℕ := B.o2 + 39

def lbl_LK (B : Blocks) : ℕ := B.o6 + 22

def lbl_LKE (B : Blocks) : ℕ := B.o10 + 25

def lbl_RETURN (B : Blocks) : ℕ := B.o14 + 82

/-- The preprocessing program. -/
def prog (B : Blocks) : Program :=
  seg0 B.o0 ++
  ladder B.o1 ++
  seg2 B.o2 B.lbl_RETURN ++
  B.med B.o3 ++
  seg4 B.o4 ++
  ladder B.o5 ++
  seg6 B.o6 B.lbl_LKE ++
  B.build B.o7 ++
  seg8 B.o8 ++
  B.bal B.o9 ++
  seg10 B.o10 B.lbl_LK ++
  B.comps B.o11 ++
  seg12 B.o12 ++
  B.comps B.o13 ++
  seg14 B.o14 B.lbl_NODE

end Blocks

end DetANN.HPIM.PP

-- ===== PP_Basic =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN

/-- The child blocks have their declared lengths. -/
def Blocks.WF (B : Blocks) : Prop :=
  (∀ off, (B.med off).length = B.Lm) ∧ (∀ off, (B.comps off).length = B.Lc) ∧
    (∀ off, (B.build off).length = B.Lb) ∧ (∀ off, (B.bal off).length = B.Lbal)

variable (B : Blocks)

end DetANN.HPIM.PP

-- ===== PP_Spec =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM

variable {m N : ℕ}

/-- The global invariant of the driver after initialisation. -/
structure GInv (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ) (s : State) :
    Prop where
  pm : s.core.ptrs 1 = m
  pPA : s.core.ptrs 12 = 4
  pN : s.core.ptrs 23 = N
  r0 : s.core.regs 0 = δ
  r1 : s.core.regs 1 = 1 + δ / 4
  r2 : s.core.regs 2 = lamOf N δ
  r20 : s.core.regs 20 = 0
  r21 : s.core.regs 21 = 2
  r22 : s.core.regs 22 = 4
  i1 : s.integerMemory 1 = m
  i2 : s.integerMemory 2 = v0
  i3 : s.integerMemory 3 = 4 + N
  pa : ∀ g : Fin N, s.integerMemory (4 + g) = 1 + g * m
  pow : ∀ t ≤ T0, s.integerMemory (4 + N + t) = 2 ^ t
  pts : ∀ (g : Fin N) (j : Fin m), s.core.mem (1 + g * m + j) = Y g j

/-- The sorted global indices of `S` are stored from integer address `a`. -/
def SList {N : ℕ} (s : State) (a : ℤ) (S : Finset (Fin N)) : Prop :=
  ∀ i : Fin S.card, s.integerMemory (a + i) = ((S.orderEmbOfFin rfl i : Fin N) : ℕ)

/-- The heap starts above the tables: `4 + N + T0 + 1`. -/
def Hbase (N T0 : ℕ) : ℤ := 4 + N + T0 + 1

/-- `median_block` for `B.med` (constant `C`). -/
def MedOK (B : Blocks) (C : ℕ) : Prop :=
  ∀ (off : ℕ) (Q : Program), Embeds Q (B.med off) off →
  ∀ (m n : ℕ) (pts : Fin n → EuclideanSpace ℝ (Fin m)) (s : State),
    1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false →
    LocalPts s (fun i j => pts i j) → s.core.ptrs 13 ≤ 0 →
    ∃ t, (run Q s detTape t).core.pc = off + B.Lm ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.regs 10 = medThreshold pts ∧
      KeepsLow s (run Q s detTape t) [] [10] ∧
      WritesOnly Q s t (fun c => c.1 = false ∧
        s.core.ptrs 13 - C * (n + 1) ≤ c.2 ∧ c.2 < s.core.ptrs 13) ∧
      (run Q s detTape t).work ≤ s.work + C * (n + 1) ^ 5 * (m + 1)

/-- `comps_block` for `B.comps` (constant `C`). -/
def CompsOK (B : Blocks) (C : ℕ) : Prop :=
  ∀ (off : ℕ) (Q : Program), Embeds Q (B.comps off) off →
  ∀ (m n : ℕ) (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (s : State),
    1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false →
    LocalPts s (fun i j => pts i j) → s.core.regs 10 = d → 0 ≤ d → s.core.ptrs 13 ≤ 0 →
    ∃ t, (run Q s detTape t).core.pc = off + B.Lc ∧ (run Q s detTape t).halted = false ∧
      (∀ i : Fin n, (run Q s detTape t).integerMemory (s.core.ptrs 13 - 1 - i) = compMin pts d i) ∧
      KeepsLow s (run Q s detTape t) [] [] ∧
      WritesOnly Q s t (fun c => c.1 = false ∧
        s.core.ptrs 13 - C * (n + 1) ≤ c.2 ∧ c.2 < s.core.ptrs 13) ∧
      (run Q s detTape t).work ≤ s.work + C * (n + 1) ^ 3 * (m + 1)

/-- `build_block` for `B.build` (constant `C`). -/
def BuildOK (B : Blocks) (C : ℕ) : Prop :=
  ∀ (off : ℕ) (Q : Program), Embeds Q (B.build off) off →
  ∀ (m n f : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (lo hi : Fin m → ℝ) (s : State),
    1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false → LocalPts s pts →
    s.core.regs 11 = r → s.core.regs 12 = c → 0 ≤ s.core.ptrs 17 →
    (∀ j : Fin m, s.core.mem (s.core.ptrs 17 + j) = lo j) →
    (∀ j : Fin m, s.core.mem (s.core.ptrs 17 + m + j) = hi j) →
    s.core.ptrs 13 ≤ 0 → s.core.ptrs 14 ≤ 0 → ¬ Starves pts r c f lo hi →
    ∃ t, (run Q s detTape t).core.pc = off + B.Lb ∧ (run Q s detTape t).halted = false ∧
      BSPAt m (run Q s detTape t) ((run Q s detTape t).core.ptrs 13) (s.core.ptrs 13)
        ((run Q s detTape t).core.ptrs 14) (s.core.ptrs 14) ((run Q s detTape t).core.ptrs 17)
        (build pts r c f lo hi) ∧
      KeepsLow s (run Q s detTape t) [13, 14, 17] [] ∧
      s.core.ptrs 13 - C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤
        (run Q s detTape t).core.ptrs 13 ∧
      s.core.ptrs 14 - C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤
        (run Q s detTape t).core.ptrs 14 ∧
      WritesOnly Q s t (fun w =>
        (if w.1 then s.core.ptrs 14 else s.core.ptrs 13) -
            C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤ w.2 ∧
          w.2 < (if w.1 then s.core.ptrs 14 else s.core.ptrs 13)) ∧
      (run Q s detTape t).work ≤ s.work +
        C * ((build pts r c f lo hi).paths.card + 1) ^ 2 * (n + 1) * (m + 1) ^ 2

/-- `balance_block` for `B.bal` (constant `C`). -/
def BalOK (B : Blocks) (C : ℕ) : Prop :=
  ∀ (off : ℕ) (Q : Program), Embeds Q (B.bal off) off →
  ∀ (m : ℕ) (T : BSP m) (s : State) (ilo ihi rlo rhi : ℤ),
    1 ≤ m → s.core.pc = off → s.halted = false → s.core.ptrs 1 = m →
    BSPAt m s ilo ihi rlo rhi (s.core.ptrs 17) T → ihi ≤ 0 → rhi ≤ 0 →
    s.core.ptrs 13 ≤ ilo → s.core.ptrs 14 ≤ rlo → 0 ≤ s.core.ptrs 15 → 0 ≤ s.core.ptrs 16 →
    ∃ t, (run Q s detTape t).core.pc = off + B.Lbal ∧ (run Q s detTape t).halted = false ∧
      (∀ s'' : State,
        (∀ z, s.core.ptrs 15 ≤ z → z < (run Q s detTape t).core.ptrs 15 →
          s''.integerMemory z = (run Q s detTape t).integerMemory z) →
        (∀ z, s.core.ptrs 16 ≤ z → z < (run Q s detTape t).core.ptrs 16 →
          s''.core.mem z = (run Q s detTape t).core.mem z) →
        BoxTreeAt m s'' ((run Q s detTape t).core.ptrs 17) (balance T (T.paths.card + 1) [] ∅)) ∧
      KeepsLow s (run Q s detTape t) [15, 16, 17] [] ∧
      s.core.ptrs 15 ≤ (run Q s detTape t).core.ptrs 15 ∧
      (run Q s detTape t).core.ptrs 15 ≤ s.core.ptrs 15 + C * (T.paths.card + 1) ∧
      s.core.ptrs 16 ≤ (run Q s detTape t).core.ptrs 16 ∧
      (run Q s detTape t).core.ptrs 16 ≤ s.core.ptrs 16 + C * (T.paths.card + 1) * m ∧
      WritesOnly Q s t (fun c =>
        ((if c.1 then s.core.ptrs 14 else s.core.ptrs 13) - C * (T.paths.card + 1) ≤ c.2 ∧
          c.2 < (if c.1 then s.core.ptrs 14 else s.core.ptrs 13)) ∨
        ((if c.1 then s.core.ptrs 16 else s.core.ptrs 15) ≤ c.2 ∧
          c.2 < (if c.1 then (run Q s detTape t).core.ptrs 16
            else (run Q s detTape t).core.ptrs 15))) ∧
      (run Q s detTape t).work ≤ s.work + C * (T.paths.card + 1) ^ 2 * (m + 1)

/-- All four child contracts. -/
structure ChildOK (B : Blocks) where
  Cm : ℕ
  Cc : ℕ
  Cb : ℕ
  Cbal : ℕ
  med : MedOK B Cm
  comps : CompsOK B Cc
  build : BuildOK B Cb
  bal : BalOK B Cbal

end DetANN.HPIM.PP

-- ===== PP_Env =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- The registers and memory a node body relies on. -/
structure NodeEnv (S : Finset (Fin N)) (v Sa Zn ZRn : ℤ) (s : State) : Prop where
  g : GInv Y δ T0 v0 s
  p2 : s.core.ptrs 2 = v
  p10 : s.core.ptrs 10 = Sa
  p11 : s.core.ptrs 11 = S.card
  p20 : s.core.ptrs 20 = Zn
  p28 : s.core.ptrs 28 = ZRn
  slist : SList s Sa S
  sa : 0 ≤ Sa

end DetANN.HPIM.PP

-- ===== PP_LK =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- The BSP bound of a node with `n` points: `2 bspFuel + 1`. -/
noncomputable def bspB (n m : ℕ) (δ : ℝ) : ℕ := 2 * bspFuel n m δ + 1

end DetANN.HPIM.PP

-- ===== PP_LKLoop =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- Per-iteration work bound of the lookup loop. -/
noncomputable def lkW {B : Blocks} (ch : ChildOK B) (n m : ℕ) (δ : ℝ) : ℕ :=
  (15 * n + 30) * m + 11 * m + 38 + ch.Cb * bspB n m δ ^ 2 * (n + 1) * (m + 1) ^ 2 +
    ch.Cbal * bspB n m δ ^ 2 * (m + 1)

/-- Scratch depth of a lookup iteration. -/
noncomputable def lkD {B : Blocks} (ch : ChildOK B) (n m : ℕ) (δ : ℝ) : ℕ := (ch.Cb * (m + 1) + ch.Cbal) * bspB n m δ

/-- Heap growth (integer, real) of a lookup iteration. -/
noncomputable def lkH {B : Blocks} (ch : ChildOK B) (n m : ℕ) (δ : ℝ) : ℕ := ch.Cbal * bspB n m δ + 6

noncomputable def lkR {B : Blocks} (ch : ChildOK B) (n m : ℕ) (δ : ℝ) : ℕ := 2 * m + ch.Cbal * bspB n m δ * m

end DetANN.HPIM.PP

-- ===== PP_NodeHead =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- Work of the node head. -/
noncomputable def headW {B : Blocks} (ch : ChildOK B) (n m M : ℕ) : ℕ :=
  12 + ch.Cm * (n + 1) ^ 5 * (m + 1) + 9 + (5 * (M - 1) + 4 * Nat.clog 2 (M - 1) + 8) + 22

end DetANN.HPIM.PP

-- ===== PP_NodeOK =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- Integer scratch depth of a node on `n` points. -/
def Dn (WbI n : ℕ) : ℕ := 2 * n + 10 * (Nat.clog 2 n + 1) + WbI

/-- **The node contract** at fuel `f`: from `NODE` with the record at `v` (list at `Sa`, `n` points),
the heap tops `H, HR`, the scratch tops `Zn, ZRn` and the frame pointer `FP`, the program reaches
`RETURN` with the frame pointer and the global invariant intact, within the budgets, writing only the
record, the new heap and the scratch below the tops, and with the tree stored at `v`. -/
def NodeOKAt (B : Blocks) (KW KH KR WbI WbR : ℕ) (f : ℕ) (S : Finset (Fin N)) : Prop :=
  ∀ (s : State) (v Sa Zn ZRn FP H HR : ℤ),
    s.core.pc = B.lbl_NODE → s.halted = false → GInv Y δ T0 v0 s →
    s.core.ptrs 2 = v → s.core.ptrs 13 = Zn → s.core.ptrs 14 = ZRn → s.core.ptrs 8 = FP →
    s.core.ptrs 15 = H → s.core.ptrs 16 = HR →
    s.integerMemory (v + 3) = Sa → s.integerMemory (v + 7) = S.card → SList s Sa S →
    Hbase N T0 ≤ Sa → Sa + S.card ≤ v → v + 8 ≤ H → 1 + (N : ℤ) * m ≤ HR → Zn ≤ 0 → ZRn ≤ 0 →
    ∃ t, (run (Blocks.prog B) s detTape t).core.pc = B.lbl_RETURN ∧
      (run (Blocks.prog B) s detTape t).halted = false ∧
      GInv Y δ T0 v0 (run (Blocks.prog B) s detTape t) ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 8 = FP ∧
      H ≤ (run (Blocks.prog B) s detTape t).core.ptrs 15 ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 15 ≤ H + treePts Y f S * KH ∧
      HR ≤ (run (Blocks.prog B) s detTape t).core.ptrs 16 ∧
      (run (Blocks.prog B) s detTape t).core.ptrs 16 ≤ HR + treePts Y f S * KR ∧
      (run (Blocks.prog B) s detTape t).work ≤ s.work + treePts Y f S * KW ∧
      (∀ c ∈ cellsWritten (Blocks.prog B) s t,
        (c.1 = false ∧ ((v ≤ c.2 ∧ c.2 < v + 8) ∨
          (H ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 15) ∨
          (Zn - Dn WbI S.card ≤ c.2 ∧ c.2 < Zn))) ∨
        (c.1 = true ∧ ((HR ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 16) ∨
          (ZRn - WbR ≤ c.2 ∧ c.2 < ZRn)))) ∧
      (∀ s'' : State,
        (∀ z, Sa ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 15 →
          s''.integerMemory z = (run (Blocks.prog B) s detTape t).integerMemory z) →
        (∀ z, 0 ≤ z → z < Hbase N T0 →
          s''.integerMemory z = (run (Blocks.prog B) s detTape t).integerMemory z) →
        (∀ z, HR ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 16 →
          s''.core.mem z = (run (Blocks.prog B) s detTape t).core.mem z) →
        HTreeAt m s'' v (hpimNode Y δ f S))

/-- The node contract at fuel `f`, for every set of at most `f + 1` points. -/
def NodeOK (B : Blocks) (KW KH KR WbI WbR : ℕ) (f : ℕ) : Prop :=
  ∀ (S : Finset (Fin N)), 1 ≤ S.card → S.card ≤ f + 1 → NodeOKAt Y δ T0 v0 B KW KH KR WbI WbR f S

end DetANN.HPIM.PP

-- ===== PP_KidSem =====
namespace DetANN.HPIM.PP

open PNormReg DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m))

/-- The kids threshold. -/
noncomputable def dK (S : Finset (Fin N)) : ℝ := 2 * (rmedOf Y S / 2)

/-- The labels written by the second components call. -/
noncomputable def labOf (S : Finset (Fin N)) (j : ℕ) : ℤ :=
  if h : j < S.card then (compMin (ptsOf Y S) (dK Y S) ⟨j, h⟩ : ℤ) else 0

/-- The components whose least index is at least `i`. -/
noncomputable def compsFrom (S : Finset (Fin N)) (i : ℕ) : Finset (Finset (Fin N)) :=
  ((Finset.univ : Finset (Fin S.card)).filter (fun j => i ≤ compMin (ptsOf Y S) (dK Y S) j)).image
    (compBotOf Y S)

end DetANN.HPIM.PP

-- ===== PP_Kids =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- Per-index overhead of the kids loop. -/
def kidW (n : ℕ) : ℕ := 23 * n + 80

/-- The heap of the children from index `i` on: each one's list and record, and its own budget. -/
noncomputable def kidSumH (f : ℕ) (S : Finset (Fin N)) (i KH : ℕ) : ℕ :=
  ∑ C ∈ compsFrom Y S i, (C.card + 8 + treePts Y f C * KH)

/-- The sum of the children budgets from index `i` on. -/
noncomputable def kidSum (f : ℕ) (S : Finset (Fin N)) (i : ℕ) : ℕ :=
  ∑ C ∈ compsFrom Y S i, treePts Y f C

end DetANN.HPIM.PP

-- ===== PP_NodeMid =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- Work of the node middle. -/
noncomputable def midW {B : Blocks} (ch : ChildOK B) (n m : ℕ) : ℕ :=
  2 * (ch.Cc * (n + 1) ^ 3 * (m + 1)) + 12 * n + 18

end DetANN.HPIM.PP

-- ===== PP_Node =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

/-- The budget constants of the node contract are large enough for every node. -/
abbrev Budgets (B : Blocks) (ch : ChildOK B) (KW KH KR WbI WbR : ℕ) : Prop :=
  (15 ≤ KW) ∧
  (∀ S : Finset (Fin N), 2 ≤ S.card →
    headW ch S.card m (MOf Y δ S) + MOf Y δ S * lkW ch S.card m δ + 2 + midW ch S.card m +
      S.card * kidW S.card + 5 ≤ S.card * KW) ∧
  (∀ S : Finset (Fin N), 2 ≤ S.card →
    MOf Y δ S + MOf Y δ S * lkH ch S.card m δ + 11 * S.card + 8 ≤ S.card * KH) ∧
  (∀ S : Finset (Fin N), 2 ≤ S.card → MOf Y δ S * lkR ch S.card m δ ≤ S.card * KR) ∧
  (∀ S : Finset (Fin N), 2 ≤ S.card → ch.Cm * (S.card + 1) ≤ WbI) ∧
  (∀ S : Finset (Fin N), 2 ≤ S.card → ch.Cc * (S.card + 1) ≤ WbI) ∧
  (∀ S : Finset (Fin N), 2 ≤ S.card → lkD ch S.card m δ ≤ WbI) ∧
  (∀ S : Finset (Fin N), 2 ≤ S.card → lkD ch S.card m δ ≤ WbR) ∧
  (10 ≤ WbI) ∧
  (∀ S : Finset (Fin N), 2 ≤ S.card → Nat.clog 2 (MOf Y δ S - 1) ≤ T0)

section

variable {Y δ T0}

end

end DetANN.HPIM.PP

-- ===== PP_Init =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

section Input

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

end Input

/-- The global ladder condition `8 N λ ≤ ρ_k` with `ρ_k = e^k / e`, `e = 1 + δ/4`. -/
def gCond (N : ℕ) (δ : ℝ) (k : ℕ) : Prop :=
  8 * (N : ℝ) * lamOf N δ ≤ 1 / (1 + δ / 4) * (1 + δ / 4) ^ k

/-- The least `k` of the global ladder (`M_glob - 1`). -/
noncomputable def KG (N : ℕ) (δ : ℝ) : ℕ := if h : ∃ k, gCond N δ k then Nat.find h else 0

/-- The size of the power table: `t₀` of the global ladder. -/
noncomputable def T0G (N : ℕ) (δ : ℝ) : ℕ := Nat.clog 2 (KG N δ)

/-- The root record. -/
noncomputable def v0G (N : ℕ) (δ : ℝ) : ℤ := Hbase N (T0G N δ) + N

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

end DetANN.HPIM.PP

-- ===== PP_Budget =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

/-- `⌈(2^12/(δ/4))^{2m}⌉`: the per-point BSP fuel. -/
noncomputable def Gn (m : ℕ) (δ : ℝ) : ℕ := ⌈((2 : ℝ) ^ 12 / (δ / 4)) ^ (2 * m)⌉₊

section

variable {B : Blocks} (ch : ChildOK B)

end

/-- `M_glob = KG + 1` bounds every ladder length. -/
noncomputable def MGG (N : ℕ) (δ : ℝ) : ℕ := KG N δ + 1

/-- The work budget per point. -/
noncomputable def KWc {B : Blocks} (ch : ChildOK B) (N m : ℕ) (δ : ℝ) : ℕ :=
  headW ch N m (MGG N δ) + MGG N δ * lkW ch N m δ + 2 + midW ch N m + N * kidW N + 5

/-- The integer heap budget per point. -/
noncomputable def KHc {B : Blocks} (ch : ChildOK B) (N m : ℕ) (δ : ℝ) : ℕ :=
  MGG N δ * (ch.Cbal * (2 * Gn m δ + 3)) + 7 * MGG N δ + 19

/-- The real heap budget per point. -/
noncomputable def KRc {B : Blocks} (ch : ChildOK B) (N m : ℕ) (δ : ℝ) : ℕ :=
  MGG N δ * (2 * m + ch.Cbal * (2 * Gn m δ + 3) * m)

/-- The integer scratch budget of one node. -/
noncomputable def WbIc {B : Blocks} (ch : ChildOK B) (N m : ℕ) (δ : ℝ) : ℕ :=
  ch.Cm * (N + 1) + ch.Cc * (N + 1) + lkD ch N m δ + 10

/-- The real scratch budget of one node. -/
noncomputable def WbRc {B : Blocks} (ch : ChildOK B) (N m : ℕ) (δ : ℝ) : ℕ := lkD ch N m δ

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

end DetANN.HPIM.PP

-- ===== PP_Asym =====
namespace DetANN.HPIM.PP

open DetANN DetANN.HPIM Classical

section

variable (N : ℕ) (δ : ℝ)

end

section

variable (N m : ℕ) (δ : ℝ)

end

section Final

variable {B : Blocks} (ch : ChildOK B) (N m : ℕ) (δ : ℝ)

/-- One constant dominating the child constants. -/
def Acon : ℕ := 1 + ch.Cm + ch.Cc + ch.Cb + ch.Cbal

section

end

variable {N m δ}

end Final

section Final2

variable {B : Blocks} (ch : ChildOK B) {N m : ℕ} {δ : ℝ}

end Final2

section Final3

variable {B : Blocks} (ch : ChildOK B) {N m : ℕ} {δ : ℝ}

end Final3

end DetANN.HPIM.PP


