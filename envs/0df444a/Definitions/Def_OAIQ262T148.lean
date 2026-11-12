-- Prove2me | Definitions.Def_OAIQ262T148
-- name    : OAIQ262T148
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:01:51.499956+00:00
-- url     : https://prove2.me/theorems/d1963aac-2cd7-44cc-b07f-611e82ac193c
-- title:
--   Definitions bundle OAIQ262T148 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 57 declarations of OpenAI's Lean: 5 definitions and 52 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.ordinarySignValue`, `OAI.AtomicTriangular.FiniteCertificate.taylorAmplitudeBox`, `OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox`, `OAI.AtomicTriangular.FiniteCertificate.taylorWaveTable`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean), [`Triangular_Signs_ExceptionalSign0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign0.lean), [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Taylor_TaylorRowsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRowsBase.lean), [`Triangular_Taylor_TaylorWave`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave.lean), [`Triangular_Taylor_TaylorWave00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave00.lean), [`Triangular_Taylor_TaylorWave000`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave000.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T086`, `OAIQ262T092`, `OAIQ262T097`, `OAIQ262T098`, `OAIQ262T099`, `OAIQ262T100`, `OAIQ262T101`, `OAIQ262T108`, `OAIQ262T133`, `OAIQ262T134`, `OAIQ262T135` and `OAIQ262T136` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T159`, `OAIQ262T160`, `OAIQ262T161`, `OAIQ262T163`, `OAIQ262T164`, `OAIQ262T165`, `OAIQ262T166`, `OAIQ262T167`, `OAIQ262T168`, `OAIQ262T169`, `OAIQ262T170`, `OAIQ262T171`, `OAIQ262T172`, `OAIQ262T173`, `OAIQ262T174`, `OAIQ262T175`, `OAIQ262T176`, `OAIQ262T177`, `OAIQ262T178`, `OAIQ262T179`, `OAIQ262T180`, `OAIQ262T181`, `OAIQ262T182`, `OAIQ262T183`, `OAIQ262T184` and `OAIQ262T185`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T086
import Definitions.Def_OAIQ262T092
import Definitions.Def_OAIQ262T097
import Definitions.Def_OAIQ262T098
import Definitions.Def_OAIQ262T099
import Definitions.Def_OAIQ262T100
import Definitions.Def_OAIQ262T101
import Definitions.Def_OAIQ262T108
import Definitions.Def_OAIQ262T133
import Definitions.Def_OAIQ262T134
import Definitions.Def_OAIQ262T135
import Definitions.Def_OAIQ262T136

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def taylorAmplitudeBox (q br : Fin 2) (j : Fin 31) : CI :=
  if br.val=0 then CI.point 1 else lambdaTable q j
lemma taylorAmplitudeBox_mem (q br : Fin 2) (j : Fin 31) :
    (taylorAmplitudeBox q br j).Mem (taylorAmplitude q br (frequency j)) := by
  unfold taylorAmplitudeBox taylorAmplitude
  split_ifs
  · simpa using CI.mem_point 1
  · exact lambdaTable_mem q j

def taylorWaveBox (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) : CI :=
  (((taylorAmplitudeBox q br j).mul (taylorExpTable q br n j)).mul
    ((taylorPhaseTable q br j).pow (l.val+2))).divNat (l.val+2).factorial

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_0_0_calc (j : Fin 31) : taylorWaveBox 0 0 0 0 j = tw0_0_0_0 j := by
  revert j
  decide +kernel
lemma tw0_0_0_1_calc (j : Fin 31) : taylorWaveBox 0 0 0 1 j = tw0_0_0_1 j := by
  revert j
  decide +kernel
lemma tw0_0_0_2_calc (j : Fin 31) : taylorWaveBox 0 0 0 2 j = tw0_0_0_2 j := by
  revert j
  decide +kernel
lemma tw0_0_0_3_calc (j : Fin 31) : taylorWaveBox 0 0 0 3 j = tw0_0_0_3 j := by
  revert j
  decide +kernel
lemma tw0_0_0_4_calc (j : Fin 31) : taylorWaveBox 0 0 0 4 j = tw0_0_0_4 j := by
  revert j
  decide +kernel
lemma tw0_0_0_5_calc (j : Fin 31) : taylorWaveBox 0 0 0 5 j = tw0_0_0_5 j := by
  revert j
  decide +kernel
lemma tw0_0_0_10_calc (j : Fin 31) : taylorWaveBox 0 0 0 10 j = tw0_0_0_10 j := by
  revert j
  decide +kernel
lemma tw0_0_0_11_calc (j : Fin 31) : taylorWaveBox 0 0 0 11 j = tw0_0_0_11 j := by
  revert j
  decide +kernel
lemma tw0_0_0_12_calc (j : Fin 31) : taylorWaveBox 0 0 0 12 j = tw0_0_0_12 j := by
  revert j
  decide +kernel
lemma tw0_0_0_13_calc (j : Fin 31) : taylorWaveBox 0 0 0 13 j = tw0_0_0_13 j := by
  revert j
  decide +kernel
lemma tw0_0_0_14_calc (j : Fin 31) : taylorWaveBox 0 0 0 14 j = tw0_0_0_14 j := by
  revert j
  decide +kernel
lemma tw0_0_0_15_calc (j : Fin 31) : taylorWaveBox 0 0 0 15 j = tw0_0_0_15 j := by
  revert j
  decide +kernel
lemma tw0_0_0_16_calc (j : Fin 31) : taylorWaveBox 0 0 0 16 j = tw0_0_0_16 j := by
  revert j
  decide +kernel
lemma tw0_0_0_17_calc (j : Fin 31) : taylorWaveBox 0 0 0 17 j = tw0_0_0_17 j := by
  revert j
  decide +kernel
lemma tw0_0_0_18_calc (j : Fin 31) : taylorWaveBox 0 0 0 18 j = tw0_0_0_18 j := by
  revert j
  decide +kernel
lemma tw0_0_0_19_calc (j : Fin 31) : taylorWaveBox 0 0 0 19 j = tw0_0_0_19 j := by
  revert j
  decide +kernel
lemma tw0_0_0_20_calc (j : Fin 31) : taylorWaveBox 0 0 0 20 j = tw0_0_0_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_0 : Fin 7 → Fin 21 → Fin 31 → CI := ![tw0_0_0,tw0_0_1,tw0_0_2,tw0_0_3,tw0_0_4,tw0_0_5,tw0_0_6]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def taylorWaveTable : Fin 2 → Fin 2 → Fin 7 → Fin 21 → Fin 31 → CI :=
  ![![tw0_0,tw0_1],![tw1_0,tw1_1]]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma exceptionalWeightBox_mem (test : Fin 4) (ep : Fin 2) (j : Fin 3) :
    (exceptionalWeightBox test ep j).Mem (exceptionalWeight test ep j) := by
  unfold exceptionalWeightBox exceptionalWeight
  split_ifs
  all_goals first
    | exact ep0
    | exact ep1
    | exact RI.mem_divNat ep1 (by norm_num)
    | exact RI.mem_divNat ep2 (by norm_num)
    | exact RI.mem_divNat (RI.mem_mul ep4 ZBox_mem) (by norm_num)
    | exact RI.mem_mul ep2 (RI.mem_pow ZBox_mem 2)
    | exact RI.mem_mul ep6 (RI.mem_pow ZBox_mem 2)
    | exact RI.mem_mul ep4 ZBox_mem

lemma exceptionalOffsetBox_mem (test : Fin 4) (l : ℕ) (r : Fin 8) :
    (exceptionalOffsetBox test l r).Mem (exceptionalOffset test l r) := by
  unfold exceptionalOffsetBox exceptionalOffset
  split_ifs
  · exact RI.mem_mul QBox1_mem ep1
  · exact RI.mem_mul QBox1_mem (RI.mem_mul (by simpa using RI.mem_point (test.val:ℤ)) ZBox_mem)
  · exact QBox1_mem
  · exact ep0
  · exact ep0

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex0r1_calc (r : Fin 8) : exceptionalRowBox 0 1 r = ex0r1 r := by
  revert r
  decide +kernel
lemma ex0r2_calc (r : Fin 8) : exceptionalRowBox 0 2 r = ex0r2 r := by
  revert r
  decide +kernel
lemma ex0r3_calc (r : Fin 8) : exceptionalRowBox 0 3 r = ex0r3 r := by
  revert r
  decide +kernel
lemma ex0r4_calc (r : Fin 8) : exceptionalRowBox 0 4 r = ex0r4 r := by
  revert r
  decide +kernel
lemma ex0r5_calc (r : Fin 8) : exceptionalRowBox 0 5 r = ex0r5 r := by
  revert r
  decide +kernel
lemma ex0r6_calc (r : Fin 8) : exceptionalRowBox 0 6 r = ex0r6 r := by
  revert r
  decide +kernel
lemma ex0r7_calc (r : Fin 8) : exceptionalRowBox 0 7 r = ex0r7 r := by
  revert r
  decide +kernel
lemma ex0r8_calc (r : Fin 8) : exceptionalRowBox 0 8 r = ex0r8 r := by
  revert r
  decide +kernel
lemma ex0r9_calc (r : Fin 8) : exceptionalRowBox 0 9 r = ex0r9 r := by
  revert r
  decide +kernel
lemma ex0r16_calc (r : Fin 8) : exceptionalRowBox 0 16 r = ex0r16 r := by
  revert r
  decide +kernel
lemma ex0r17_calc (r : Fin 8) : exceptionalRowBox 0 17 r = ex0r17 r := by
  revert r
  decide +kernel
lemma ex0r18_calc (r : Fin 8) : exceptionalRowBox 0 18 r = ex0r18 r := by
  revert r
  decide +kernel
lemma ex0r19_calc (r : Fin 8) : exceptionalRowBox 0 19 r = ex0r19 r := by
  revert r
  decide +kernel
lemma ex0r20_calc (r : Fin 8) : exceptionalRowBox 0 20 r = ex0r20 r := by
  revert r
  decide +kernel
lemma ex0r21_calc (r : Fin 8) : exceptionalRowBox 0 21 r = ex0r21 r := by
  revert r
  decide +kernel
lemma ex0b1_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 1 r = ex0b1 r := by
  revert r
  decide +kernel
lemma ex0b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 2 r = ex0b2 r := by
  revert r
  decide +kernel
lemma ex0b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 3 r = ex0b3 r := by
  revert r
  decide +kernel
lemma ex0b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 4 r = ex0b4 r := by
  revert r
  decide +kernel
lemma ex0b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 5 r = ex0b5 r := by
  revert r
  decide +kernel
lemma ex0b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 6 r = ex0b6 r := by
  revert r
  decide +kernel
lemma ex0b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 7 r = ex0b7 r := by
  revert r
  decide +kernel
lemma ex0b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 8 r = ex0b8 r := by
  revert r
  decide +kernel
lemma ex0b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 9 r = ex0b9 r := by
  revert r
  decide +kernel
lemma ex0b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 19 r = ex0b19 r := by
  revert r
  decide +kernel
lemma ex0b20_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 20 r = ex0b20 r := by
  revert r
  decide +kernel
lemma ex0b21_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 21 r = ex0b21 r := by
  revert r
  decide +kernel
lemma ex0b22_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 22 r = ex0b22 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex1r0_calc (r : Fin 8) : exceptionalRowBox 1 0 r = ex1r0 r := by
  revert r
  decide +kernel
lemma ex1b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 0 r = ex1b0 r := by
  revert r
  decide +kernel
lemma ex1b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 10 r = ex1b10 r := by
  revert r
  decide +kernel
lemma ex1b11_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 11 r = ex1b11 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def ordinarySignValue (side : Fin 2) (n : Fin 7) (y : Fin 2) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  if side.val=0 then (∑ r : Fin 8, ordinaryOffset n r*e r) -
    finiteTaylor side (nearNode n) (nearDisplacement n y) e τ
  else finiteTaylor side (nearNode n) (nearDisplacement n y) e τ
end AtomicTriangular.Construction
end

end OAI
end


