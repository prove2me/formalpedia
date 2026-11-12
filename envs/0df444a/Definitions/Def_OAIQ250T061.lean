-- Prove2me | Definitions.Def_OAIQ250T061
-- name    : OAIQ250T061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:18:33.330482+00:00
-- url     : https://prove2.me/theorems/99e81ee6-6524-4f41-a0e6-fec92100e998
-- title:
--   Definitions bundle OAIQ250T061 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 7 definitions and 6 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.tr1_0_0`, `OAI.AtomicTriangular.FiniteCertificate.tr1_1_0`, `OAI.AtomicTriangular.FiniteCertificate.tr1_1_1`, `OAI.AtomicTriangular.FiniteCertificate.tr1_2_1`, `OAI.AtomicTriangular.FiniteCertificate.tr1_3_0`, `OAI.AtomicTriangular.FiniteCertificate.tr1_4_1`, `OAI.AtomicTriangular.FiniteCertificate.tr1_5_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Construction_Normalization`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean), [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp11.lean), [`Triangular_Taylor_TaylorRows10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows10.lean), [`Triangular_Taylor_TaylorRows11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows11.lean), [`Triangular_Taylor_TaylorRows12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows12.lean), [`Triangular_Taylor_TaylorRows13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows13.lean), [`Triangular_Taylor_TaylorRows14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows14.lean), [`Triangular_Taylor_TaylorRows15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows15.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T005`, `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T016`, `OAIQ250T026`, `OAIQ250T036`, `OAIQ250T037`, `OAIQ250T038`, `OAIQ250T039`, `OAIQ250T040`, `OAIQ250T041`, `OAIQ250T042`, `OAIQ250T043` and `OAIQ250T044` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086`, `OAIQ250T098`, `OAIQ250T110` and `OAIQ250T111`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T005
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T016
import Definitions.Def_OAIQ250T026
import Definitions.Def_OAIQ250T036
import Definitions.Def_OAIQ250T037
import Definitions.Def_OAIQ250T038
import Definitions.Def_OAIQ250T039
import Definitions.Def_OAIQ250T040
import Definitions.Def_OAIQ250T041
import Definitions.Def_OAIQ250T042
import Definitions.Def_OAIQ250T043
import Definitions.Def_OAIQ250T044

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_1_7_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 7)).exp = taylorExp1_1_7 j := by
  revert j
  decide +kernel
lemma taylorExp1_1_9_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 9)).exp = taylorExp1_1_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_0_0 : Fin 21 → Fin 8 → RI := ![tr1_0_0_0,tr1_0_0_1,tr1_0_0_2,tr1_0_0_3,tr1_0_0_4,tr1_0_0_5,tr1_0_0_6,tr1_0_0_7,tr1_0_0_8,tr1_0_0_9,tr1_0_0_10,tr1_0_0_11,tr1_0_0_12,tr1_0_0_13,tr1_0_0_14,tr1_0_0_15,tr1_0_0_16,tr1_0_0_17,tr1_0_0_18,tr1_0_0_19,tr1_0_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_1_0 : Fin 21 → Fin 8 → RI := ![tr1_1_0_0,tr1_1_0_1,tr1_1_0_2,tr1_1_0_3,tr1_1_0_4,tr1_1_0_5,tr1_1_0_6,tr1_1_0_7,tr1_1_0_8,tr1_1_0_9,tr1_1_0_10,tr1_1_0_11,tr1_1_0_12,tr1_1_0_13,tr1_1_0_14,tr1_1_0_15,tr1_1_0_16,tr1_1_0_17,tr1_1_0_18,tr1_1_0_19,tr1_1_0_20]
def tr1_1_1 : Fin 21 → Fin 8 → RI := ![tr1_1_1_0,tr1_1_1_1,tr1_1_1_2,tr1_1_1_3,tr1_1_1_4,tr1_1_1_5,tr1_1_1_6,tr1_1_1_7,tr1_1_1_8,tr1_1_1_9,tr1_1_1_10,tr1_1_1_11,tr1_1_1_12,tr1_1_1_13,tr1_1_1_14,tr1_1_1_15,tr1_1_1_16,tr1_1_1_17,tr1_1_1_18,tr1_1_1_19,tr1_1_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_2_1 : Fin 21 → Fin 8 → RI := ![tr1_2_1_0,tr1_2_1_1,tr1_2_1_2,tr1_2_1_3,tr1_2_1_4,tr1_2_1_5,tr1_2_1_6,tr1_2_1_7,tr1_2_1_8,tr1_2_1_9,tr1_2_1_10,tr1_2_1_11,tr1_2_1_12,tr1_2_1_13,tr1_2_1_14,tr1_2_1_15,tr1_2_1_16,tr1_2_1_17,tr1_2_1_18,tr1_2_1_19,tr1_2_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_3_0 : Fin 21 → Fin 8 → RI := ![tr1_3_0_0,tr1_3_0_1,tr1_3_0_2,tr1_3_0_3,tr1_3_0_4,tr1_3_0_5,tr1_3_0_6,tr1_3_0_7,tr1_3_0_8,tr1_3_0_9,tr1_3_0_10,tr1_3_0_11,tr1_3_0_12,tr1_3_0_13,tr1_3_0_14,tr1_3_0_15,tr1_3_0_16,tr1_3_0_17,tr1_3_0_18,tr1_3_0_19,tr1_3_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_4_1 : Fin 21 → Fin 8 → RI := ![tr1_4_1_0,tr1_4_1_1,tr1_4_1_2,tr1_4_1_3,tr1_4_1_4,tr1_4_1_5,tr1_4_1_6,tr1_4_1_7,tr1_4_1_8,tr1_4_1_9,tr1_4_1_10,tr1_4_1_11,tr1_4_1_12,tr1_4_1_13,tr1_4_1_14,tr1_4_1_15,tr1_4_1_16,tr1_4_1_17,tr1_4_1_18,tr1_4_1_19,tr1_4_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_5_0 : Fin 21 → Fin 8 → RI := ![tr1_5_0_0,tr1_5_0_1,tr1_5_0_2,tr1_5_0_3,tr1_5_0_4,tr1_5_0_5,tr1_5_0_6,tr1_5_0_7,tr1_5_0_8,tr1_5_0_9,tr1_5_0_10,tr1_5_0_11,tr1_5_0_12,tr1_5_0_13,tr1_5_0_14,tr1_5_0_15,tr1_5_0_16,tr1_5_0_17,tr1_5_0_18,tr1_5_0_19,tr1_5_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors09 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 9 k j) ∧ cellBarrier 9 < ∏ j : Fin 15,(cellFactor 9 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 9 k j) ∧ cellBarrier 9 < ∏ j : Fin 15,(cellFactor 9 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction

lemma normalizingDen_pos {z : ℝ} (hz : 0<z) : 0<normalizingDen z := by
  exact mul_pos (mul_pos Q_one_pos hz) (Real.exp_pos _)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_GaussianPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped FourierTransform SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular
open Construction

lemma gaussianSchwartz_apply (α : ℝ) (hα : 0<α) (x : Plane) :
    gaussianSchwartz α hα x=gaussian α x := by
  simp only [gaussianSchwartz,Analysis.gaussianSchwartz_apply,gaussian,neg_mul]
lemma gaussianSchwartz_coe (α : ℝ) (hα : 0<α) :
    (gaussianSchwartz α hα : Plane → ℝ)=gaussian α := funext (gaussianSchwartz_apply α hα)
end AtomicTriangular
end

end OAI
end


