-- Prove2me | Definitions.Def_OAIQ250T059
-- name    : OAIQ250T059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:16:49.194564+00:00
-- url     : https://prove2.me/theorems/ba83896d-9800-497d-80d9-b58eaab7d1d0
-- title:
--   Definitions bundle OAIQ250T059 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 7 definitions and 4 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.tr0_1_0`, `OAI.AtomicTriangular.FiniteCertificate.tr0_1_1`, `OAI.AtomicTriangular.FiniteCertificate.tr0_3_0`, `OAI.AtomicTriangular.FiniteCertificate.tr0_3_1`, `OAI.AtomicTriangular.FiniteCertificate.tr0_4_1`, `OAI.AtomicTriangular.FiniteCertificate.tr0_5_0`, `OAI.AtomicTriangular.FiniteCertificate.tr0_6_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_DeletedQuotient`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/DeletedQuotient.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp11.lean), [`Triangular_Taylor_TaylorRows01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows01.lean), [`Triangular_Taylor_TaylorRows03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows03.lean), [`Triangular_Taylor_TaylorRows04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows04.lean), [`Triangular_Taylor_TaylorRows05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows05.lean), [`Triangular_Taylor_TaylorRows06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows06.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T026`, `OAIQ250T027`, `OAIQ250T028`, `OAIQ250T029`, `OAIQ250T030`, `OAIQ250T031`, `OAIQ250T032`, `OAIQ250T033`, `OAIQ250T034`, `OAIQ250T035`, `OAIQ250T036` and `OAIQ250T040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086`, `OAIQ250T109` and `OAIQ250T110`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T026
import Definitions.Def_OAIQ250T027
import Definitions.Def_OAIQ250T028
import Definitions.Def_OAIQ250T029
import Definitions.Def_OAIQ250T030
import Definitions.Def_OAIQ250T031
import Definitions.Def_OAIQ250T032
import Definitions.Def_OAIQ250T033
import Definitions.Def_OAIQ250T034
import Definitions.Def_OAIQ250T035
import Definitions.Def_OAIQ250T036
import Definitions.Def_OAIQ250T040

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

lemma real_function_nonneg_of_deleted {f : ℝ → ℝ} {m s : ℝ} (hfm : f m=0)
    (hdfm : deriv f m=0) (hb : 0≤deletedSecond f m s) : 0≤f s := by
  by_cases hsm : s=m
  · simp [hsm,hfm]
  · rw [deletedSecond_of_jets hfm hdfm hsm] at hb
    simpa only [zero_mul] using (le_div_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hsm))).mp hb
end AtomicTriangular.Construction
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
lemma cellFactors07 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 7 k j) ∧ cellBarrier 7 < ∏ j : Fin 15,(cellFactor 7 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 7 k j) ∧ cellBarrier 7 < ∏ j : Fin 15,(cellFactor 7 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

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
lemma taylorExp1_1_1_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 1)).exp = taylorExp1_1_1 j := by
  revert j
  decide +kernel
lemma taylorExp1_1_13_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 13)).exp = taylorExp1_1_13 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_1_0 : Fin 21 → Fin 8 → RI := ![tr0_1_0_0,tr0_1_0_1,tr0_1_0_2,tr0_1_0_3,tr0_1_0_4,tr0_1_0_5,tr0_1_0_6,tr0_1_0_7,tr0_1_0_8,tr0_1_0_9,tr0_1_0_10,tr0_1_0_11,tr0_1_0_12,tr0_1_0_13,tr0_1_0_14,tr0_1_0_15,tr0_1_0_16,tr0_1_0_17,tr0_1_0_18,tr0_1_0_19,tr0_1_0_20]
def tr0_1_1 : Fin 21 → Fin 8 → RI := ![tr0_1_1_0,tr0_1_1_1,tr0_1_1_2,tr0_1_1_3,tr0_1_1_4,tr0_1_1_5,tr0_1_1_6,tr0_1_1_7,tr0_1_1_8,tr0_1_1_9,tr0_1_1_10,tr0_1_1_11,tr0_1_1_12,tr0_1_1_13,tr0_1_1_14,tr0_1_1_15,tr0_1_1_16,tr0_1_1_17,tr0_1_1_18,tr0_1_1_19,tr0_1_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_3_0 : Fin 21 → Fin 8 → RI := ![tr0_3_0_0,tr0_3_0_1,tr0_3_0_2,tr0_3_0_3,tr0_3_0_4,tr0_3_0_5,tr0_3_0_6,tr0_3_0_7,tr0_3_0_8,tr0_3_0_9,tr0_3_0_10,tr0_3_0_11,tr0_3_0_12,tr0_3_0_13,tr0_3_0_14,tr0_3_0_15,tr0_3_0_16,tr0_3_0_17,tr0_3_0_18,tr0_3_0_19,tr0_3_0_20]
def tr0_3_1 : Fin 21 → Fin 8 → RI := ![tr0_3_1_0,tr0_3_1_1,tr0_3_1_2,tr0_3_1_3,tr0_3_1_4,tr0_3_1_5,tr0_3_1_6,tr0_3_1_7,tr0_3_1_8,tr0_3_1_9,tr0_3_1_10,tr0_3_1_11,tr0_3_1_12,tr0_3_1_13,tr0_3_1_14,tr0_3_1_15,tr0_3_1_16,tr0_3_1_17,tr0_3_1_18,tr0_3_1_19,tr0_3_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_4_1 : Fin 21 → Fin 8 → RI := ![tr0_4_1_0,tr0_4_1_1,tr0_4_1_2,tr0_4_1_3,tr0_4_1_4,tr0_4_1_5,tr0_4_1_6,tr0_4_1_7,tr0_4_1_8,tr0_4_1_9,tr0_4_1_10,tr0_4_1_11,tr0_4_1_12,tr0_4_1_13,tr0_4_1_14,tr0_4_1_15,tr0_4_1_16,tr0_4_1_17,tr0_4_1_18,tr0_4_1_19,tr0_4_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_5_0 : Fin 21 → Fin 8 → RI := ![tr0_5_0_0,tr0_5_0_1,tr0_5_0_2,tr0_5_0_3,tr0_5_0_4,tr0_5_0_5,tr0_5_0_6,tr0_5_0_7,tr0_5_0_8,tr0_5_0_9,tr0_5_0_10,tr0_5_0_11,tr0_5_0_12,tr0_5_0_13,tr0_5_0_14,tr0_5_0_15,tr0_5_0_16,tr0_5_0_17,tr0_5_0_18,tr0_5_0_19,tr0_5_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_6_1 : Fin 21 → Fin 8 → RI := ![tr0_6_1_0,tr0_6_1_1,tr0_6_1_2,tr0_6_1_3,tr0_6_1_4,tr0_6_1_5,tr0_6_1_6,tr0_6_1_7,tr0_6_1_8,tr0_6_1_9,tr0_6_1_10,tr0_6_1_11,tr0_6_1_12,tr0_6_1_13,tr0_6_1_14,tr0_6_1_15,tr0_6_1_16,tr0_6_1_17,tr0_6_1_18,tr0_6_1_19,tr0_6_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


