-- Prove2me | Definitions.Def_OAIQ262T111
-- name    : OAIQ262T111
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:57:52.924135+00:00
-- url     : https://prove2.me/theorems/eaa41fb3-77f7-49e7-8e52-4ed7e4caa1db
-- title:
--   Definitions bundle OAIQ262T111 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 5 definitions and 4 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.tr1_3_1`, `OAI.AtomicTriangular.FiniteCertificate.tr1_4_0`, `OAI.AtomicTriangular.FiniteCertificate.tr1_4_1`, `OAI.AtomicTriangular.FiniteCertificate.tr1_5_0`, `OAI.AtomicTriangular.FiniteCertificate.tr1_5_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_DeletedQuotient`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/DeletedQuotient.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean), [`Triangular_Taylor_TaylorExp01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp01.lean), [`Triangular_Taylor_TaylorRows13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows13.lean), [`Triangular_Taylor_TaylorRows14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows14.lean), [`Triangular_Taylor_TaylorRows15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows15.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T044`, `OAIQ262T059`, `OAIQ262T074`, `OAIQ262T075`, `OAIQ262T076`, `OAIQ262T077`, `OAIQ262T078`, `OAIQ262T079`, `OAIQ262T080` and `OAIQ262T081` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146`, `OAIQ262T190` and `OAIQ262T191`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T044
import Definitions.Def_OAIQ262T059
import Definitions.Def_OAIQ262T074
import Definitions.Def_OAIQ262T075
import Definitions.Def_OAIQ262T076
import Definitions.Def_OAIQ262T077
import Definitions.Def_OAIQ262T078
import Definitions.Def_OAIQ262T079
import Definitions.Def_OAIQ262T080
import Definitions.Def_OAIQ262T081

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_DeletedQuotient
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGrid2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors28 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 28 k j) ∧ cellBarrier 28 < ∏ j : Fin 15,(cellFactor 28 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 28 k j) ∧ cellBarrier 28 < ∏ j : Fin 15,(cellFactor 28 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors29 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 29 k j) ∧ cellBarrier 29 < ∏ j : Fin 15,(cellFactor 29 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 29 k j) ∧ cellBarrier 29 < ∏ j : Fin 15,(cellFactor 29 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_1_3_calc (j : Fin 31) : ((taylorPhase0_1 j).mul (CI.point 3)).exp = taylorExp0_1_3 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_3_1 : Fin 21 → Fin 8 → RI := ![tr1_3_1_0,tr1_3_1_1,tr1_3_1_2,tr1_3_1_3,tr1_3_1_4,tr1_3_1_5,tr1_3_1_6,tr1_3_1_7,tr1_3_1_8,tr1_3_1_9,tr1_3_1_10,tr1_3_1_11,tr1_3_1_12,tr1_3_1_13,tr1_3_1_14,tr1_3_1_15,tr1_3_1_16,tr1_3_1_17,tr1_3_1_18,tr1_3_1_19,tr1_3_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_4_0 : Fin 21 → Fin 8 → RI := ![tr1_4_0_0,tr1_4_0_1,tr1_4_0_2,tr1_4_0_3,tr1_4_0_4,tr1_4_0_5,tr1_4_0_6,tr1_4_0_7,tr1_4_0_8,tr1_4_0_9,tr1_4_0_10,tr1_4_0_11,tr1_4_0_12,tr1_4_0_13,tr1_4_0_14,tr1_4_0_15,tr1_4_0_16,tr1_4_0_17,tr1_4_0_18,tr1_4_0_19,tr1_4_0_20]
def tr1_4_1 : Fin 21 → Fin 8 → RI := ![tr1_4_1_0,tr1_4_1_1,tr1_4_1_2,tr1_4_1_3,tr1_4_1_4,tr1_4_1_5,tr1_4_1_6,tr1_4_1_7,tr1_4_1_8,tr1_4_1_9,tr1_4_1_10,tr1_4_1_11,tr1_4_1_12,tr1_4_1_13,tr1_4_1_14,tr1_4_1_15,tr1_4_1_16,tr1_4_1_17,tr1_4_1_18,tr1_4_1_19,tr1_4_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows15
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
def tr1_5_1 : Fin 21 → Fin 8 → RI := ![tr1_5_1_0,tr1_5_1_1,tr1_5_1_2,tr1_5_1_3,tr1_5_1_4,tr1_5_1_5,tr1_5_1_6,tr1_5_1_7,tr1_5_1_8,tr1_5_1_9,tr1_5_1_10,tr1_5_1_11,tr1_5_1_12,tr1_5_1_13,tr1_5_1_14,tr1_5_1_15,tr1_5_1_16,tr1_5_1_17,tr1_5_1_18,tr1_5_1_19,tr1_5_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


