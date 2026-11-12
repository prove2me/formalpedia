-- Prove2me | Definitions.Def_OAIQ262T104
-- name    : OAIQ262T104
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:54:35.93263+00:00
-- url     : https://prove2.me/theorems/88ccb0d3-344b-4b3b-be8c-907e395de7d4
-- title:
--   Definitions bundle OAIQ262T104 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 definition and 10 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_1_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign3.lean), [`Triangular_Signs_GaussianDeleted`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/GaussianDeleted.lean), [`Triangular_Signs_OrdinaryComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/OrdinaryComparison.lean), [`Triangular_Signs_Signs01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs01.lean), [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T020`, `OAIQ262T034`, `OAIQ262T043`, `OAIQ262T045`, `OAIQ262T046` and `OAIQ262T047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146` and `OAIQ262T149`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T020
import Definitions.Def_OAIQ262T034
import Definitions.Def_OAIQ262T043
import Definitions.Def_OAIQ262T045
import Definitions.Def_OAIQ262T046
import Definitions.Def_OAIQ262T047

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_0_1_calc (j : Fin 31) : ((taylorPhase0_0 j).mul (CI.point 1)).exp = taylorExp0_0_1 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex3b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 5 r = ex3b5 r := by
  revert r
  decide +kernel
lemma ex3b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 6 r = ex3b6 r := by
  revert r
  decide +kernel
lemma ex3b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 7 r = ex3b7 r := by
  revert r
  decide +kernel
lemma ex3b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 8 r = ex3b8 r := by
  revert r
  decide +kernel
lemma ex3b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 9 r = ex3b9 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_GaussianDeleted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
lemma gaussian_deleted_formula {z m v : ℝ} (hz : 0<z) (hv : v≠0) :
    deletedSecond (gaussianG z) m (m+v)=
      Q 1*z*Real.exp ((1-m)/z)*(Real.exp (-v/z)-1+v/z)/v^2 := by
  rw [deletedSecond,ite_eq_right (by intro hh; apply hv; linarith : m+v≠m),(gaussianG_deriv hz m).deriv]
  simp only [gaussianG]
  rw [show (1-(m+v))/z=(1-m)/z+(-v/z) by ring,Real.exp_add]
  field_simp [hz.ne',hv]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Signs01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_1_0 : Fin 21 → Fin 8 → RI := ![bs0_1_0_0,bs0_1_0_1,bs0_1_0_2,bs0_1_0_3,bs0_1_0_4,bs0_1_0_5,bs0_1_0_6,bs0_1_0_7,bs0_1_0_8,bs0_1_0_9,bs0_1_0_10,bs0_1_0_11,bs0_1_0_12,bs0_1_0_13,bs0_1_0_14,bs0_1_0_15,bs0_1_0_16,bs0_1_0_17,bs0_1_0_18,bs0_1_0_19,bs0_1_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_OrdinaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma ordinaryOffset_actual (n : Fin 7) (z : ℝ) :
    (∑ r : Fin 8,ordinaryOffset n r*actualParameter z r)=
      if n.val=0 then Q 1/(2*Z) else if n.val=1 then (4/5)*Q 1*Real.exp (-2/z) else 0 := by
  fin_cases n <;> (first | (simp [ordinaryOffset,actualParameter,Fin.sum_univ_succ]; all_goals first | (norm_num [ordinaryOffset,actualParameter,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [ordinaryOffset,actualParameter,Fin.sum_univ_succ]; done) | norm_num [ordinaryOffset,actualParameter,Fin.sum_univ_succ])
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGrid1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors14 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 14 k j) ∧ cellBarrier 14 < ∏ j : Fin 15,(cellFactor 14 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 14 k j) ∧ cellBarrier 14 < ∏ j : Fin 15,(cellFactor 14 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors15 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 15 k j) ∧ cellBarrier 15 < ∏ j : Fin 15,(cellFactor 15 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 15 k j) ∧ cellBarrier 15 < ∏ j : Fin 15,(cellFactor 15 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


