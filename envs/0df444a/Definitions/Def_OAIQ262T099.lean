-- Prove2me | Definitions.Def_OAIQ262T099
-- name    : OAIQ262T099
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:52:04.225688+00:00
-- url     : https://prove2.me/theorems/a2e42f2c-21be-4dde-9130-3a29d10af4cd
-- title:
--   Definitions bundle OAIQ262T099 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition and 11 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.tw0_0_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_PolytopeInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/PolytopeInterval.lean), [`Triangular_Signs_ExceptionalInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean), [`Triangular_Signs_RemainderSums3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums3.lean), [`Triangular_Signs_RemainderSums4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums4.lean), [`Triangular_Signs_RemainderSums5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums5.lean), [`Triangular_Signs_RemainderSums6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums6.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorWave000`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave000.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T006`, `OAIQ262T012`, `OAIQ262T015`, `OAIQ262T017`, `OAIQ262T018`, `OAIQ262T019`, `OAIQ262T022` and `OAIQ262T023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146` and `OAIQ262T148`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T006
import Definitions.Def_OAIQ262T012
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T017
import Definitions.Def_OAIQ262T018
import Definitions.Def_OAIQ262T019
import Definitions.Def_OAIQ262T022
import Definitions.Def_OAIQ262T023

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_PolytopeInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Bernstein

lemma polytope_polynomial_lower (n : ℕ) (a : Fin (n+1) → Fin 8 → ℝ) (m : ℝ)
    (hm : ∀ d, m < rowLower (bernsteinRows n a d))
    (e : Fin 8 → ℝ) (he : ParameterPolytope e) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    m < ∑ l : Fin (n+1), (∑ r : Fin 8, a l r*e r)*τ^l.val := by
  let c : ℕ → ℝ := fun l => if hl : l<n+1 then ∑ r : Fin 8, a ⟨l,hl⟩ r*e r else 0
  have hb : ∀ d < n+1, m < bernsteinCoefficient n c d := by
    intro d hd
    have hh := (hm ⟨d,hd⟩).trans_le (rowLower_le (bernsteinRows n a ⟨d,hd⟩) e he)
    rw [bernsteinRows_dot] at hh
    have heq : bernsteinCoefficient n c d =
        ∑ l : Fin (n+1), ((d.choose l.val:ℝ)/(n.choose l.val:ℝ))*(∑ r : Fin 8, a l r*e r) := by
      unfold bernsteinCoefficient
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [c,dite_eq_left l.isLt]
    rwa [heq]
  have hh := strict_bernstein_bound n c m hb hτ
  rw [← Fin.sum_univ_eq_sum_range] at hh
  simpa only [c,Fin.is_lt,dite_eq_left] using hh
end AtomicTriangular.Construction
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
def tw0_0_0 : Fin 21 → Fin 31 → CI := ![tw0_0_0_0,tw0_0_0_1,tw0_0_0_2,tw0_0_0_3,tw0_0_0_4,tw0_0_0_5,tw0_0_0_6,tw0_0_0_7,tw0_0_0_8,tw0_0_0_9,tw0_0_0_10,tw0_0_0_11,tw0_0_0_12,tw0_0_0_13,tw0_0_0_14,tw0_0_0_15,tw0_0_0_16,tw0_0_0_17,tw0_0_0_18,tw0_0_0_19,tw0_0_0_20]

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

lemma ep4 : (RI.point 4).Mem (4 : ℝ) := by simpa using RI.mem_point 4
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderConst3_1_calc : RI.sum (fun j : Fin 31 => (remainderData3_01 j).mul (columnNorm22 j))=remainderConst3_1 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderConst4_0_calc : RI.sum (fun j : Fin 31 => (remainderData4_00 j).mul (columnNorm22 j))=remainderConst4_0 := by decide +kernel
lemma remainderConst4_1_calc : RI.sum (fun j : Fin 31 => (remainderData4_01 j).mul (columnNorm22 j))=remainderConst4_1 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderConst5_0_calc : RI.sum (fun j : Fin 31 => (remainderData5_00 j).mul (columnNorm22 j))=remainderConst5_0 := by decide +kernel
lemma remainderConst5_1_calc : RI.sum (fun j : Fin 31 => (remainderData5_01 j).mul (columnNorm22 j))=remainderConst5_1 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderConst6_0_calc : RI.sum (fun j : Fin 31 => (remainderData6_00 j).mul (columnNorm22 j))=remainderConst6_0 := by decide +kernel
lemma remainderConst6_1_calc : RI.sum (fun j : Fin 31 => (remainderData6_01 j).mul (columnNorm22 j))=remainderConst6_1 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors04 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 4 k j) ∧ cellBarrier 4 < ∏ j : Fin 15,(cellFactor 4 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 4 k j) ∧ cellBarrier 4 < ∏ j : Fin 15,(cellFactor 4 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors05 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 5 k j) ∧ cellBarrier 5 < ∏ j : Fin 15,(cellFactor 5 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 5 k j) ∧ cellBarrier 5 < ∏ j : Fin 15,(cellFactor 5 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


