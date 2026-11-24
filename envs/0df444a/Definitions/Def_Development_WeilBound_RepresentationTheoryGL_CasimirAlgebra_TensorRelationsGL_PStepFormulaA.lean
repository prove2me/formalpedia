-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:38.245399+00:00
-- url     : https://prove2.me/theorems/f002fd76-05a4-44ec-b18b-7009a5de2ff7
-- title:
--   PStep Formula A
-- statement:
--   Definitions and structural lemmas for PStep Formula A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one


set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz
namespace PStepFormula
section
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
end
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
def rot (n : ℕ) : Equiv.Perm (Fin (1 + n)) where
  toFun k := if h : (k : ℕ) < n then ⟨k + 1, by omega⟩ else ⟨0, by omega⟩
  invFun k := if h : (k : ℕ) = 0 then ⟨n, by omega⟩ else ⟨k - 1, by omega⟩
  left_inv k := by
    apply Fin.ext; by_cases h : (k : ℕ) < n <;> simp [h] <;> omega
  right_inv k := by
    apply Fin.ext
    by_cases h : (k : ℕ) = 0
    · simp [h]
    · have h' : (k : ℕ) - 1 < n := by omega
      simp [h, h']; omega
end PStepFormula
end PositivityTheory.Rg.Cz
end


