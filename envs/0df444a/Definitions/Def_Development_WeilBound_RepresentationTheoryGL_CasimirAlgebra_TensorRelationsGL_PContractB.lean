-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractB
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:21.642283+00:00
-- url     : https://prove2.me/theorems/b7bc767c-e3c4-48d5-a1b7-76e230583b12
-- title:
--   PContract B
-- statement:
--   Definitions and structural lemmas for PContract B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PContractB.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractD
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
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
namespace PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
def semiS {ι Γ : Type} [Fintype ι] (m : ℕ) (τ0 : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (c : ι → ℤ) : Submodule ℂ (TV n M (Fin m)) where
  carrier := {ζ | ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ ζ = (∏ τ, (κ τ γ).det ^ c τ) • ζ}
  add_mem' := by
    intro a b ha hb γ
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha γ, hb γ, smul_add]
  zero_mem' := by
    intro γ
    simp
  smul_mem' := by
    intro r a ha γ
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_smul, ha γ, smul_comm]
end PositivityTheory.Rg.Cz.CtrX
end


