-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WeilBasisExistence
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WeilBasisExistence
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:35:22.274827+00:00
-- url     : https://prove2.me/theorems/7f476f5b-568c-42bd-8b8a-b52c363becca
-- title:
--   Weil Basis Existence
-- statement:
--   Definitions and structural lemmas for Weil Basis Existence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/WeilBasisExistence.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HGZeroRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScRefExists_WB_hG_add_right
import Theorems.Thm_PI_ScRefExists_WB_hG_smul_right
import Theorems.Thm_PI_ScRefExists_WB_hG_zero_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
namespace PI.ScRefExists.WB
variable (I : Formalism.MainNotions.S.AutInst)
theorem smul_Ap {p : ℕ} (c : Ap I p) (x : Fin I.n → I.E) : c • x = (c : I.E) • x := rfl
def WA (p r : ℕ) (e f : Fin r → Fin I.n → I.E) : Submodule (Ap I p) (Fin I.n → I.E) :=
  LA I p ⊓
  { carrier := {x | ∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0}
    add_mem' := by
      intro x y hx hy
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      intro a
      exact ⟨by rw [hG_add_right, (hx a).1, (hy a).1, add_zero],
        by rw [hG_add_right, (hx a).2, (hy a).2, add_zero]⟩
    zero_mem' := by
      simp only [Set.mem_setOf_eq]
      intro a
      exact ⟨hG_zero_right I _, hG_zero_right I _⟩
    smul_mem' := by
      intro c x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      intro a
      exact ⟨by rw [smul_Ap, hG_smul_right, (hx a).1, mul_zero],
        by rw [smul_Ap, hG_smul_right, (hx a).2, mul_zero]⟩ }
end PI.ScRefExists.WB


