-- Prove2me | solution 1 for AAInvW.mRel_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:57:15.589039+00:00
-- url     : https://prove2.me/submissions/21292f30-1282-4a34-9bbe-cc01f1ea6808

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel
import Theorems.Thm_AAInvW_mE_apply
import Theorems.Thm_AAInvW_eab_h_local
import Theorems.Thm_AAInvW_eab_h_smooth
import Theorems.Thm_AAInvW_smooth_local
import Theorems.Thm_P2M_AAInvW_smooth_linear__4ce59117e344


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
open scoped Classical
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
namespace AAInvW
theorem _root_.solution (hH : HInvol H) {G : Matrix (Fin n) (Fin n) ℂ → E} {ψ : mSub H E} (h : mRel G ψ)
    (v : ℂ) (a b : Fin n) : mRel (Formalism.QuantumDeterminants.Top (EabH H) v a b G) (Tm (mE hH) v a b ψ) := by
  obtain ⟨hs, hv⟩ := h
  have hE : SmoothOnH H (EabH H a b G) := eab_h_smooth n H E G a b hH hs
  refine ⟨?_, ?_⟩
  · by_cases hab : a = b
    · exact smooth_local n H E _ _
        (fun x _ => by simp only [Formalism.QuantumDeterminants.Top, if_pos hab]; exact add_comm _ _)
        (smooth_linear' n H E _ _ v hE hs)
    · exact smooth_local n H E _ _
        (fun x _ => by simp only [Formalism.QuantumDeterminants.Top, if_neg hab, zero_add]) hE
  · intro y hy
    have h1 : EabH H a b G y = EabH H a b (mExt ψ.1) y :=
      eab_h_local n H E _ _ a b y hH (fun x hx => by rw [hv x hx, mExt_pos hx]) hy
    simp only [Formalism.QuantumDeterminants.Top, Tm, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, mE_apply, h1, hv y hy]
    split_ifs <;> simp [Module.algebraMap_end_apply]
end AAInvW
