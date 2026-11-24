-- Prove2me | solution 1 for AAInvW.mQminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:35:11.724989+00:00
-- url     : https://prove2.me/submissions/7a87cdac-5af1-4f7a-b1b0-bfb16de41833

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel
import Theorems.Thm_AAInvW_mRel_fold

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
theorem _root_.solution (hH : HInvol H) (t : ℕ) (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUH H g) (hf : SmoothOnH H f) :
    qminorOp (EabH H) a b u f g =
      ((qminor (mE hH) a b u (mCls f) : mSub H E) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨g, hg⟩ := by
  have hc : mRel f (mCls (H := H) f) := by
    refine ⟨hf, fun y hy => ?_⟩
    unfold mCls
    rw [dif_pos hf]
  unfold qminorOp qminor
  rw [Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Pi.smul_apply, Module.End.mul_apply]
  have hfold := (mRel_fold hH (List.ofFn fun k : Fin t => (a (σ k), b k, u - ((k : ℕ) : ℂ))) hc).2 g hg
  simp only [List.map_ofFn, Function.comp_def] at hfold
  rw [hfold]
  simp [Int.cast_smul_eq_zsmul]
end AAInvW
