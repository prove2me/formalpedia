-- Prove2me | solution 1 for AAInvW.operator_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:51:41.126581+00:00
-- url     : https://prove2.me/submissions/c8e3dda3-c781-4f78-a70f-a237ec70253b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel
import Theorems.Thm_AAInvW_mE_gl
import Theorems.Thm_AAInvW_mQminor
import Theorems.Thm_AAInvW_mE_rho
import Theorems.Thm_P2M_AAInvW_smooth_right__23e71241d98e


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
namespace AAInvW
theorem _root_.solution : OpModel := by
  unfold OpModel
  intro E _ _ n H hH
  refine ⟨mSub H E, mCls (H := H), mE hH, mE_gl hH, ?_, ?_⟩
  · intro t a b u f g hg hf
    exact mQminor hH t a b u f g hg hf
  · intro s hs
    refine ⟨mRho hH s hs, ?_, ?_, ?_⟩
    · intro f hf
      have hf' : SmoothOnH H (fun x => f (x * s)) := smooth_right' n H E f s hH hs hf
      apply Subtype.ext
      funext x
      unfold mCls
      rw [dif_pos hf', dif_pos hf]
      rfl
    · intro ψ y hy y' hy' hyy
      subst hyy
      rfl
    · intro a b
      exact mE_rho hH s hs a b
end AAInvW
