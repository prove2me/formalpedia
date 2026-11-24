-- Prove2me | solution 1 for AAInvW.mE_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:03.133194+00:00
-- url     : https://prove2.me/submissions/b6284467-c17a-4708-b8c2-5fa1c9c71665

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel

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
theorem _root_.solution (hH : HInvol H) (a b : Fin n) (φ : mSub H E) (x : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x}) :
    ((mE hH a b φ : mSub H E) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) x =
      EabH H a b (mExt φ.1) x.1 := rfl
end AAInvW
