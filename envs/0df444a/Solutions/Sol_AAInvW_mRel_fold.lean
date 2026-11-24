-- Prove2me | solution 1 for AAInvW.mRel_fold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:18:42.6893+00:00
-- url     : https://prove2.me/submissions/54e1b004-8bd9-478d-bd15-5b1a18df6d00

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel
import Theorems.Thm_AAInvW_mRel_top

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
theorem _root_.solution (hH : HInvol H) (l : List (Fin n × Fin n × ℂ)) {f : Matrix (Fin n) (Fin n) ℂ → E}
    {ψ : mSub H E} (h : mRel f ψ) :
    mRel ((l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.2.2 p.1 p.2.1).foldr (fun T h => T h) f)
      ((l.map fun p => Tm (mE hH) p.2.2 p.1 p.2.1).prod ψ) := by
  induction l with
  | nil => simpa using h
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    exact mRel_top hH ih _ _ _
end AAInvW
