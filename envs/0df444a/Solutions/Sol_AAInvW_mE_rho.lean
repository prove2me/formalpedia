-- Prove2me | solution 1 for AAInvW.mE_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:33:57.002546+00:00
-- url     : https://prove2.me/submissions/3a01b764-7872-4e64-bded-75b06f8b7220

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel
import Theorems.Thm_AAInvW_mE_apply
import Theorems.Thm_AAInvW_ana_mul
import Theorems.Thm_AAInvW_eab_h_local
import Theorems.Thm_AAInvW_eab_h_right


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
theorem _root_.solution (hH : HInvol H) (s : Matrix (Fin n) (Fin n) ℂ) (hs : inUH H s) (a b : Fin n) :
    mE (E := E) hH a b * mRho hH s hs = mRho hH s hs * ∑ c, ∑ d, (s⁻¹ c a * s b d) • mE hH c d := by
  refine LinearMap.ext (fun φ => Subtype.ext (funext (fun x => ?_)))
  rw [Module.End.mul_apply, Module.End.mul_apply, mE_apply]
  have h1 : EabH H a b (mExt (mRho hH s hs φ).1) x.1 = EabH H a b (fun y => mExt φ.1 (y * s)) x.1 :=
    eab_h_local n H E _ _ a b x.1 hH (fun y hy => by
      show mExt _ y = mExt _ (y * s)
      rw [mExt_pos hy, mExt_pos (ana_mul hy hs)]
      rfl) x.2
  rw [h1, AAInvW.eab_h_right n H E (mExt φ.1) a b s x.1 hH φ.2 hs x.2]
  show _ = ((∑ c, ∑ d, (s⁻¹ c a * s b d) • mE hH c d) φ).1 ⟨x.1 * s, ana_mul x.2 hs⟩
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, mE_apply]
end AAInvW
