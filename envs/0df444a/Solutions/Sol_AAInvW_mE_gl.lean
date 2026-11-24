-- Prove2me | solution 1 for AAInvW.mE_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:57:14.970276+00:00
-- url     : https://prove2.me/submissions/db644aca-246c-4d6a-b375-9cdda1aecd0c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OperatorModel
import Theorems.Thm_AAInvW_mE_apply
import Theorems.Thm_AAInvW_conjugated_generator_gl_relation
import Theorems.Thm_AAInvW_eab_h_local


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
theorem _root_.solution (hH : HInvol H) : GlRel (mE (E := E) hH) := by
  intro a b c d
  have key : ∀ (a b c d : Fin n) (φ : mSub H E) (x : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x}),
      (mE hH a b (mE hH c d φ)).1 x = EabH H a b (EabH H c d (mExt φ.1)) x.1 := by
    intro a b c d φ x
    rw [mE_apply]
    exact eab_h_local n H E _ _ a b x.1 hH (fun y hy => by rw [mExt_pos hy, mE_apply]) x.2
  refine LinearMap.ext (fun φ => Subtype.ext (funext (fun x => ?_)))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]
  rw [key, key, AAInvW.conjugated_generator_gl_relation n H E (mExt φ.1) a b c d x.1 hH φ.2 x.2]
  split_ifs <;> simp [mE_apply]
end AAInvW
