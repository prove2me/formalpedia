-- Prove2me | solution 1 for AAInvW.ly_Eab_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:03:59.646285+00:00
-- url     : https://prove2.me/submissions/a236340d-90ee-4289-997a-72e0f066d22e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_LyQminorLeft

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
namespace AAInvW
theorem _root_.solution {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) (s : Matrix (Fin n) (Fin n) ℂ) :
    EabH H a b (fun x => F (s * x)) = fun x => EabH H a b F (s * x) := by
  funext x
  simp only [EabH, RdV, Matrix.mul_assoc]
end AAInvW
