-- Prove2me | solution 1 for AAInvW.ly_Top_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:34:48.689119+00:00
-- url     : https://prove2.me/submissions/381aee55-461e-4677-9915-55671bda7dcc

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
    (H : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E)
    (s : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.QuantumDeterminants.Top (EabH H) v a b (fun x => F (s * x)) = fun x => Formalism.QuantumDeterminants.Top (EabH H) v a b F (s * x) := by
  funext x
  simp only [Formalism.QuantumDeterminants.Top, EabH, RdV, Matrix.mul_assoc]
end AAInvW
