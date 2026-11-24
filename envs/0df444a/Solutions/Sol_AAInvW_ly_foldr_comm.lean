-- Prove2me | solution 1 for AAInvW.ly_foldr_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:30:35.382631+00:00
-- url     : https://prove2.me/submissions/dbe4d1c5-95ea-4642-801a-ec80585647ed

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
theorem _root_.solution {X E : Type*} (L : (X → E) → (X → E)) (l : List ((X → E) → (X → E)))
    (hl : ∀ T ∈ l, ∀ f, T (L f) = L (T f)) (f : X → E) :
    l.foldr (fun T h => T h) (L f) = L (l.foldr (fun T h => T h) f) := by
  induction l with
  | nil => rfl
  | cons T l ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hl T' (by simp [hT'])), hl T (by simp)]
end AAInvW
