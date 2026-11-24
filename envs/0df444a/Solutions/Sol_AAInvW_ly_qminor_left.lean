-- Prove2me | solution 1 for AAInvW.ly_qminor_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:55:13.01993+00:00
-- url     : https://prove2.me/submissions/0bcf1092-a4f6-479b-b54a-383203f609a3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_LyQminorLeft
import Theorems.Thm_AAInvW_ly_Top_left
import Theorems.Thm_AAInvW_ly_foldr_comm

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
    (H : Matrix (Fin n) (Fin n) ℂ) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (F : Matrix (Fin n) (Fin n) ℂ → E)
    (s x : Matrix (Fin n) (Fin n) ℂ) :
    qminorOp (EabH H) a b u (fun y => F (s * y)) x = qminorOp (EabH H) a b u F (s * x) := by
  unfold qminorOp
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Pi.smul_apply, Pi.smul_apply]
  congr 1
  rw [ly_foldr_comm (fun f y => f (s * y)) _ ?_ F]
  intro T hT f
  simp only [List.mem_ofFn, Set.mem_range] at hT
  obtain ⟨i, rfl⟩ := hT
  exact ly_Top_left H _ _ _ f s
end AAInvW
