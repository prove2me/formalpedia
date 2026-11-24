-- Prove2me | solution 1 for AAInvW.qminor_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:47:04.19414+00:00
-- url     : https://prove2.me/submissions/04783491-514a-480b-bc49-56f3fe191016

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdIntertwine
import Theorems.Thm_AAInvW_ofFn_prod_intertwine

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E E' : Fin n → Fin n → A) (ρ : A)
    (h : ∀ a b, E a b * ρ = ρ * E' a b) (a b : Fin t → Fin n) (u : ℂ) :
    qminor E a b u * ρ = ρ * qminor E' a b u := by
  unfold qminor
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [mul_assoc, ofFn_prod_intertwine ρ t _ _ (fun k => ?_), ← mul_assoc, ← mul_assoc,
    (Int.cast_commute _ ρ).eq]
  simp only [Tm, add_mul, mul_add, h]
  split_ifs
  · rw [Algebra.commutes]
  · rw [zero_mul, mul_zero]
end AAInvW
