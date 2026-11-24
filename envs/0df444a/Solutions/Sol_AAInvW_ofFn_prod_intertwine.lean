-- Prove2me | solution 1 for AAInvW.ofFn_prod_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:28:22.898036+00:00
-- url     : https://prove2.me/submissions/bece68cd-a706-47d1-826b-1fffc5ee46d9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdIntertwine

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
theorem _root_.solution {A : Type*} [Ring A] (ρ : A) :
    ∀ (t : ℕ) (X Y : Fin t → A), (∀ k, X k * ρ = ρ * Y k) →
      (List.ofFn X).prod * ρ = ρ * (List.ofFn Y).prod := by
  intro t
  induction t with
  | zero =>
    intro X Y _
    simp
  | succ t ih =>
    intro X Y h
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      ih (fun i => X i.succ) (fun i => Y i.succ) (fun i => h i.succ), ← mul_assoc, h 0, mul_assoc]
end AAInvW
