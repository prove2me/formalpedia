-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep
-- name    : Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:39.89073+00:00
-- url     : https://prove2.me/theorems/c48672bc-2627-4940-9c76-46498206892d
-- title:
--   Val Of Kind Indep
-- statement:
--   Definitions and structural lemmas for Val Of Kind Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace GlobalTheory.RowValueCheck
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
def emptyValue [NeZero d] (X : RowData C V d I J) (ν : WithTop ℝ) : RowValue X where
  nu := ν
  FF := fun _ => ∅
  VAL := fun _ _ h => absurd h (Set.notMem_empty _)
def Agree {σ : Type} (S : Set σ) (F F' : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, (∀ x, μ x ≠ 0 → x ∈ S) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ F'
def hOf (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) :
    Option (Fin 2 × ZMod d × ZMod d) → MvPowerSeries (WV I) C
  | some (g, a, a') => hL g a a'
  | none => 0
end GlobalTheory.RowValueCheck


