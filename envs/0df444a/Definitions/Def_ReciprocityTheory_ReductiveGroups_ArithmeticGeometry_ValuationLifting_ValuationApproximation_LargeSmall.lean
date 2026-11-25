-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_LargeSmall
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_LargeSmall
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:16:58.105839+00:00
-- url     : https://prove2.me/theorems/3aef9bbc-a07a-4fb5-ac09-480f5df68d79
-- title:
--   Large Small
-- statement:
--   Definitions and structural lemmas for Large Small, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/LargeSmall.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Lift.VA
def PairSep : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ)) → (∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) →
    ∀ i j, i ≠ j → ∃ w, 1 < v i w ∧ v j w < 1
def LargeSmall : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, 1 < v i x) → (∀ i j, i ≠ j → ∃ w, 1 < v i w ∧ v j w < 1) →
    ∀ i, ∃ y, 1 < v i y ∧ ∀ j, j ≠ i → v j y < 1
def NearOne : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ y, 1 < v i y ∧ ∀ j, j ≠ i → v j y < 1) →
    ∀ i (ε : ι → WithZero (Multiplicative ℤ)), (∀ j, ε j ≠ 0) →
      ∃ z, v i z = 1 ∧ ∀ j, j ≠ i → v j z < ε j
def Assembly : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ)) →
    (∀ i (ε : ι → WithZero (Multiplicative ℤ)), (∀ j, ε j ≠ 0) →
      ∃ z, v i z = 1 ∧ ∀ j, j ≠ i → v j z < ε j) →
    ∀ n : ι → ℤ, ∃ x : Ω, ∀ i, v i x = WithZero.exp (n i)
end ReciprocityTheory.ChartRestriction.G.Lift.VA


