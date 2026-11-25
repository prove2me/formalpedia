-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:11:09.13002+00:00
-- url     : https://prove2.me/theorems/2f596362-fba7-476e-a2b7-1c3bc2931da7
-- title:
--   Lift St
-- statement:
--   Definitions and structural lemmas for Lift St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/LiftSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Lift
def ApproxStatement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, v i x = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
    (∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) → ∀ n : ι → ℤ,
      ∃ x : Ω, ∀ i, v i x = ((Multiplicative.ofAdd (n i) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
end ReciprocityTheory.ChartRestriction.G.Lift


