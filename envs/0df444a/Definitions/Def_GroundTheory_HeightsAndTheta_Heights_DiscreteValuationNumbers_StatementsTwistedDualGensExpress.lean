-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:01.997139+00:00
-- url     : https://prove2.me/theorems/ac786289-8326-4511-aa8e-2d02ef0d1976
-- title:
--   Statements Twisted Dual Gens Express
-- statement:
--   Definitions and structural lemmas for Statements Twisted Dual Gens Express, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsTwistedDualGensExpress.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreClosureNumber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def TwistedDualGensExpress.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (ϖ : R) (Ω : Type) [Field Ω] [Algebra R Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle R (segreVec y) N E),
    SameGenericFibre ϖ B B' →
    ∀ (a a' : K → ℤ) (M M' : ℕ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a φ → IsTwistedDualGens y B' a' φ' →
    ∀ c, segreVec y c ≠ 0 → ∀ m, ∃ (n : ℕ) (r : Fin M → Ω),
      (∀ l, r l ∈ chartRing R (segreVec y) c) ∧
      algebraMap R Ω ϖ ^ n • φ' m = ∑ l, (r l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k)) • φ l
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


