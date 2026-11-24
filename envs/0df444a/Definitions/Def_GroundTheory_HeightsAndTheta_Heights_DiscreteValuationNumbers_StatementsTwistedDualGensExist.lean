-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:23.739662+00:00
-- url     : https://prove2.me/theorems/c9f954b1-a836-4ef4-b9b5-54b7b4ca89b0
-- title:
--   Statements Twisted Dual Gens Exist
-- statement:
--   Definitions and structural lemmas for Statements Twisted Dual Gens Exist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsTwistedDualGensExist.lean

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
def TwistedDualGensExist.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B : ChartBundle O (segreVec y) N E),
    ∃ a₁ : K → ℤ, ∀ a : K → ℤ, a₁ ≤ a →
      ∃ (M : ℕ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


