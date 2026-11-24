-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensSpan
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:25.871817+00:00
-- url     : https://prove2.me/theorems/ef1de1bf-4abb-4a75-a251-0df66f655f1f
-- title:
--   Statements Twisted Dual Gens Span
-- statement:
--   Definitions and structural lemmas for Statements Twisted Dual Gens Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsTwistedDualGensSpan.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
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
def TwistedDualGensSpan.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Ω : Type) [Field Ω] [Algebra R Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B : ChartBundle R (segreVec y) N E)
    (a : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω E),
    IsTwistedDualGens y B a φ → ∀ c, segreVec y c ≠ 0 →
      Submodule.span Ω (Set.range φ) = ⊤
end
end GroundTheory.Heights₂.Heights.NumbersDVR


