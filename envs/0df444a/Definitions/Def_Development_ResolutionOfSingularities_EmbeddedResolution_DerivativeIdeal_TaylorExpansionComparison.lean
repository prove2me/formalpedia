-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:48.675956+00:00
-- url     : https://prove2.me/theorems/85d6570f-ccde-4e64-a323-452858513660
-- title:
--   Taylor Expansion Comparison
-- statement:
--   Definitions and structural lemmas for Taylor Expansion Comparison, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution
section
variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
end
section
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]
end
section
open IsLocalRing
def IsTaylorExpansionOn (P : Type*) [CommRing P] {A R B : Type*} [CommRing A] [CommRing R]
    [CommRing B] [Algebra P R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ x : P,
    TaylorExpansion.truncatedSeries φ D β N (algebraMap P R x) - φ' (algebraMap P R x) ∈ maximalIdeal B ^ N
end
end FunctorialResolution.EmbeddedResolution


