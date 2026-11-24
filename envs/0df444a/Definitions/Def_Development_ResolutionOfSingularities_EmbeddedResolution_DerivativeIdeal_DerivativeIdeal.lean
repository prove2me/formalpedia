-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:42.302446+00:00
-- url     : https://prove2.me/theorems/f13c141f-3c39-4d4d-9a41-664ef2527832
-- title:
--   Derivative Ideal
-- statement:
--   Definitions and structural lemmas for Derivative Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution
def derivIdeal (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ D : Derivation k S S, ∃ y ∈ J, D y = x}
def derivIdealIterate (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S] :
    ℕ → Ideal S → Ideal S
  | 0, J => J
  | r + 1, J => derivIdeal k (derivIdealIterate k r J)
end FunctorialResolution.EmbeddedResolution


