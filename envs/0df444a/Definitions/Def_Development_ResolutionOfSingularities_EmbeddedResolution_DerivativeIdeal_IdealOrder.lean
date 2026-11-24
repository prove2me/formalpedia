-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:44.196933+00:00
-- url     : https://prove2.me/theorems/78149b91-acf6-48d1-8177-0b9c15bab5df
-- title:
--   Ideal Order
-- statement:
--   Definitions and structural lemmas for Ideal Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean

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
open IsLocalRing
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
noncomputable def idealOrder (I : Ideal R) : ℕ∞ :=
  sSup ((fun n : ℕ => (n : ℕ∞)) '' {n : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ n})
end FunctorialResolution.EmbeddedResolution


