-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:45.813619+00:00
-- url     : https://prove2.me/theorems/c02d0d9c-d4ad-4e0a-951f-f693fa0b759c
-- title:
--   Tuned Ideal
-- statement:
--   Definitions and structural lemmas for Tuned Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution
def tuningWeight (m : ℕ) (c : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range m, (m - j) * c j
section
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
def tuningMonomial (J : Ideal S) (m : ℕ) (c : ℕ → ℕ) : Ideal S :=
  ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j
def tunedIdeal (J : Ideal S) (m s : ℕ) : Ideal S :=
  ⨆ c : ℕ → ℕ, ⨆ _ : s ≤ tuningWeight m c, tuningMonomial k J m c
section
variable [Algebra ℚ S]
end
end
end FunctorialResolution.EmbeddedResolution


