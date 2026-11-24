-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LeadingForm
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LeadingForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:26.707847+00:00
-- url     : https://prove2.me/theorems/9fb6bd8f-c3c1-4ce2-a052-c2a40a9b7b69
-- title:
--   Leading Form
-- statement:
--   Definitions and structural lemmas for Leading Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LeadingForm.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
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
def multiIndicesOfDegree (h r : ℕ) : Finset (Fin h → ℕ) :=
  (Fintype.piFinset fun _ : Fin h => Finset.range (r + 1)).filter fun β => ∑ i, β i = r
def ofDigitsFin (N : ℕ) {h : ℕ} (β : Fin h → ℕ) : ℕ := ∑ i, β i * N ^ (i : ℕ)
end FunctorialResolution.EmbeddedResolution


