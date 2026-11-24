-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivBalancedOrderLocus
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivBalancedOrderLocus
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:25.603485+00:00
-- url     : https://prove2.me/theorems/fae93807-ffd6-488d-aa06-22230d7f46bd
-- title:
--   Deriv Balanced Order Locus
-- statement:
--   Definitions and structural lemmas for Deriv Balanced Order Locus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivBalancedOrderLocus.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
  (I : X.IdealSheafData) (m : ℕ)
end FunctorialResolution.EmbeddedResolution


