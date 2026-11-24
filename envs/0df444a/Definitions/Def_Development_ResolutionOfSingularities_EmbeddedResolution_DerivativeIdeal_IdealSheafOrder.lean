-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:25.961647+00:00
-- url     : https://prove2.me/theorems/49ba4c63-82c2-41f5-9c39-146db03982c2
-- title:
--   Ideal Sheaf Order
-- statement:
--   Definitions and structural lemmas for Ideal Sheaf Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
noncomputable def stalkIdeal (I : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  ⨆ U : {U : X.affineOpens // x ∈ U.1.1},
    Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1)
noncomputable def orderAt (I : X.IdealSheafData) (x : X) : ℕ∞ :=
  idealOrder (stalkIdeal I x)
noncomputable def orderAtLeastLocus (I : X.IdealSheafData) (m : ℕ) : Set X :=
  {x : X | (m : ℕ∞) ≤ orderAt I x}
end FunctorialResolution.EmbeddedResolution


