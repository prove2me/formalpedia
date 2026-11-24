-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:37:43.07815+00:00
-- url     : https://prove2.me/theorems/2b335e88-5d03-406c-95f9-3ba9cb5373d3
-- title:
--   Irreducible Components Of Support
-- statement:
--   Definitions and structural lemmas for Irreducible Components Of Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IrreducibleComponentsOfSupport.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isClosed_of_maximal_irreducible_subset_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
structure IsIrreducibleComponentOfSupport {X : Scheme.{u}} (D : X.IdealSheafData) (C : Set X) : Prop where
  isIrreducible : IsIrreducible C
  maximal : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C
  subset_support : C ⊆ (D.support : Set X)
namespace IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
theorem isClosed (hC : IsIrreducibleComponentOfSupport D C) : IsClosed C :=
  isClosed_of_maximal_irreducible_subset_support D hC.isIrreducible hC.subset_support hC.maximal
end IsIrreducibleComponentOfSupport
namespace IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
variable {k : Type u} [Field k]
end IsIrreducibleComponentOfSupport
end FunctorialResolution.EmbeddedResolution


