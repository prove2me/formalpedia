-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerLast
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerLast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:58.312016+00:00
-- url     : https://prove2.me/theorems/9339661f-0890-4955-9018-a636bb7137e6
-- title:
--   Imports Ter Last
-- statement:
--   Definitions and structural lemmas for Imports Ter Last, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsTerLast.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_JoinCoordAssocVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
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
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord assocDeg assocVar ptCoord ptFlagModel)
def JoinVerticalDivisorLeft.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (b : K ⊕ K' → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
    IsVertDiv O (mcIdeal O (joinCoord x z)) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x (joinCoord z w))) (assocDeg (K₂ := K₂) b)
      (rename (assocVar ι₂) f) (rename (assocVar ι₂) g)
end GroundTheory.Heights₂.Heights.NumbersDVR


