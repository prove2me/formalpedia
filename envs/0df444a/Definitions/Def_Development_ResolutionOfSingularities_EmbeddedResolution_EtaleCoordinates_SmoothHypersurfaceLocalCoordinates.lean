-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:49:24.4068+00:00
-- url     : https://prove2.me/theorems/0d47fae1-6c17-4269-bb64-e0b3bdefa2b8
-- title:
--   Smooth Hypersurface Local Coordinates
-- statement:
--   Definitions and structural lemmas for Smooth Hypersurface Local Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
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
section
variable {P : Scheme.{u}}
variable {k : Type u} [Field k]
end
section
variable {X : Scheme.{u}} {k : Type u} [Field k]
end
section
variable {P : Scheme.{u}} {k : Type u} [Field k]
def HasLocalCoordsOnSmoothHypersurface (p : P ⟶ Spec (CommRingCat.of k)) (H : P.IdealSheafData)
    (N : List P.IdealSheafData) (Z : H.subscheme.IdealSheafData) : Prop :=
  ∀ x ∈ (Z.subschemeι ≫ H.subschemeι).ker.support,
    ∃ (U : P.Opens) (hU : IsAffineOpen U) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n)
      (j₀ : Fin n) (lab : ℕ → Option (Fin n)) (S : Finset (Fin n)),
      restrictIdeal H U = c.coordIdeal {j₀} ∧
      (∀ i, ∀ hi : i < N.length, lab i = none → restrictIdeal (N[i]'hi) U = ⊤) ∧
      (∀ i, ∀ hi : i < N.length, ∀ j : Fin n, lab i = some j →
        restrictIdeal (N[i]'hi) U = c.coordIdeal {j}) ∧
      (∀ i i' : ℕ, i < N.length → i' < N.length → ∀ j : Fin n,
        lab i = some j → lab i' = some j → i = i') ∧
      Z.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩ =
        Ideal.span
          ((fun j : Fin n =>
            (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord j)) ''
              (S : Set (Fin n)))
end
end FunctorialResolution.EmbeddedResolution


