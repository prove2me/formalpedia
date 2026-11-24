-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothPullbackLocalAmbientEmbedding
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothPullbackLocalAmbientEmbedding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:38.467396+00:00
-- url     : https://prove2.me/theorems/4a8473c4-2c4f-467d-ad07-89cc78dd9ee4
-- title:
--   Smooth Pullback Local Ambient Embedding
-- statement:
--   Definitions and structural lemmas for Smooth Pullback Local Ambient Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothPullbackLocalAmbientEmbedding.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def SmoothPullbackHasLocalAmbientEmbedding : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X Y A : Scheme.{u})
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pA : A ⟶ Spec (CommRingCat.of k)) [IsAffine A] [Smooth pA]
    [LocallyOfFiniteType pA] [QuasiCompact pA]
    (i : X ⟶ A) [IsClosedImmersion i], i ≫ pA = pX →
    ∀ (M c : ℕ) (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) [IsClosedImmersion ρ],
      ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA →
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) ρ c →
    ∀ (r : ℕ) (h : Y ⟶ X) [SmoothOfRelativeDimension r h], h ≫ pX = pY →
    ∀ y : Y,
      ∃ (V : Y.Opens) (_ : y ∈ V) (_ : IsAffineOpen V)
        (A' : Scheme.{u}) (pA' : A' ⟶ Spec (CommRingCat.of k)),
        IsAffine A' ∧ Smooth pA' ∧ LocallyOfFiniteType pA' ∧ QuasiCompact pA' ∧
        ∃ g : A' ⟶ A, Smooth g ∧ g ≫ pA = pA' ∧
          ∃ j : V.toScheme ⟶ A', IsClosedImmersion j ∧
            IsPullback j (V.ι ≫ h) g i ∧
            ∃ N₀ : ℕ, r ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
              ∃ σ : A' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin (M + N))),
                IsClosedImmersion σ ∧
                σ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin (M + N))) = pA' ∧
                HasSmoothCoordCodim
                  (affineSpaceIndexedByToSpec k (ULift.{u} (Fin (M + N)))) σ (c + (N - r))
end FunctorialResolution.EmbeddedResolution
end


