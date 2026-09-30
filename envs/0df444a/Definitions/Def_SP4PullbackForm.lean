-- Prove2me | Definitions.Def_SP4PullbackForm
-- name    : SP4PullbackForm
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-05T19:24:16.340085+00:00
-- url     : https://prove2.me/theorems/053d8167-4156-4fea-9e1c-b9f8281fd285
-- title:
--   The arbitrary-atlas transported formulation of smooth Poincaré
-- statement:
--   This defines the predicate asserting that, for every compact Hausdorff Type-0 smooth four-manifold N with an arbitrary given atlas and every homeomorphism e from N to the standard sphere, there exists a smooth-groupoid structomorphism from the given atlas to the atlas pulled back along e. Its underlying self-homeomorphism of N need not be the identity. The definition does not prove the predicate.
-- source:
--   Unpublished local Lean source SPC4.lean, SHA-256 b17fdb932034e5211d0db8171c08e2b3a182016bceaecdd2deb49c39d6bfd5cc; supported copy and exact oracle provenance in the accompanying local package.

-- Derived from frozen local sources; exact source/hash provenance in items.json.
import Definitions.Def_SP4Sphere
import Definitions.Def_SP4PullbackCharts

set_option autoImplicit false

namespace SP4Mission

open scoped Manifold ContDiff

noncomputable section

section Transport

variable {N : Type} [TopologicalSpace N]

def SPC4Pullback : Prop :=
  ∀ (N : Type) [TopologicalSpace N] [T2Space N] [CompactSpace N]
    [cs : ChartedSpace (EuclideanSpace ℝ (Fin 4)) N] [IsManifold (𝓡 4) ∞ N],
    ∀ e : N ≃ₜ S4,
      Nonempty (@Structomorph (EuclideanSpace ℝ (Fin 4)) _
        (contDiffGroupoid ∞ (𝓡 4)) N N _ _ cs e.sp4MissionPullbackChartedSpace)

end Transport

section Bridge

open Set ChartedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H'}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace H' X']
  {m : ℕ∞ω} [IsManifold I m X] [IsManifold I m X']

end Bridge

end

end SP4Mission


