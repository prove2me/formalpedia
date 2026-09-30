-- Prove2me | Definitions.Def_SP4Sphere
-- name    : SP4Sphere
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-05T19:23:23.387379+00:00
-- url     : https://prove2.me/theorems/dcd344e5-0dc2-4e16-a372-067b2b95942a
-- title:
--   Standard four-sphere and smooth Poincaré predicates
-- statement:
--   The standard four-sphere is the unit sphere in Euclidean five-space. SPC4 says that every compact Hausdorff Type-0 manifold with a given boundaryless smooth real four-dimensional atlas, if homeomorphic to this sphere, is smoothly diffeomorphic to it. SPC4Homotopy replaces homeomorphism by homotopy equivalence. These are propositions, not proofs.
-- source:
--   Unpublished local Lean source SPC4.lean, SHA-256 b17fdb932034e5211d0db8171c08e2b3a182016bceaecdd2deb49c39d6bfd5cc; supported copy and exact oracle provenance in the accompanying local package.

-- Derived from frozen local sources; exact source/hash provenance in items.json.
import Mathlib

set_option autoImplicit false

namespace SP4Mission

open scoped Manifold ContDiff

noncomputable section

abbrev S4 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (4 + 1))) 1

def SPC4 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M],
    Nonempty (M ≃ₜ S4) →
    Nonempty (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ S4)

def SPC4Homotopy : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M],
    Nonempty (ContinuousMap.HomotopyEquiv M S4) →
    Nonempty (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ S4)

section Transport

variable {N : Type} [TopologicalSpace N]

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


