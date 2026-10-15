-- Prove2me | Definitions.Def_Plasticity_Faces
-- name    : Plasticity_Faces
-- status  : Definition
-- author  : @scanstone
-- created : 2026-10-15T00:31:18.04871+00:00
-- url     : https://prove2.me/theorems/651c4dbb-3b45-48ed-845b-e610dc733dfc
-- title:
--   Faces of the unit ball contained in the sphere, and the conclusions of the face theorem
-- statement:
--   Let $E$ be a real normed space with closed unit ball $B$ and unit sphere $S$.
--   A **sphere face** (`IsSphereFace C`) is a nonempty convex set $C\subseteq S$ that is an extreme subset of $B$: whenever a point of $C$ lies in the open segment between two points of $B$, both points lie in $C$. Its **dimension** is $\dim\operatorname{span}(C-C)$, written `Module.finrank ℝ (vectorSpan ℝ C)`; its relative boundary $\partial C$ and relative interior are taken in its affine hull (`intrinsicFrontier`, `intrinsicInterior`).
--
--   For a map $F$ from the unit ball of $X$ to that of $Y$ and a sphere face $C$ of $B_Y$, `MatchesFace F C` states, for $D=B_X\cap F^{-1}(C)$: $D$ is a compact sphere face of $B_X$ of the same finite dimension as $C$; $B_X\cap F^{-1}(-C)=-D$; $B_X\cap F^{-1}(\partial C)=\partial D$; $B_X\cap F^{-1}(\operatorname{ext}C)=\operatorname{ext}D$; and $F(tD)=tC$ for $0\le t\le1$. It bundles the conclusions of the face theorem (card `Plasticity.Faces.matchesFace_of_finiteDimensional`) for use in lemma cards.
-- source:
--   This repository: expositions/faces/codirected_compactness.md §1 (faces, extreme subsets), expositions/faces/finite_faces_boundary_crossing.md §1 (Theorem 1); Mathlib's IsExtreme, Set.extremePoints, intrinsicFrontier and vectorSpan

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Plasticity: faces of the unit ball

A *sphere face* of the closed unit ball `B` of a real normed space is a nonempty convex subset
`C` of the unit sphere that is an extreme subset of `B`: if a point of `C` lies in the open
segment between two points of `B`, both points lie in `C`.
Its dimension is that of its affine span, `Module.finrank ℝ (vectorSpan ℝ C)`, and its relative
boundary and relative interior are Mathlib's `intrinsicFrontier ℝ C` and `intrinsicInterior ℝ C`.

`MatchesFace F C` collects, for a map `F` between unit balls and a face `C` of the target ball,
the conclusions of the face theorem about `D = B_X ∩ F⁻¹(C)`; it is used by the lemma cards of
the face theorem.
-/

namespace Plasticity

open scoped Pointwise

/-- `C` is a face of the closed unit ball of `E` contained in the unit sphere. -/
def IsSphereFace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) : Prop :=
  C.Nonempty ∧ Convex ℝ C ∧ C ⊆ Metric.sphere (0 : E) 1 ∧
    IsExtreme ℝ (Metric.closedBall (0 : E) 1) C

/-- The conclusions of the face theorem for a face `C` of the unit ball of `Y` and the set
`D = B_X ∩ F⁻¹(C)`: `D` is a compact sphere face of the same finite dimension,
`B_X ∩ F⁻¹(-C) = -D`, `F` matches relative boundaries and extreme points, and `F` maps `t • D`
onto `t • C` for `0 ≤ t ≤ 1`. -/
def MatchesFace {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y) (C : Set Y) : Prop :=
  IsSphereFace (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) ∧
    IsCompact (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) ∧
    FiniteDimensional ℝ (vectorSpan ℝ (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) ∧
    Module.finrank ℝ (vectorSpan ℝ (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) =
      Module.finrank ℝ (vectorSpan ℝ C) ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (-C) = -(Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (intrinsicFrontier ℝ C) =
      intrinsicFrontier ℝ (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) ∧
    Metric.closedBall (0 : X) 1 ∩ F ⁻¹' (C.extremePoints ℝ) =
      (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C).extremePoints ℝ ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, F '' (t • (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) = t • C

end Plasticity


