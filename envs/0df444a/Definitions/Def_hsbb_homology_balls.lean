-- Prove2me | Definitions.Def_hsbb_homology_balls
-- name    : hsbb_homology_balls
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T12:15:10.108362+00:00
-- url     : https://prove2.me/theorems/564a9b8b-c5ab-403c-b565-7ce2f83391f5
-- title:
--   Homology spheres, homology balls, and bounding
-- statement:
--   Singular homology $H_n(X;\mathbb Z)$ and $H_n(X;\mathbb Q)$ of a topological space $X$, taken from Mathlib's singular homology functor with coefficients $\mathbb Z$ (resp. $\mathbb Q$).
--
--   A **closed topological 3-manifold** is a compact Hausdorff space admitting an atlas modelled on $\mathbb R^3$. It is an **integral homology 3-sphere** if
--   $$H_n(M;\mathbb Z) \cong H_n(S^3;\mathbb Z) \quad \text{for all } n \ge 0,$$
--   and a **rational homology 3-sphere** if the same holds with $\mathbb Q$ coefficients.
--
--   A **smooth 4-manifold with boundary** here is a compact Hausdorff space with a $C^\infty$ atlas modelled on the half-space $\{x\in\mathbb R^4 : x_0 \ge 0\}$; $\partial W$ is its manifold boundary. $W$ is an **integral (rational) homology 4-ball** if $H_n(W) \cong H_n(\mathrm{pt})$ for all $n$ with $\mathbb Z$ ($\mathbb Q$) coefficients.
--
--   A space $M$ **bounds a smooth integral homology ball** (resp. rational homology ball, contractible 4-manifold) if there is such a $W$ that is an integral homology ball (resp. rational homology ball, contractible) with $\partial W$ homeomorphic to $M$.
--
--   These are the basic notions of the question *which (rational) homology 3-spheres bound (rational) homology 4-balls?*
--
--   **Formalization Note.** Bounding only asks for a homeomorphism $\partial W \cong M$; since topological 3-manifolds have unique smooth structures (Moise), this is the standard notion. Orientations are not tracked: if $M$ bounds $W$ then $-M$ bounds $-W$. The 4-manifold is required to be smooth; in the topological category every integral homology 3-sphere bounds a contractible 4-manifold (Freedman).
-- source:
--   Open Problem Garden, 'Which homology 3-spheres bound homology 4-balls?' (rybu, 2009), http://www.openproblemgarden.org/op/which_homology_3_spheres_bound_homology_4_balls

import Mathlib

/-!
# Homology spheres and homology balls

Core vocabulary for the mission "Which homology 3-spheres bound homology 4-balls?"
(Open Problem Garden, posted by rybu, 2009).
-/

open scoped Manifold ContDiff

namespace HomologySpheresBoundBalls

/-- Singular homology `H_n(X; ℤ)` of a topological space, as a `ℤ`-module. -/
noncomputable def intHomology (n : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat.{0} ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

/-- Singular homology `H_n(X; ℚ)` of a topological space, as a `ℚ`-vector space. -/
noncomputable def ratHomology (n : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat.{0} ℚ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) n).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X)

/-- The round 3-sphere `S³ ⊆ ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- `M` is a closed topological 3-manifold: a compact Hausdorff space that is locally
homeomorphic to `ℝ³` (it admits an atlas modelled on `ℝ³`). -/
def IsClosedTop3Manifold (M : Type) [TopologicalSpace M] : Prop :=
  CompactSpace M ∧ T2Space M ∧ Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 3)) M)

/-- `M` is an integral homology 3-sphere: a closed topological 3-manifold with
`H_n(M; ℤ) ≅ H_n(S³; ℤ)` for every `n`. -/
def IsIntHomology3Sphere (M : Type) [TopologicalSpace M] : Prop :=
  IsClosedTop3Manifold M ∧ ∀ n : ℕ, Nonempty (intHomology n M ≅ intHomology n Sphere3)

/-- `M` is a rational homology 3-sphere: a closed topological 3-manifold with
`H_n(M; ℚ) ≅ H_n(S³; ℚ)` for every `n`. -/
def IsRatHomology3Sphere (M : Type) [TopologicalSpace M] : Prop :=
  IsClosedTop3Manifold M ∧ ∀ n : ℕ, Nonempty (ratHomology n M ≅ ratHomology n Sphere3)

/-- A compact smooth (`C^∞`) 4-manifold with boundary, modelled on the half-space
`{x ∈ ℝ⁴ | 0 ≤ x₀}`. -/
structure Smooth4ManifoldWithBoundary where
  /-- The underlying type. -/
  carrier : Type
  [top : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [compact : CompactSpace carrier]
  [charted : ChartedSpace (EuclideanHalfSpace 4) carrier]
  [smooth : IsManifold (𝓡∂ 4) ∞ carrier]

attribute [instance] Smooth4ManifoldWithBoundary.top Smooth4ManifoldWithBoundary.t2
  Smooth4ManifoldWithBoundary.compact Smooth4ManifoldWithBoundary.charted
  Smooth4ManifoldWithBoundary.smooth

namespace Smooth4ManifoldWithBoundary

/-- The manifold boundary `∂W`, with the subspace topology. -/
abbrev bdry (W : Smooth4ManifoldWithBoundary) : Type := (𝓡∂ 4).boundary W.carrier

/-- `W` is an integral homology 4-ball: `H_n(W; ℤ) ≅ H_n(pt; ℤ)` for every `n`. -/
def IsIntHomologyBall (W : Smooth4ManifoldWithBoundary) : Prop :=
  ∀ n : ℕ, Nonempty (intHomology n W.carrier ≅ intHomology n PUnit)

/-- `W` is a rational homology 4-ball: `H_n(W; ℚ) ≅ H_n(pt; ℚ)` for every `n`. -/
def IsRatHomologyBall (W : Smooth4ManifoldWithBoundary) : Prop :=
  ∀ n : ℕ, Nonempty (ratHomology n W.carrier ≅ ratHomology n PUnit)

end Smooth4ManifoldWithBoundary

/-- `M` bounds a smooth integral homology 4-ball: there is a compact smooth 4-manifold `W`
with boundary which is an integral homology ball and whose boundary is homeomorphic to `M`. -/
def BoundsIntHomologyBall (M : Type) [TopologicalSpace M] : Prop :=
  ∃ W : Smooth4ManifoldWithBoundary, W.IsIntHomologyBall ∧ Nonempty (W.bdry ≃ₜ M)

/-- `M` bounds a smooth rational homology 4-ball. -/
def BoundsRatHomologyBall (M : Type) [TopologicalSpace M] : Prop :=
  ∃ W : Smooth4ManifoldWithBoundary, W.IsRatHomologyBall ∧ Nonempty (W.bdry ≃ₜ M)

/-- `M` bounds a smooth contractible 4-manifold. -/
def BoundsContractible (M : Type) [TopologicalSpace M] : Prop :=
  ∃ W : Smooth4ManifoldWithBoundary, ContractibleSpace W.carrier ∧ Nonempty (W.bdry ≃ₜ M)

end HomologySpheresBoundBalls


