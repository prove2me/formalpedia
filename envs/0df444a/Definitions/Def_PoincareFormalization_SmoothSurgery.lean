-- Prove2me | Definitions.Def_PoincareFormalization_SmoothSurgery
-- name    : PoincareFormalization_SmoothSurgery
-- status  : Definition
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T19:54:50.993375+00:00
-- url     : https://prove2.me/theorems/a02db688-06b2-413e-b9d4-cebbe0d57f52
-- title:
--   Smooth $3$-manifolds, smooth connected sums, spherical space forms, and surgery decompositions
-- statement:
--   Defines the smooth $3$-manifold surgery decomposition interface used in Perelman's proof of the three-dimensional smooth Poincaré conjecture:
--
--   1. `SmoothThreeManifold`: a nonempty, connected, compact, Hausdorff smooth $3$-manifold without boundary.
--   2. `IsSmoothConnectedSum M A B`: $M$ is covered by two open subsets $U, V$ diffeomorphic to punctured copies $A \setminus \{p_A\}$ and $B \setminus \{p_B\}$ whose intersection $U \cap V$ is homeomorphic to the neck $S^2 \times \mathbb{R}$.
--   3. `IsSphericalSpaceForm M`: $M$ admits a finite-sheeted smooth covering map $p : \mathbb{S}^3 \to M$ that is locally a diffeomorphism.
--   4. `IsS1ProdS2 M`: $M$ is homeomorphic to $S^1 \times S^2$.
--   5. `IsStandardSmoothDecomposition M`: inductive predicate asserting that $M$ is built from $3$-spheres, spherical space forms, and $S^1 \times S^2$ handles by finitely many smooth connected sums.
-- source:
--   B. Kleiner and J. Lott, Notes on Perelman's papers, Geometry & Topology 12 (2008), https://arxiv.org/abs/math/0605667, Lemma 73.4 (p. 140), Proposition 77.2 (p. 146), and Lemma 81.2 (p. 160).

import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareFormalization

abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)
abbrev S3 : Type := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)
abbrev S2 : Type := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1)
abbrev S1 : Type := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (1 + 1))) 1)

/-- A nonempty, connected, compact, Hausdorff smooth 3-manifold without boundary. -/
structure SmoothThreeManifold where
  Carrier : Type
  topology : TopologicalSpace Carrier
  hausdorff : @T2Space Carrier topology
  charts : @ChartedSpace E3 _ Carrier topology
  smooth : let _ := topology; let _ := charts; IsManifold (𝓡 3) ∞ Carrier
  compact : @CompactSpace Carrier topology
  connected : @ConnectedSpace Carrier topology

attribute [instance] SmoothThreeManifold.topology SmoothThreeManifold.hausdorff
  SmoothThreeManifold.charts SmoothThreeManifold.smooth
  SmoothThreeManifold.compact SmoothThreeManifold.connected

/-- A smooth 3-manifold `M` is a **smooth connected sum** of `A` and `B` if `M` is covered
by two open subsets `U, V` diffeomorphic to punctured copies `A \ {p_A}` and `B \ {p_B}`
whose intersection `U ∩ V` is homeomorphic to the collar `S² × ℝ` (equivalently, `M` is
obtained by gluing `A \ B³` and `B \ B³` along their `S²` boundaries). -/
def IsSmoothConnectedSum (M A B : SmoothThreeManifold) : Prop :=
  ∃ (U V : TopologicalSpace.Opens M.Carrier) (pA : A.Carrier) (pB : B.Carrier),
    (U : Set M.Carrier) ∪ (V : Set M.Carrier) = Set.univ ∧
    Nonempty (U ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (⟨({pA}ᶜ : Set A.Carrier), isOpen_compl_singleton⟩ : TopologicalSpace.Opens A.Carrier)) ∧
    Nonempty (V ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (⟨({pB}ᶜ : Set B.Carrier), isOpen_compl_singleton⟩ : TopologicalSpace.Opens B.Carrier)) ∧
    Nonempty ((U ⊓ V : TopologicalSpace.Opens M.Carrier) ≃ₜ (S2 × ℝ))

/-- A `SmoothThreeManifold` is a **spherical space form** if it is diffeomorphic to a
quotient `S³ / Γ` by a finite group `Γ` acting freely, smoothly, and isometrically on `S³`
(modeled via a finite-sheeted smooth covering `S³ → M` that is locally a diffeomorphism). -/
def IsSphericalSpaceForm (M : SmoothThreeManifold) : Prop :=
  ∃ (p : S3 → M.Carrier), IsCoveringMap p ∧
    (∀ y : S3, ∃ e : OpenPartialHomeomorph S3 M.Carrier,
      y ∈ e.source ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      Set.EqOn p e e.source) ∧
    ∀ x : M.Carrier, Set.Finite (p ⁻¹' {x})

/-- A `SmoothThreeManifold` is **handle-like (`S¹ × S²`)** if it is homeomorphic to
`S¹ × S²` (and smooth). -/
def IsS1ProdS2 (M : SmoothThreeManifold) : Prop :=
  Nonempty (M.Carrier ≃ₜ (S1 × S2))

/-- Inductive predicate recording that `M` is diffeomorphic to a finite smooth connected
sum of copies of `S¹ × S²` and spherical space forms (with the empty sum being `S³`). -/
inductive IsStandardSmoothDecomposition : SmoothThreeManifold → Prop
  | sphere (M : SmoothThreeManifold) :
      Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ S3) → IsStandardSmoothDecomposition M
  | spherical (M : SmoothThreeManifold) :
      IsSphericalSpaceForm M → IsStandardSmoothDecomposition M
  | handle (M : SmoothThreeManifold) :
      IsS1ProdS2 M → IsStandardSmoothDecomposition M
  | sum (M A B : SmoothThreeManifold) :
      IsSmoothConnectedSum M A B →
      IsStandardSmoothDecomposition A →
      IsStandardSmoothDecomposition B →
      IsStandardSmoothDecomposition M

end PoincareFormalization


