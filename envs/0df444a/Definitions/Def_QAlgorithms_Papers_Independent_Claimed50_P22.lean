-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22
-- name    : QAlgorithms_Papers_Independent_Claimed50_P22
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:08:07.225129+00:00
-- url     : https://prove2.me/theorems/c301c854-c908-498e-86d8-74d9711c1c22
-- title:
--   Definitions for On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups
-- statement:
--   The objects the formalized statements of *On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups* (arXiv:1002.1602) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BastianiSmoothOn`: Definition 2.1, PDF pp. 6–7: a tower of all iterated directional derivatives on an open set, jointly continuous in the base point and all directions, including order zero. Limits use nonzero real increments.
--   - `BastianiAtlas`: Smooth-atlas compatibility in the real locally convex calculus, Section 2, PDF p. 7. Chart domains and targets are open by construction.
--   - `BastianiSmoothMap`: Vector-valued smoothness on a locally convex manifold, Section 2, PDF p. 7, tested on every chart of its smooth atlas.
--   - `BastianiSmoothKernel`: Smoothness on the product manifold in the product atlas; Theorem 7.1, PDF p. 21.
--   - `LocallyBoundedRepresentation`: Definition 3.1(f), PDF p. 8: a uniform operator-norm bound on an identity neighborhood. No topology on GL(V) is imposed.
--   - `ContinuousVectors`: Continuous vectors, Definition 3.1(b), PDF p. 8; a subtype of this set always carries the subspace topology from V.
--   - `NormalSubgroupFilter`: Section 12, PDF p. 36: a nonempty downward-directed family of closed normal subgroups, cofinal in identity neighborhoods.
--   - `FixedVectors`: Section 12, PDF p. 36: vectors fixed by every member of the given subgroup, for a unitary (or real orthogonal) representation.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, https://arxiv.org/abs/1002.1602v3

import Mathlib

/-!
Statements from K.-H. Neeb, arXiv:1002.1602v3.
The local calculus is Definition 2.1's jointly continuous directional calculus.
Deferred nodes are recorded in HARD.md. Compilation is pending batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

section DirectionalCalculus

variable {E : Type u} {F : Type v}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Definition 2.1, PDF pp. 6–7: a tower of all iterated directional
derivatives on an open set, jointly continuous in the base point and all
directions, including order zero. Limits use nonzero real increments. -/
def BastianiSmoothOn (U : Set E) (f : E → F) : Prop :=
  ∃ d : (n : ℕ) → E → (Fin n → E) → F,
    (∀ x ∈ U, d 0 x (fun i => Fin.elim0 i) = f x) ∧
    (∀ n, ContinuousOn (fun p : E × (Fin n → E) => d n p.1 p.2)
      (U ×ˢ (Set.univ : Set (Fin n → E)))) ∧
    (∀ n x, x ∈ U → ∀ (a : Fin n → E) (h : E),
      Tendsto (fun t : ℝ => t⁻¹ • (d n (x + t • h) a - d n x a))
        (𝓝[≠] (0 : ℝ)) (𝓝 (d (n + 1) x (Fin.snoc a h))))

/-- Sanity check: the zero map has the zero derivative tower, including order zero. -/
example (U : Set E) : BastianiSmoothOn U (fun _ : E => (0 : F)) := by
  refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
  · intro x hx
    rfl
  · intro n
    exact continuousOn_const
  · intro n x hx a h
    simpa only [sub_self, smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

variable {M : Type w} [TopologicalSpace M] [ChartedSpace E M]

/-- Smooth-atlas compatibility in the real locally convex calculus,
Section 2, PDF p. 7. Chart domains and targets are open by construction. -/
def BastianiAtlas : Prop :=
  ∀ c ∈ atlas E M, ∀ e ∈ atlas E M,
    BastianiSmoothOn (c.symm.trans e).source (c.symm.trans e)

/-- Vector-valued smoothness on a locally convex manifold, Section 2,
PDF p. 7, tested on every chart of its smooth atlas. -/
def BastianiSmoothMap (f : M → F) : Prop :=
  ∀ c ∈ atlas E M, BastianiSmoothOn c.target (fun x => f (c.symm x))

/-- Smoothness on the product manifold in the product atlas;
Theorem 7.1, PDF p. 21. -/
def BastianiSmoothKernel (K : M × M → F) : Prop :=
  ∀ c ∈ atlas E M, ∀ e ∈ atlas E M,
    BastianiSmoothOn (c.target ×ˢ e.target)
      (fun p : E × E => K (c.symm p.1, e.symm p.2))

/-- Sanity check: zero directions are retained, even at derivative order zero. -/
example (a : Fin 0 → E) (h : E) : Fin.snoc a h = fun _ => h := rfl

end DirectionalCalculus

section BanachRepresentations

variable {K : Type u} [RCLike K]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type w} [NormedAddCommGroup V] [NormedSpace K V]

/-- Definition 3.1(f), PDF p. 8: a uniform operator-norm bound on an
identity neighborhood. No topology on GL(V) is imposed. -/
def LocallyBoundedRepresentation (pi : G →* (V ≃L[K] V)) : Prop :=
  ∃ U : Set G, U ∈ 𝓝 (1 : G) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ U, ‖(pi g).toContinuousLinearMap‖ ≤ C

/-- Continuous vectors, Definition 3.1(b), PDF p. 8; a subtype of this
set always carries the subspace topology from V. -/
def ContinuousVectors (pi : G →* (V ≃L[K] V)) : Set V :=
  {v | Continuous (fun g : G => pi g v)}

/-- Sanity check: zero is a continuous vector for every representation. -/
example (pi : G →* (V ≃L[K] V)) : (0 : V) ∈ ContinuousVectors pi := by
  change Continuous (fun g : G => pi g 0)
  simpa only [map_zero] using (continuous_const : Continuous (fun _ : G => (0 : V)))

end BanachRepresentations

section SubgroupFilters

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {I : Type v}

/-- Section 12, PDF p. 36: a nonempty downward-directed family of
closed normal subgroups, cofinal in identity neighborhoods. -/
def NormalSubgroupFilter (N : I → Subgroup G) : Prop :=
  Nonempty I ∧
  (∀ i, (N i).Normal) ∧
  (∀ i, IsClosed (N i : Set G)) ∧
  (∀ i j, ∃ k, N k ≤ N i ∧ N k ≤ N j) ∧
  (∀ U : Set G, U ∈ 𝓝 (1 : G) → ∃ i, (N i : Set G) ⊆ U)

variable {K : Type w} [RCLike K]
variable {H : Type z} [NormedAddCommGroup H] [InnerProductSpace K H]

/-- Section 12, PDF p. 36: vectors fixed by every member of the given
subgroup, for a unitary (or real orthogonal) representation. -/
def FixedVectors (pi : G →* (H ≃ₗᵢ[K] H)) (N : Subgroup G) : Set H :=
  {v | ∀ g ∈ N, pi g v = v}

/-- Sanity check: zero belongs to every fixed-vector space. -/
example (pi : G →* (H ≃ₗᵢ[K] H)) (N : Subgroup G) :
    (0 : H) ∈ FixedVectors pi N := by
  intro g hg
  exact map_zero (pi g)

end SubgroupFilters

end QAlgorithms.Papers.Independent.Claimed50.P22


