-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35
-- name    : QAlgorithms_Papers_Independent_Next46_P35
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:33:33.563979+00:00
-- url     : https://prove2.me/theorems/6a88864b-7523-467b-bf73-acc04fe1f45e
-- title:
--   Definitions for Pro-Lie groups which are infinite-dimensional Lie groups
-- statement:
--   The objects the formalized statements of *Pro-Lie groups which are infinite-dimensional Lie groups* (arXiv:math/0609684) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AmbientLocallyContractibleAt`: Definition 10.1(ii), PDF p. 39: one neighborhood contracts to the point in the ambient space. The homotopy need not stay inside the neighborhood.
--   - `DirectionalSmoothOn`: The locally convex smooth calculus used on PDF p. 2: jointly continuous iterated directional derivatives, on an open coordinate domain. The derivative-tower implementation follows pinned accepted Claimed50.P22.BastianiSmoothOn (line 24), without imposing a norm.
--   - `DirectionalAtlas`: PDF p. 2: compatibility of every actual atlas transition in locally convex directional calculus. Implementation follows accepted Claimed50.P22.BastianiAtlas (line 49).
--   - `DirectionalManifoldSmooth`: PDF p. 2: smooth manifold-valued maps, using both actual atlases. Continuity makes each coordinate domain open.
--   - `CarriesLocallyConvexLieStructure`: PDF p. 2: existence of a compatible Lie group structure over an arbitrary Hausdorff locally convex real model. The supplied topology on G is retained; no normability, countability, regularity, or exponential function is required.
--   - `CarriesFiniteDimensionalLieStructure`: PDF pp. 2,11: an existential finite-dimensional real smooth Lie structure, with charts for the given topology. Used only to define the finite-dimensional factors of a pro-Lie group; dimension zero is included.
--   - `IsProLieGroup`: PDF p. 6, Theorem 2.1: the closed-subgroup-of-an-arbitrary-product characterization of pro-Lie groups. The embedding retains the complete induced Hausdorff projective-limit topology, rather than merely an injective homomorphism.
--   - `CompactGroupSemisimple`: PDF p. 10, Proposition 3.4: semisimplicity in the compact connected Hausdorff group sense is total disconnectedness of the center. This admits infinite products of simple compact factors and does not assume a Lie structure.
-- source:
--   Pro-Lie groups which are infinite-dimensional Lie groups, arXiv:math/0609684v1, https://arxiv.org/abs/math/0609684v1

import Mathlib

/-!
Statements from Hofmann–Neeb, arXiv:math/0609684v1.
All new definitions are local to this paper. The directional-calculus body is
adapted, with provenance, from the pinned accepted Claimed50.P22 definitions;
that chunk is not imported. No frozen definition module is changed.
Compilation and independent moderation are pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Next46.P35

open Set Filter Topology
open scoped Manifold ContDiff

universe u v w z

/-- Definition 10.1(ii), PDF p. 39: one neighborhood contracts to the point
in the ambient space. The homotopy need not stay inside the neighborhood. -/
def AmbientLocallyContractibleAt {X : Type u} [TopologicalSpace X] (x : X) : Prop :=
  ∃ U : Set X, U ∈ 𝓝 x ∧
    ContinuousMap.Homotopic
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
      (ContinuousMap.const U x)

/-- Sanity: a singleton ambient space contracts at its unique point. -/
example {X : Type u} [TopologicalSpace X] [Subsingleton X] (x : X) :
    AmbientLocallyContractibleAt x := by
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  have h : (⟨Subtype.val, continuous_subtype_val⟩ : C((Set.univ : Set X), X)) =
      ContinuousMap.const (Set.univ : Set X) x := by
    ext y
    exact Subsingleton.elim _ _
  rw [h]

section DirectionalCalculus

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The locally convex smooth calculus used on PDF p. 2: jointly continuous
iterated directional derivatives, on an open coordinate domain.
The derivative-tower implementation follows pinned accepted
Claimed50.P22.BastianiSmoothOn (line 24), without imposing a norm. -/
def DirectionalSmoothOn (U : Set E) (f : E → F) : Prop :=
  ∃ d : (n : ℕ) → E → (Fin n → E) → F,
    (∀ x ∈ U, d 0 x (fun i => Fin.elim0 i) = f x) ∧
    (∀ n, ContinuousOn (fun p : E × (Fin n → E) => d n p.1 p.2)
      (U ×ˢ (Set.univ : Set (Fin n → E)))) ∧
    (∀ n x, x ∈ U → ∀ (a : Fin n → E) (h : E),
      Tendsto (fun t : ℝ => t⁻¹ • (d n (x + t • h) a - d n x a))
        (𝓝[≠] (0 : ℝ)) (𝓝 (d (n + 1) x (Fin.snoc a h))))

/-- Sanity: constants at zero have the zero derivative tower, also at order zero. -/
example (U : Set E) : DirectionalSmoothOn U (fun _ : E => (0 : F)) := by
  refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
  · intro x hx
    rfl
  · intro n
    exact continuousOn_const
  · intro n x hx a h
    simpa only [sub_self, smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

variable {M : Type w} {N : Type z}
variable [TopologicalSpace M] [TopologicalSpace N]
variable [ChartedSpace E M] [ChartedSpace F N]

/-- PDF p. 2: compatibility of every actual atlas transition in locally
convex directional calculus. Implementation follows accepted
Claimed50.P22.BastianiAtlas (line 49). -/
def DirectionalAtlas : Prop :=
  ∀ c ∈ atlas E M, ∀ e ∈ atlas E M,
    DirectionalSmoothOn (c.symm.trans e).source (c.symm.trans e)

/-- PDF p. 2: smooth manifold-valued maps, using both actual atlases.
Continuity makes each coordinate domain open. -/
def DirectionalManifoldSmooth (f : M → N) : Prop :=
  Continuous f ∧ ∀ c ∈ atlas E M, ∀ e ∈ atlas F N,
    DirectionalSmoothOn (c.target ∩ (fun x => f (c.symm x)) ⁻¹' e.source)
      (fun x => e (f (c.symm x)))

end DirectionalCalculus

/-- Sanity: the zero-dimensional singleton model has a compatible atlas
and every continuous map into its singleton manifold is smooth. -/
example : DirectionalAtlas (E := PUnit.{1}) (M := PUnit.{1}) ∧
    DirectionalManifoldSmooth (E := PUnit.{1}) (F := PUnit.{1}) (id : PUnit.{1} → PUnit.{1}) := by
  have hs : ∀ (U : Set PUnit.{1}) (f : PUnit.{1} → PUnit.{1}), DirectionalSmoothOn U f := by
    intro U f
    refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro x hx
      exact Subsingleton.elim _ _
    · intro n
      exact continuousOn_const
    · intro n x hx a h
      simpa only [sub_self, smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : PUnit.{1}))
          (𝓝[≠] (0 : ℝ)) (𝓝 (0 : PUnit.{1})))
  constructor
  · intro c hc e he
    exact hs _ _
  · refine ⟨continuous_id, ?_⟩
    intro c hc e he
    exact hs _ _

/-- PDF p. 2: existence of a compatible Lie group structure over an arbitrary
Hausdorff locally convex real model. The supplied topology on G is retained;
no normability, countability, regularity, or exponential function is required. -/
def CarriesLocallyConvexLieStructure (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ (E : Type u) (a : AddCommGroup E),
    letI := a
    ∃ m : Module ℝ E,
      letI := m
      ∃ t : TopologicalSpace E,
        letI := t
        IsTopologicalAddGroup E ∧ ContinuousSMul ℝ E ∧
          LocallyConvexSpace ℝ E ∧ T2Space E ∧
          ∃ c : ChartedSpace E G,
            letI := c
            letI : ChartedSpace (E × E) (G × G) := prodChartedSpace E G E G
            DirectionalAtlas (E := E) (M := G) ∧
              DirectionalManifoldSmooth (E := E × E) (F := E)
                (fun p : G × G => p.1 * p.2) ∧
              DirectionalManifoldSmooth (E := E) (F := E) (fun g : G => g⁻¹)

/-- Sanity: the trivial group admits the zero-dimensional locally convex model. -/
example : CarriesLocallyConvexLieStructure PUnit.{1} := by
  have hs : ∀ {A : Type} [AddCommGroup A] [Module ℝ A] [TopologicalSpace A]
      (U : Set A) (f : A → PUnit.{1}), DirectionalSmoothOn U f := by
    intro A a m t U f
    refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro x hx
      exact Subsingleton.elim _ _
    · intro n
      exact continuousOn_const
    · intro n x hx a h
      simpa only [sub_self, smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : PUnit.{1}))
          (𝓝[≠] (0 : ℝ)) (𝓝 (0 : PUnit.{1})))
  refine ⟨PUnit.{1}, (inferInstance : AddCommGroup PUnit.{1}), ?_⟩
  refine ⟨(inferInstance : Module ℝ PUnit.{1}), ?_⟩
  refine ⟨(inferInstance : TopologicalSpace PUnit.{1}), ?_⟩
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    (inferInstance : ChartedSpace PUnit.{1} PUnit.{1}), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro c hc e he
    exact hs _ _
  · refine ⟨continuous_const, ?_⟩
    intro c hc e he
    exact hs _ _
  · refine ⟨continuous_const, ?_⟩
    intro c hc e he
    exact hs _ _

/-- PDF pp. 2,11: an existential finite-dimensional real smooth Lie structure,
with charts for the given topology. Used only to define the finite-dimensional
factors of a pro-Lie group; dimension zero is included. -/
def CarriesFiniteDimensionalLieStructure (G : Type u) [Group G]
    [TopologicalSpace G] : Prop :=
  ∃ n : ℕ, ∃ c : ChartedSpace (Fin n → ℝ) G,
    letI := c
    LieGroup (modelWithCornersSelf ℝ (Fin n → ℝ)) ∞ G

/-- Sanity: a specified zero-dimensional smooth atlas witnesses existence. -/
example (G : Type u) [Group G] [TopologicalSpace G]
    [ChartedSpace (Fin 0 → ℝ) G]
    [LieGroup (modelWithCornersSelf ℝ (Fin 0 → ℝ)) ∞ G] :
    CarriesFiniteDimensionalLieStructure G :=
  ⟨0, inferInstance, inferInstance⟩

/-- PDF p. 6, Theorem 2.1: the closed-subgroup-of-an-arbitrary-product
characterization of pro-Lie groups. The embedding retains the complete induced
Hausdorff projective-limit topology, rather than merely an injective homomorphism. -/
def IsProLieGroup (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ (J : Type u) (F : J → Type u) (a : ∀ j, Group (F j))
      (t : ∀ j, TopologicalSpace (F j)),
    letI := a
    letI := t
    (∀ j, T2Space (F j)) ∧ (∀ j, IsTopologicalGroup (F j)) ∧
      (∀ j, CarriesFiniteDimensionalLieStructure (F j)) ∧
      ∃ f : G →* (∀ j, F j), IsClosedEmbedding f

/-- Sanity: the empty product presentation gives the trivial pro-Lie group. -/
example : IsProLieGroup PUnit.{1} := by
  let f : PUnit.{1} →* (PEmpty → PUnit.{1}) :=
    { toFun := fun _ _ => PUnit.unit
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  refine ⟨PEmpty, (fun _ => PUnit.{1}), (fun _ => inferInstance),
    (fun _ => inferInstance), ?_, ?_, ?_, f, ?_⟩
  · intro j
    exact PEmpty.elim j
  · intro j
    exact PEmpty.elim j
  · intro j
    exact PEmpty.elim j
  · refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · exact Subsingleton.elim _ _
    · intro x y h
      exact Subsingleton.elim _ _
    · have h : Set.range f = Set.univ := by
        ext x
        simp only [Set.mem_range, Set.mem_univ, iff_true]
        exact ⟨PUnit.unit, Subsingleton.elim _ _⟩
      rw [h]
      exact isClosed_univ

/-- PDF p. 10, Proposition 3.4: semisimplicity in the compact connected
Hausdorff group sense is total disconnectedness of the center. This admits
infinite products of simple compact factors and does not assume a Lie structure. -/
def CompactGroupSemisimple (S : Type u) [Group S] [TopologicalSpace S]
    [IsTopologicalGroup S] [T2Space S] [CompactSpace S] [ConnectedSpace S] : Prop :=
  TotallyDisconnectedSpace (Subgroup.center S)

/-- Sanity: the trivial compact connected group is semisimple. -/
example : CompactGroupSemisimple PUnit.{1} := by
  change TotallyDisconnectedSpace (Subgroup.center PUnit.{1})
  infer_instance

end QAlgorithms.Papers.Independent.Next46.P35


