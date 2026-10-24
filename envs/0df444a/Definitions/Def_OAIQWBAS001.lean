-- Prove2me | Definitions.Def_OAIQWBAS001
-- name    : OAIQWBAS001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T21:10:13.331805+00:00
-- url     : https://prove2.me/theorems/dfad3405-b743-40e8-ac9c-4c25481b4314
-- title:
--   OpenAI Bass trace split: definitions bundle OAIQWBAS001
-- statement:
--   One of the three definitions bundles (`OAIQWBAS000`, `OAIQWBAS001`, `OAIQWBAS002`) of the split of OpenAI's proof of the complex group-ring Bass trace conjecture: the Hattori–Stallings trace of every class in $K_0(\mathbb C[G])$ vanishes on the conjugacy classes of infinite-order elements (`OAI.BassTrace.RightProjective.bassTraceModules_vanishing_and_support`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/RingTheory/BassTrace` (OpenAI, *The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture*, OpenAI Math Release, September 24, 2026, result family 207, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. Among them are the exterior chain complexes and their relabelings, the graph metric and the transport distance on finitely supported probability vectors, separating filtrations with their simplexwise areas, and the path sums of an idempotent matrix. The bundles split the material only to keep each one within the platform's compile limits.
--
--   The definitions of the published statement (`ModuleK0`, `HattoriStallings` and the rest) are not repeated: the bundles import them from the published bundle `Def_BassTrace`. It imports no other bundle of this split.
--
--   Modules (some only in part): `ActivatedUnions`, `AffineCoarea`, `AffinePotentials`, `BallGeometry`, `CellTriangulation`, `DirectedCuts`, `FacetGeometry`, `GeometricSubcomplexes`, `GraphCounting`, `GraphRealization`, `Incidence`, `LocalCuts`, `MarkedArea`, `MarkedSubdivisions`, `OrbitAreas`, `SimplexCoordinates`, `SimplexMeasures`, `SimplexVolume`, `SubdivisionWeights`, `SupportGeometry`, `TraceCoefficients`, `TreeArea`, `TreeDeterminants`, `VolumeBounds`.
--
--   The theorems the definitions do not need are proved in the four solutions of this split. Two prove the published intermediate statements `OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound` and `OAI.BassTrace.Sparse.vanishing_of_zero_strata`. The third proves the matrix form `OAI.BassTrace.bassTrace` from them, and the fourth proves `OAI.BassTrace.RightProjective.bassTraceModules_vanishing_and_support` from that. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 207; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/BassTrace at commit adc7f12

import Mathlib
import Definitions.Def_BassTrace

section
-- module Solutions.OAIQW_BassTrace.TraceCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace

open scoped Classical

noncomputable def idempotentTraceCoefficient {G : Type*} [Group G]
    {q : ℕ} (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) (g : G) : ℂ :=
  classCoefficient g (Matrix.trace e)

end BassTrace

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.Incidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.Orientation

section

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def facetForm (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ)) : (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun x => Matrix.detRowAlternating.curryLeft x v
    map_add' := fun x y => by simp
    map_smul' := fun c x => by simp }

@[simp] lemma facetForm_apply (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ))
    (x : Fin (n+1) → ℝ) : facetForm n v x = Matrix.det (Fin.cons x v) := rfl

end

open scoped BigOperators

end Sparse.Orientation

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.FacetGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Two-sided facet incidence inside a single affine carrier, without a manifold hypothesis. -/

namespace BassTrace.Sparse

open Set Finset

open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) : Finset E :=
  (hK.toFinset.biUnion id).filter (fun u => u ∉ F ∧ insert u F ∈ K.faces)

@[simp] lemma mem_facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) (u : E) : u ∈ facetApexes K hK F ↔ u ∉ F ∧ insert u F ∈ K.faces := by
  simp only [facetApexes,Finset.mem_filter,Finset.mem_biUnion,Set.Finite.mem_toFinset,id_eq]
  exact ⟨fun h => h.2,fun h => ⟨⟨insert u F,h.2,Finset.mem_insert_self _ _⟩,h⟩⟩

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.CellTriangulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in

lemma simplex_affine_indicator (s t : Finset V)
    (hi : AffineIndependent ℝ ((↑) : s → V)) :
    ∃ f : V →ᵃ[ℝ] ℝ, ∀ x ∈ s, f x = if x ∈ t then 1 else 0 := by
  classical
  obtain ⟨u, hsu, huind, hutop⟩ := exists_subset_affineIndependent_affineSpan_eq_top hi
  let B : AffineBasis u ℝ V := ⟨Subtype.val, huind, by simpa using hutop⟩
  let T : Finset u := t.preimage Subtype.val Subtype.val_injective.injOn
  refine ⟨∑ i ∈ T, B.coord i, ?_⟩
  intro x hx
  let i : u := ⟨x, hsu hx⟩
  have hsum (R : Finset u) : (∑ j ∈ R, B.coord j) (B i) =
      ∑ j ∈ R, B.coord j (B i) := by
    induction R using Finset.induction_on with
    | empty => simp
    | @insert j R hj ih => simp [Finset.sum_insert hj, ih]
  change (∑ j ∈ T, B.coord j) (B i) = _
  rw [hsum]
  simp [T, B.coord_apply, i]

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.DirectedCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section ArbitraryAmbientComplex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_finite_coordinate_patch (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) :
    ∃ U : Submodule ℝ V, FiniteDimensional ℝ U ∧
      ∀ s ∈ K.faces, (s : Set V) ⊆ Set.range U.subtype := by
  let S : Finset V := hK.toFinset.biUnion id
  let U : Submodule ℝ V := Submodule.span ℝ (S : Set V)
  refine ⟨U, FiniteDimensional.span_of_finite ℝ S.finite_toSet, ?_⟩
  intro s hs x hx
  have hxS : x ∈ S := Finset.mem_biUnion.mpr ⟨s, by simpa using hs, hx⟩
  exact ⟨⟨x, Submodule.subset_span hxS⟩, rfl⟩

end ArbitraryAmbientComplex

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def directedUnionComplex {I : Type*} (K : I → Geometry.SimplicialComplex ℝ V)
    (hK : Directed (· ≤ ·) K) : Geometry.SimplicialComplex ℝ V where
  faces := {s | ∃ i, s ∈ (K i).faces}
  indep := by
    rintro s ⟨i, hi⟩
    exact (K i).indep hi
  isRelLowerSet_faces := by
    rintro s ⟨i, hi⟩
    exact ⟨(K i).nonempty_of_mem_faces hi, fun t hts ht =>
      ⟨i, (K i).down_closed hi hts ht⟩⟩
  inter_subset_convexHull := by
    rintro s t ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := hK i j
    exact (K k).inter_subset_convexHull (hik hi) (hjk hj)

lemma directedUnionComplex_space {I : Type*} (K : I → Geometry.SimplicialComplex ℝ V)
    (hK : Directed (· ≤ ·) K) : (directedUnionComplex K hK).space = ⋃ i, (K i).space := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, Set.mem_iUnion]
  exact ⟨fun ⟨s, ⟨i, hs⟩, hx⟩ => ⟨i, s, hs, hx⟩,
    fun ⟨i, s, hs, hx⟩ => ⟨s, ⟨i, hs⟩, hx⟩⟩

def finitePatch (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) : Geometry.SimplicialComplex ℝ V where
  faces := {s | s.Nonempty ∧ ∃ t ∈ A, s ⊆ t}
  indep := by
    rintro s ⟨hs, t, ht, hst⟩
    exact K.indep (K.down_closed (hA t ht) hst hs)
  isRelLowerSet_faces := by
    rintro s ⟨hs, t, ht, hst⟩
    exact ⟨hs, fun u hus hu => ⟨hu, t, ht, hus.trans hst⟩⟩
  inter_subset_convexHull := by
    rintro s t ⟨hs, u, hu, hsu⟩ ⟨ht, v, hv, htv⟩
    exact K.inter_subset_convexHull (K.down_closed (hA u hu) hsu hs)
      (K.down_closed (hA v hv) htv ht)

lemma finitePatch_finite (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) :
    (finitePatch K A hA).faces.Finite := by
  classical
  apply (A.biUnion Finset.powerset).finite_toSet.subset
  rintro s ⟨_, t, ht, hst⟩
  exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_powerset.mpr hst⟩

lemma finitePatch_mono (K : Geometry.SimplicialComplex ℝ V)
    {A B : Finset (Finset V)} (hA : ∀ s ∈ A, s ∈ K.faces) (hB : ∀ s ∈ B, s ∈ K.faces)
    (hAB : A ⊆ B) : finitePatch K A hA ≤ finitePatch K B hB := by
  rintro s ⟨hs, t, ht, hst⟩
  exact ⟨hs, t, hAB ht, hst⟩

lemma mem_finitePatch (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) {s : Finset V} (hs : s ∈ A) :
    s ∈ (finitePatch K A hA).faces :=
  ⟨K.nonempty_of_mem_faces (hA s hs), s, hs, Finset.Subset.refl s⟩

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.LocalCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section LocallyFiniteCuts

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma finiteComplex_space_finiteHull (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) (hc : Convex ℝ K.space) :
    ∃ s : Finset V, K.space = convexHull ℝ (s : Set V) := by
  classical
  let s : Finset V := hK.toFinset.biUnion id
  refine ⟨s, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨t, ht, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    apply convexHull_mono (t := (s : Set V)) ?_ hx
    intro y hy
    exact Finset.mem_biUnion.mpr ⟨t, by simpa using ht, hy⟩
  · apply convexHull_min ?_ hc
    intro x hx
    obtain ⟨t, ht, hx⟩ := Finset.mem_biUnion.mp hx
    exact K.subset_space (by simpa using ht) hx

end LocallyFiniteCuts

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.GeometricSubcomplexes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

/-! Local finiteness passes to a simplexwise finite subdivision. -/

namespace Sparse.Cuts

/-! Geometric subcomplexes used by the compatible-cut lemma. A marked subset
is a union of closed simplices, not necessarily the full complex induced by
its old vertices. Keeping this distinction is essential for unions of levels. -/

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

open scoped Classical

structure UniversalCuts (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (J : Type*) where
  form : J → V →ₗ[ℝ] ℝ
  level : J → ℝ
  positive : ∀ j, 0 < level j
  relevant : Finset V → Finset J
  vanish : ∀ s j, j ∉ relevant s →
    ∀ x ∈ convexHull ℝ (s : Set V), form j x = 0

end Sparse.Cuts

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.MarkedSubdivisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V}

namespace UniversalCuts

variable {J : Type*} (d : UniversalCuts V J)

def closedPatch (P : Set V) (A : Finset J) : Set V :=
  P ∩ {x | ∀ j ∈ A, d.form j x ≤ d.level j}

def outerPatch (P : Set V) (A : Finset J) : Set V :=
  P ∩ {x | ∃ j ∈ A, d.level j ≤ d.form j x}

def spherePatch (P : Set V) (A : Finset J) : Set V :=
  d.closedPatch P A ∩ {x | ∃ j ∈ A, d.form j x = d.level j}

end UniversalCuts

end

open Set Finset

open scoped Classical Topology

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

namespace MarkedFamily

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in

lemma locallyConstant_active_union {I : Type*} (A : I → Set V) (B : I → Set X)
    (hB : ∀ i, IsClopen (B i)) (Q : Set V)
    (hfinite : {i | (A i ∩ Q).Nonempty}.Finite) :
    IsLocallyConstant (fun x => (⋃ i, if x ∈ B i then A i else ∅) ∩ Q) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hp (i : I) : ∀ᶠ y in 𝓝 x, (y ∈ B i ↔ x ∈ B i) := by
    by_cases hx : x ∈ B i
    · exact Filter.Eventually.mono ((hB i).2.mem_nhds hx) (by intro y hy; exact ⟨fun _ => hx, fun _ => hy⟩)
    · exact Filter.Eventually.mono ((hB i).1.isOpen_compl.mem_nhds hx)
        (by intro y hy; exact ⟨fun h => False.elim (hy h), fun h => False.elim (hx h)⟩)
  filter_upwards [hfinite.eventually_all.mpr (fun i _ => hp i)] with y hy
  ext p
  simp only [Set.mem_inter_iff,Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i,hi⟩,hpQ⟩
    by_cases hyB : y ∈ B i
    · simp only [hyB,ite_true] at hi
      have hxB := (hy i ⟨p,hi,hpQ⟩).mp hyB
      exact ⟨⟨i,by simpa only [hxB,ite_true] using hi⟩,hpQ⟩
    · simp only [hyB,ite_false,Set.mem_empty_iff_false] at hi
  · rintro ⟨⟨i,hi⟩,hpQ⟩
    by_cases hxB : x ∈ B i
    · simp only [hxB,ite_true] at hi
      have hyB := (hy i ⟨p,hi,hpQ⟩).mpr hxB
      exact ⟨⟨i,by simpa only [hyB,ite_true] using hi⟩,hpQ⟩
    · simp only [hxB,ite_false,Set.mem_empty_iff_false] at hi

end MarkedFamily

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.ActivatedUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

section

open Set Finset

open scoped Classical Topology

variable {V X I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

def activatedUnion (A : I → Set V) (B : I → Set X) (x : X) : Set V :=
  ⋃ i, if x ∈ B i then A i else ∅

def replacementSet (P Z : Set V) (U S : I → Set V) (B : I → Set X) (x : X) : Set V :=
  (Z \ activatedUnion U B x) ∪ (P ∩ activatedUnion S B x)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X] in
lemma replacementSet_subset {P Z : Set V} (hZ : Z ⊆ P)
    (U S : I → Set V) (B : I → Set X) (x : X) :
    replacementSet P Z U S B x ⊆ P := by
  intro p hp
  exact hp.elim (fun h => hZ h.1) (fun h => h.1)

end

open Set Finset

open scoped Topology

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.AffinePotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite affine branch geometry for the exact transport metric and compatible cuts. -/

namespace BassTrace.Sparse

open Set Filter

open scoped Topology

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]

section Compact

variable [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

lemma exists_extreme_maximizer {s : Set E} (hs : IsCompact s) (hne : s.Nonempty)
    (f : E →L[ℝ] ℝ) :
    ∃ x ∈ s.extremePoints ℝ, ∀ y ∈ s, f y ≤ f x := by
  obtain ⟨x, hx, hxmax⟩ := hs.exists_isMaxOn hne f.continuous.continuousOn
  have hex : IsExposed ℝ s {x ∈ s | ∀ y ∈ s, f y ≤ f x} := fun _ => ⟨f, rfl⟩
  obtain ⟨z, hz⟩ := (hex.isCompact hs).extremePoints_nonempty ⟨x, hx, hxmax⟩
  exact ⟨z, hex.isExtreme.extremePoints_subset_extremePoints hz, hz.1.2⟩

end Compact

section Potential

variable {V : Type*} [Fintype V] [MetricSpace V]

def potentialSet : Set (V → ℝ) :=
  {l | (∑ v, l v) = 0 ∧ ∀ v w, |l v - l w| ≤ dist v w}

lemma zero_mem_potentialSet : (0 : V → ℝ) ∈ potentialSet := by
  simp [potentialSet, dist_nonneg]

lemma isClosed_potentialSet : IsClosed (potentialSet : Set (V → ℝ)) := by
  have heq : (potentialSet : Set (V → ℝ)) =
      {l | (∑ v, l v) = 0} ∩ ⋂ v, ⋂ w, {l | |l v - l w| ≤ dist v w} := by
    ext l
    simp [potentialSet]
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun v => isClosed_iInter fun w =>
      isClosed_le (by fun_prop) continuous_const

noncomputable def totalDistances : ℝ := ∑ v : V, ∑ w : V, dist v w

lemma dist_le_totalDistances (v w : V) : dist v w ≤ totalDistances (V := V) := by
  classical
  apply (Finset.single_le_sum (f := fun w' : V => dist v w') (fun _ _ => dist_nonneg) (Finset.mem_univ w)).trans
  exact Finset.single_le_sum (f := fun v' : V => ∑ w' : V, dist v' w')
    (fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg) (Finset.mem_univ v)

lemma potential_coordinate_bound [Nonempty V] {l : V → ℝ} (hl : l ∈ potentialSet) (v : V) :
    |l v| ≤ totalDistances (V := V) := by
  classical
  have hmin : ∃ w, l w ≤ 0 := by
    by_contra! h
    have hp : 0 < ∑ w, l w := Finset.sum_pos (fun w _ => h w) Finset.univ_nonempty
    rw [hl.1] at hp
    exact lt_irrefl 0 hp
  have hmax : ∃ w, 0 ≤ l w := by
    by_contra! h
    have hp : ∑ w, l w < 0 := Finset.sum_neg (fun w _ => h w) Finset.univ_nonempty
    rw [hl.1] at hp
    exact lt_irrefl 0 hp
  obtain ⟨w, hw⟩ := hmin
  obtain ⟨z, hz⟩ := hmax
  have hvw := (hl.2 v w).trans (dist_le_totalDistances v w)
  have hvz := (hl.2 v z).trans (dist_le_totalDistances v z)
  rw [abs_le] at hvw hvz ⊢
  constructor <;> linarith

lemma isCompact_potentialSet [Nonempty V] : IsCompact (potentialSet : Set (V → ℝ)) := by
  apply IsCompact.of_isClosed_subset (s := Set.Icc (fun _ : V => -totalDistances (V := V))
    (fun _ : V => totalDistances (V := V))) isCompact_Icc isClosed_potentialSet
  intro l hl
  constructor <;> intro v
  · exact (abs_le.mp (potential_coordinate_bound hl v)).1
  · exact (abs_le.mp (potential_coordinate_bound hl v)).2

noncomputable def centerPotential (l : V → ℝ) (v : V) : ℝ :=
  l v - (∑ w, l w) / Fintype.card V

noncomputable def potentialPairing (k : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ v : V, (k v) • ContinuousLinearMap.proj v

end Potential

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.GraphRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.GraphGeometry

section

open scoped BigOperators

variable {Y : Type*} (Γ : SimpleGraph Y)

lemma graphMetric_discrete (hΓ : Γ.Connected) (a b : Y) (hab : a ≠ b) :
    (1 : ℝ) ≤ (Γ.dist a b : ℝ) := by
  have hd : Γ.dist a b ≠ 0 := by
    intro he
    exact hab ((hΓ.preconnected a b).dist_eq_zero_iff.mp he)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd

end

open Set Finset

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.BallGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

/-! Finite-center selection from compactness of closed original simplices, without a
cocompactness assumption on the continuous ambient space. -/

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*} [DecidableEq Y]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite]

def originalTops (K : PreAbstractSimplicialComplex Y) (n : ℕ) : Set (Finset Y) :=
  {s | s ∈ K.faces ∧ s.card=n+1}

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.SimplexVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Euclidean coordinate simplex volume from the volume of the ℓ¹ ball and sign symmetry. -/

namespace BassTrace.Sparse

open MeasureTheory Set

open scoped ENNReal

def standardSolidSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def l1UnitPolytope (n : ℕ) : Set (Fin n → ℝ) := {x | ∑ i, |x i| ≤ 1}

def signReflection {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if ε i then x i else -x i

def signChamber {n : ℕ} (ε : Fin n → Bool) : Set (Fin n → ℝ) :=
  signReflection ε ⁻¹' standardSolidSimplex n

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.TreeDeterminants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An oriented incidence matrix of a tree, with its root row deleted, is unimodular,
independently of a planar structure or ordering of children. -/

namespace BassTrace.Sparse

section

open SimpleGraph

noncomputable def treeEdgeEquiv {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Fin n ≃ Γ.edgeSet := by
  classical
  apply Fintype.equivOfCardEq
  have h := hΓ.card_edgeFinset
  rw [Γ.edgeFinset_card, Fintype.card_fin] at h
  simp only [Fintype.card_fin]
  omega

def rootCoordinate {n : ℕ} (v : Fin (n+1)) : Fin n → ℤ :=
  fun i => if i.succ=v then 1 else 0

lemma rootCoordinate_zero (n : ℕ) : rootCoordinate (0 : Fin (n+1)) = 0 := by
  ext i
  simp [rootCoordinate]

lemma rootCoordinate_succ {n : ℕ} (v : Fin n) :
    rootCoordinate v.succ = Pi.single v 1 := by
  ext i
  simp [rootCoordinate,Pi.single_apply,eq_comm]

noncomputable def treeIncidence {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.1) i -
  rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.2) i

lemma adjacent_difference_mem_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) {u v : Fin (n+1)} (huv : Γ.Adj u v) :
    rootCoordinate u - rootCoordinate v ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
  classical
  let e : Γ.edgeSet := ⟨s(u,v),huv⟩
  let j := (treeEdgeEquiv Γ hΓ).symm e
  have hj : treeEdgeEquiv Γ hΓ j = e := (treeEdgeEquiv Γ hΓ).apply_symm_apply e
  have hc := Submodule.subset_span (R := ℤ) (Set.mem_range_self
    (f := (treeIncidence Γ hΓ).col) j)
  have he : s(e.val.out.1,e.val.out.2) = s(u,v) := e.val.out_eq
  rcases Sym2.eq_iff.mp he with h | h
  · have heq : rootCoordinate u - rootCoordinate v = (treeIncidence Γ hΓ).col j := by
      ext i
      simp [Matrix.col,treeIncidence,hj,h.1,h.2]
    rw [heq]
    exact hc
  · have heq : rootCoordinate u - rootCoordinate v = -(treeIncidence Γ hΓ).col j := by
      ext i
      simp [Matrix.col,treeIncidence,hj,h.1,h.2]
    rw [heq]
    exact Submodule.neg_mem _ hc

lemma walk_difference_mem_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) {u v : Fin (n+1)} (p : Γ.Walk u v) :
    rootCoordinate u - rootCoordinate v ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have h := Submodule.add_mem _ (adjacent_difference_mem_span Γ hΓ huv) ih
    convert h using 1
    abel

lemma treeIncidence_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hsingle (i : Fin n) : Pi.single i (1 : ℤ) ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
    obtain ⟨p⟩ := hΓ.connected.preconnected i.succ 0
    simpa only [rootCoordinate_zero,sub_zero,rootCoordinate_succ] using
      walk_difference_mem_span Γ hΓ p
  have hx : x = ∑ i, x i • Pi.single i (1 : ℤ) := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ (x i) (hsingle i))

theorem treeIncidence_isUnit_det {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : IsUnit (treeIncidence Γ hΓ).det := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  apply (LinearMap.range_eq_top (f := (treeIncidence Γ hΓ).mulVecLin)).mp
  rw [Matrix.range_mulVecLin,treeIncidence_span]

theorem treeIncidence_abs_real_det {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : |((treeIncidence Γ hΓ).map (Int.castRingHom ℝ)).det| = 1 := by
  classical
  change |((treeIncidence Γ hΓ).map (fun x => (x : ℝ))).det| = 1
  rw [← Int.cast_det]
  rcases Int.isUnit_iff.mp (treeIncidence_isUnit_det Γ hΓ) with h | h <;> simp [h]

open MeasureTheory Set

noncomputable def realTreeIncidence {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Matrix (Fin n) (Fin n) ℝ :=
  (treeIncidence Γ hΓ).map (Int.castRingHom ℝ)

lemma realTreeIncidence_det_ne_zero {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : (realTreeIncidence Γ hΓ).det ≠ 0 := by
  intro h
  have hh := treeIncidence_abs_real_det Γ hΓ
  change |(realTreeIncidence Γ hΓ).det| = 1 at hh
  rw [h,abs_zero] at hh
  exact zero_ne_one hh

noncomputable def treeGradient {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) (ℓ : Fin (n+1) → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j =>
    (ℓ ((treeEdgeEquiv Γ hΓ j).val.out.1) - ℓ ((treeEdgeEquiv Γ hΓ j).val.out.2)) /
      Real.sqrt n)

noncomputable def treeSolidSimplex {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Set (Fin n → ℝ) :=
  (Matrix.toLin' (realTreeIncidence Γ hΓ)) ⁻¹' standardSolidSimplex n

end

open MeasureTheory Set Finset

open scoped ENNReal

noncomputable section

def barycentricParam {n : ℕ} (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cases (1-∑ i, x i) x

@[simp] lemma barycentricParam_zero {n : ℕ} (x : Fin n → ℝ) :
    barycentricParam x 0 = 1-∑ i, x i := rfl

@[simp] lemma barycentricParam_succ {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    barycentricParam x i.succ = x i := rfl

def treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x : EuclideanSpace ℝ (Fin n)) : Fin (n+1) → ℝ :=
  barycentricParam (Matrix.toLin' (realTreeIncidence T hT) x.ofLp)

def treeArea {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) (Q : Set (Fin (n+1) → ℝ)) : ℝ≥0∞ :=
  μHE[j] ((treeParam T hT) ⁻¹' Q)

def fullBarycentricSimplex (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

end

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.TreeArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

open MeasureTheory Set Finset

open scoped ENNReal

section

def treeMatrixEquiv {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' (realTreeIncidence T hT))
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT))),
     Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT)))⟩

def independentCoordinates (n : ℕ) : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun p := fun i => p i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def treeCoordinates {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap.comp
    ((treeMatrixEquiv T hT).symm.toLinearMap.comp (independentCoordinates n))

@[simp] lemma treeCoordinates_treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x : EuclideanSpace ℝ (Fin n)) : treeCoordinates T hT (treeParam T hT x) = x := by
  change (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
    ((treeMatrixEquiv T hT).symm ((treeMatrixEquiv T hT) x.ofLp)) = x
  simp

end

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.MarkedArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical Pointwise

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]

def simplexEnumeration {n : ℕ} (s : Finset Y) (hs : s.card=n+1) : Fin (n+1) ≃ s :=
  (Finset.equivFinOfCardEq hs).symm

def simplexCoordinates {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    (Y →₀ ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) :=
  LinearMap.pi (fun i => Finsupp.lapply (simplexEnumeration s hs i).val)

def simplexGraph {n : ℕ} (Γ : SimpleGraph Y) (s : Finset Y) (hs : s.card=n+1) :
    SimpleGraph (Fin (n+1)) := Γ.comap (fun i => (simplexEnumeration s hs i).val)

end

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.SimplexMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open MeasureTheory Set Finset

open scoped ENNReal

def treeAreaMeasure {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) : Measure (Fin (n+1) → ℝ) :=
  Measure.map (treeParam T hT) μHE[j]

end

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

section

variable {Y : Type*} [DecidableEq Y]

def simplexEmbed {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] (Y →₀ ℝ) :=
  (Finsupp.lmapDomain ℝ ℝ (fun i => (simplexEnumeration s hs i).val)).comp
    (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).symm.toLinearMap

omit [DecidableEq Y] in
lemma simplexCoordinates_embed {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : simplexCoordinates s hs (simplexEmbed s hs p) = p := by
  ext i
  change (Finsupp.mapDomain (fun i => (simplexEnumeration s hs i).val)
    ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).symm p))
    (simplexEnumeration s hs i).val = p i
  have hi : Function.Injective (fun i => (simplexEnumeration s hs i).val) :=
    Subtype.val_injective.comp (simplexEnumeration s hs).injective
  rw [Finsupp.mapDomain_apply hi]
  exact congrFun ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).apply_symm_apply p) i

omit [DecidableEq Y] in
lemma simplexEmbed_support {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : (simplexEmbed s hs p).support ⊆ s := by
  let f : Fin (n+1) ↪ Y := ⟨fun i => (simplexEnumeration s hs i).val,
    Subtype.val_injective.comp (simplexEnumeration s hs).injective⟩
  change (Finsupp.mapDomain f _).support ⊆ s
  rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain]
  intro y hy
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
  exact (simplexEnumeration s hs i).property

end

end

section

open Finset Set MeasureTheory

variable {n : ℕ}

def relabelCoefficients (e : Equiv.Perm (Fin (n+1))) :
    (Fin (n+1) → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) where
  toFun p := p ∘ e.symm
  invFun p := p ∘ e
  left_inv p := by ext i; simp
  right_inv p := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def edgeVector (u v : Fin (n+1)) : Fin (n+1) → ℝ := Pi.single u 1 - Pi.single v 1

def treeEdgePermutation (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) : Equiv.Perm (Fin n) :=
  (treeEdgeEquiv T hT).trans (e.mapEdgeSet.trans (treeEdgeEquiv U hU).symm)

def signedEdgeMap (π : Equiv.Perm (Fin n)) (ε : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun j => ε (π.symm j) * x.ofLp (π.symm j))
  map_add' x y := by ext j; simp [mul_add]
  map_smul' a x := by ext j; simp [mul_left_comm]

end

open MeasureTheory Set Finset

open scoped ENNReal

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.OrbitAreas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

def simplexPermutation {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1) :
    Equiv.Perm (Fin (n+1)) :=
  ((simplexEnumeration s hs).trans (Finset.equivMap e.toEmbedding s)).trans
    (simplexEnumeration (s.map e.toEmbedding) (by simpa using hs)).symm

end

open Finset Set

open scoped Pointwise Classical

variable {H Y : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (K : PreAbstractSimplicialComplex Y) (n : ℕ)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

lemma smul_finset_eq_map (h : H) (s : Finset Y) :
    h • s=s.map (MulAction.toPerm h).toEmbedding := by
  ext y
  simp only [Finset.mem_smul_finset,Finset.mem_map]
  rfl

end Sparse

namespace Sparse.OrbitAreas

section

open scoped BigOperators Pointwise ENNReal

variable {H T : Type*} [Group H] [MulAction H T]

def representative (a : T) (b : MulAction.orbit H a) : H := b.property.choose

@[simp] lemma representative_smul (a : T) (b : MulAction.orbit H a) :
    representative a b • a = b.val := b.property.choose_spec

def orbitTimesStabilizer (a : T) : MulAction.orbit H a × MulAction.stabilizer H a ≃ H where
  toFun p := representative a p.1 * p.2.val
  invFun h := (⟨h • a,⟨h,rfl⟩⟩,⟨(representative a ⟨h • a,⟨h,rfl⟩⟩)⁻¹*h,by
    rw [MulAction.mem_stabilizer_iff,mul_smul]
    exact (eq_inv_smul_iff.mpr (representative_smul a ⟨h • a,⟨h,rfl⟩⟩)).symm⟩)
  left_inv p := by
    have he : (representative a p.1 * p.2.val) • a = p.1.val := by
      rw [mul_smul, p.2.property,representative_smul]
    apply Prod.ext
    · exact Subtype.ext he
    · apply Subtype.ext
      dsimp
      have hb : (⟨(representative a p.1 * p.2.val) • a,
          ⟨representative a p.1 * p.2.val,rfl⟩⟩ : MulAction.orbit H a) = p.1 := Subtype.ext he
      rw [hb,inv_mul_cancel_left]
  right_inv h := by simp

@[simp] lemma orbitTimesStabilizer_smul (a : T)
    (p : MulAction.orbit H a × MulAction.stabilizer H a) :
    orbitTimesStabilizer a p • a = p.1.val := by
  change (representative a p.1 * p.2.val) • a = _
  rw [mul_smul,p.2.property,representative_smul]

end

section

open MeasureTheory Set

open scoped ENNReal

variable {H T X : Type*} [Group H] [MulAction H T] [MulAction H X]
  [Countable H] [Countable T] [MeasurableSpace X]

def orbitActivated (B : Set X) (f : T → X → ℝ≥0∞) (a : T) (h : H) (x : X) : ℝ≥0∞ :=
  B.indicator (f (h⁻¹ • a)) (h⁻¹ • x)

end

open Set Finset MeasureTheory

open scoped Pointwise ENNReal Classical

variable {H T : Type*} [Group H] [MulAction H T]

variable [Finite (MulAction.orbitRel.Quotient H T)]

def orbitReps : Finset T :=
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient H T)
  (Finset.univ : Finset (MulAction.orbitRel.Quotient H T)).image Quotient.out

end Sparse.OrbitAreas

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.AffineCoarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine coarea from product measure and one-dimensional Lebesgue scaling. The transverse
measure may be s-finite; orthonormal coordinates specialize this to affine polyhedral area. -/

namespace BassTrace.Sparse

open MeasureTheory Set

open scoped ENNReal

section Product

variable {F : Type*} [MeasurableSpace F] (ν : Measure F) [SFinite ν]

def productSlice (Q : Set (ℝ × F)) (a c t : ℝ) : Set F :=
  {z | ((t - c) / a, z) ∈ Q}

end Product

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open scoped InnerProductSpace

noncomputable def normalParamIsometry (u : E) (hu : ‖u‖ = 1) :
    WithLp 2 (ℝ × (ℝ ∙ u)ᗮ) ≃ₗᵢ[ℝ] E :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.toSpanUnitSingleton u hu)
    (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ)).trans
    (ℝ ∙ u).orthogonalDecomposition.symm

noncomputable def euclideanSliceArea (Q : Set E) (u : E) (a c t : ℝ) : ℝ≥0∞ :=
  volume {z : (ℝ ∙ u)ᗮ | ((t - c) / a) • u + (z : E) ∈ Q}

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.SimplexCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y : Type*} [DecidableEq Y]

lemma simplexEmbed_nonneg {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Fin (n+1) → ℝ} (hp : ∀ i,0≤p i) (y : Y) : 0 ≤ simplexEmbed s hs p y := by
  by_cases hy : y∈s
  · obtain ⟨i,hi⟩ := (simplexEnumeration s hs).surjective ⟨y,hy⟩
    have h := congrFun (simplexCoordinates_embed s hs p) i
    change simplexEmbed s hs p (simplexEnumeration s hs i).val = p i at h
    rw [hi] at h
    rw [h]
    exact hp i
  · rw [Finsupp.notMem_support_iff.mp (fun h => hy (simplexEmbed_support s hs p h))]

omit [DecidableEq Y] in
lemma simplexEmbed_total {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : (simplexEmbed s hs p).sum (fun _ r=>r)=∑ i,p i := by
  rw [Finsupp.sum_of_support_subset _ (simplexEmbed_support s hs p) _ (by intros; rfl)]
  rw [← (Finset.sum_attach s (fun y : Y => simplexEmbed s hs p y))]
  change (∑ y : s, simplexEmbed s hs p y.val) = _
  rw [← (simplexEnumeration s hs).sum_comp (fun y : s => simplexEmbed s hs p y.val)]
  congr 1
  funext i
  exact congrFun (simplexCoordinates_embed s hs p) i

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.GraphCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

namespace Sparse.GraphCounting

open SimpleGraph

variable {Y : Type*} (Γ : SimpleGraph Y)

lemma extend_tour [DecidableEq Y] {v a b : Y} (p : Γ.Walk v v)
    (ha : a ∈ p.support) (hab : Γ.Adj a b) :
    ∃ q : Γ.Walk v v, q.length = p.length+2 ∧
      q.support.toFinset = insert b p.support.toFinset := by
  let q := (p.takeUntil a ha).append
    ((hab.toWalk.append hab.symm.toWalk).append (p.dropUntil a ha))
  refine ⟨q, ?_, ?_⟩
  · have hl := congrArg SimpleGraph.Walk.length (p.take_spec ha)
    simp only [Walk.length_append] at hl
    simp only [q, Walk.length_append, Adj.length_toWalk]
    omega
  · ext y
    have hm := congrArg (fun r : Γ.Walk v v => y ∈ r.support) (p.take_spec ha)
    simp only [Walk.mem_support_append_iff] at hm
    simp only [q, List.mem_toFinset, Finset.mem_insert, Walk.mem_support_append_iff,
      Adj.support_toWalk, List.mem_cons]
    have haa : a ∈ (p.takeUntil a ha).support := Walk.end_mem_support _
    have hh : y = a → y ∈ (p.takeUntil a ha).support := fun h => h ▸ haa
    tauto

lemma exists_tour_of_card [Fintype Y] [DecidableEq Y] (hΓ : Γ.Connected) (v : Y)
    (k : ℕ) (hk : k < Fintype.card Y) :
    ∃ p : Γ.Walk v v, p.length = 2*k ∧ p.support.toFinset.card = k+1 := by
  induction k with
  | zero => exact ⟨.nil, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨p,hp,hpc⟩ := ih (by omega)
    have hs : p.support.toFinset ≠ Finset.univ := by
      intro he
      have hcc := congrArg Finset.card he
      simp only [Finset.card_univ,hpc] at hcc
      omega
    have hex : ∃ b, b ∉ p.support.toFinset := by
      by_contra! ht
      exact hs (Finset.eq_univ_of_forall ht)
    obtain ⟨b,hb⟩ := hex
    obtain ⟨r⟩ := hΓ.preconnected v b
    obtain ⟨d,_,hd1,hd2⟩ := r.exists_boundary_dart
      (p.support.toFinset : Set Y) (by simp) hb
    obtain ⟨q,hq,hqs⟩ := extend_tour Γ p (by simpa using hd1) d.adj
    refine ⟨q, by omega, ?_⟩
    rw [hqs,Finset.card_insert_of_notMem hd2,hpc]

theorem exists_covering_tour [Fintype Y] [DecidableEq Y] (hΓ : Γ.Connected)
    (v : Y) : ∃ p : Γ.Walk v v,
      p.length = 2*(Fintype.card Y-1) ∧ p.support.toFinset = Finset.univ := by
  have hn : 0 < Fintype.card Y := Fintype.card_pos_iff.mpr ⟨v⟩
  obtain ⟨p,hp,hpc⟩ := exists_tour_of_card Γ hΓ v (Fintype.card Y-1) (by omega)
  refine ⟨p,hp,Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_⟩
  simp only [Finset.card_univ,hpc]
  omega

lemma connected_set_tour [DecidableEq Y] (s : Finset Y) (hc : (Γ.induce (s : Set Y)).Connected)
    (v : Y) (hv : v ∈ s) {n : ℕ} (hs : s.card=n+1) :
    ∃ p : Γ.Walk v v, p.length=2*n ∧ p.support.toFinset=s := by
  obtain ⟨p,hp,hps⟩ := exists_covering_tour (Γ.induce (s : Set Y)) hc ⟨v,hv⟩
  let f := (SimpleGraph.Embedding.induce (G := Γ) (s : Set Y)).toHom
  refine ⟨p.map f, ?_, ?_⟩
  · change (p.map f).length = 2*n
    rw [Walk.length_map,hp]
    have hcard : Fintype.card (s : Set Y) = s.card :=
      Fintype.card_of_subtype s (fun _ => Iff.rfl)
    rw [hcard,hs,Nat.add_sub_cancel]
  · change (p.map f).support.toFinset = s
    rw [Walk.support_map]
    ext y
    simp only [List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨a,_,rfl⟩
      exact a.property
    · intro hy
      refine ⟨⟨y,hy⟩,?_,rfl⟩
      have hm : (⟨y,hy⟩ : (s : Set Y)) ∈ p.support.toFinset := hps ▸ Finset.mem_univ _
      exact List.mem_toFinset.mp hm

abbrev BasedWalk (v : Y) (n : ℕ) := {p : (b : Y) × Γ.Walk v b // p.2.length = n}

def basedWalkSucc (v : Y) (n : ℕ) :
    BasedWalk Γ v (n+1) → (w : Γ.neighborSet v) × BasedWalk Γ w n
  | ⟨⟨_,.cons h p⟩,hl⟩ => ⟨⟨_,h⟩,⟨⟨_,p⟩,by simpa using hl⟩⟩

def basedWalkCons (v : Y) (n : ℕ) :
    ((w : Γ.neighborSet v) × BasedWalk Γ w n) → BasedWalk Γ v (n+1)
  | ⟨⟨w,h⟩,⟨⟨b,p⟩,hp⟩⟩ => ⟨⟨b,.cons h p⟩,by change p.length+1=n+1; change p.length=n at hp; omega⟩

abbrev ConnectedSets (v : Y) (n : ℕ) :=
  {s : Finset Y // v ∈ s ∧ s.card=n+1 ∧ (Γ.induce (s : Set Y)).Connected}

def connectedSetTour [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    Γ.Walk v v := (connected_set_tour Γ s.val s.property.2.2 v s.property.1
      s.property.2.1).choose

lemma connectedSetTour_length [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    (connectedSetTour Γ v n s).length=2*n :=
  (connected_set_tour Γ s.val s.property.2.2 v s.property.1 s.property.2.1).choose_spec.1

def connectedSetEncoding [DecidableEq Y] (v : Y) (n : ℕ) :
    ConnectedSets Γ v n → BasedWalk Γ v (2*n) :=
  fun s => ⟨⟨v,connectedSetTour Γ v n s⟩,connectedSetTour_length Γ v n s⟩

end Sparse.GraphCounting

namespace Sparse.GraphCounting

open Set Finset

variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]

abbrev ConnectedThrough (B : Finset Y) (n : ℕ) :=
  {s : Finset Y // s.card = n+1 ∧ (Γ.induce (s : Set Y)).Connected ∧
    ∃ v ∈ B, v ∈ s}

noncomputable def throughEncoding (B : Finset Y) (n : ℕ) :
    ConnectedThrough Γ B n → (v : B) × ConnectedSets Γ v n := fun s =>
  ⟨⟨s.property.2.2.choose,s.property.2.2.choose_spec.1⟩,
    ⟨s.val,s.property.2.2.choose_spec.2,s.property.1,s.property.2.1⟩⟩

end Sparse.GraphCounting

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.VolumeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

/-! Scalar estimates for iterated volume growth and high-dimensional ball bounds. -/

open Finset MeasureTheory intervalIntegral

namespace Sparse

noncomputable def dividedPower (n : ℕ) (t : ℝ) : ℝ :=
  t ^ n / (n.factorial : ℝ)

noncomputable def slicingError (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, dividedPower (i + 1) t

@[simp] lemma dividedPower_zero (t : ℝ) : dividedPower 0 t = 1 := by
  simp [dividedPower]

@[simp] lemma slicingError_zero (t : ℝ) : slicingError 0 t = 0 := by
  simp [slicingError]

@[simp] lemma dividedPower_one (t : ℝ) : dividedPower 1 t = t := by
  simp [dividedPower]

/-! A strict high-dimensional volume margin with radius 4 D² and half-radius 2 D². -/

def volumeThreshold (D : ℕ) : ℕ := (4 * D ^ 3 + D + 3) ^ 2

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

def ballVolumeBound (D n : ℕ) (R : ℝ) : ℝ :=
  ((n+1)*D^(⌊R*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) : ℕ) / (n.factorial : ℝ)

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.SupportGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y X : Type*} [DecidableEq Y] [TopologicalSpace X]

variable {K : PreAbstractSimplicialComplex Y}

omit [DecidableEq Y] [TopologicalSpace X] in
lemma connectedComponentIn_inter_of_subset {V : Type*} [TopologicalSpace V]
    (S W : Set V) (p : V) (hp : p∈S)
    (hW : connectedComponentIn S p⊆W) :
    connectedComponentIn (S∩W) p=connectedComponentIn S p := by
  apply Set.Subset.antisymm (connectedComponentIn_mono p Set.inter_subset_left)
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hp) (fun _ h=>⟨connectedComponentIn_subset S p h,hW h⟩)

end Sparse

namespace Sparse.OrbitForms

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y : Type*} [Group H] [MulAction H Y]

def componentVectorEmbedding : (Y →₀ ℝ) →ₗ[ℝ] lp (fun _ : Y => ℝ) 2 :=
  Finsupp.linearCombination ℝ (fun y => lp.single 2 y 1)

lemma componentVectorEmbedding_apply (v : Y →₀ ℝ) (y : Y) :
    componentVectorEmbedding v y = v y := by
  simp only [componentVectorEmbedding,Finsupp.linearCombination_apply, Finsupp.sum,
    lp.coeFn_sum,lp.coeFn_smul,Finset.sum_apply,Pi.smul_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]

end Sparse.OrbitForms

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQW_BassTrace.SubdivisionWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

section

open Set Finset

open scoped Classical Pointwise

variable {H Y : Type*} [Group H] [MulAction H Y]

def generatedReps (T : Finset (Finset Y)) : Finset (Finset Y) :=
  (T.biUnion Finset.powerset).filter (·.Nonempty)

end

section

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*}

def uniformVector (s : Finset Y) : Y →₀ ℂ :=
  ∑y∈s,Finsupp.single y (s.card : ℂ)⁻¹

end

open Set Finset

open scoped BassTrace.Sparse Classical

end BassTrace.Sparse

end

end OAI
end


