-- Prove2me | Definitions.Def_OAIStdSimplexCompat
-- name    : OAIStdSimplexCompat
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T08:31:58.384985+00:00
-- url     : https://prove2.me/theorems/c7014b9a-e570-4ee1-a054-618b8beeb719
-- title:
--   Standard simplex compatibility layer for ports of openai/math (the Mathlib d13f23b `Convexity.StdSimplex` API on Mathlib 0df444a)
-- statement:
--   A compatibility layer, not new mathematics. OpenAI's [openai/math](https://github.com/openai/math) Lean library is built on Mathlib `d13f23b`; prove2.me's environment is Mathlib `0df444a`. Both define the standard simplex as the structure `Convexity.StdSimplex R X` (finitely supported nonnegative weights summing to 1), but `0df444a` lacks part of the API that OpenAI's code uses, and its `SimplexCategory.toTop` takes the topological $n$-simplex to be the subtype `stdSimplex ℝ (Fin (n+1))` of `Fin (n+1) → ℝ`, where `d13f23b` takes the structure. This bundle supplies the missing API so that ported OpenAI code compiles here unchanged, or with one mechanical renaming.
--
--   This is not OpenAI's code, and nothing in it is copied from openai/math.
--
--   **Part 1, on `Convexity.StdSimplex`, under the `d13f23b` names.** Copied from Mathlib `d13f23b` (Apache 2.0; authors Kim Morrison, Andrew Yang, Yaël Dillies and Joël Riou) and adapted to `0df444a`; only declarations `0df444a` does not already have:
--
--   - from `Geometry/Convex/ConvexSpace/Defs.lean`: `total_of_fintype`, `total_fin_two`, `range_toFun_comp_weights`, `weights_apply_eq_one`, `weights_apply_le_one`, `single_injective`, `map_id'`, `map_comp'`, `mem_range_map_iff`, `equivIcc` (the 1-simplex and $[0,1]$) with its four simp lemmas, `StdSimplex.iConvexComb_single`, and the `Subsingleton`, `Inhabited`, `Nonempty`, `Nontrivial` and `Unique` instances;
--   - `Topology.lean`: the topology on `StdSimplex R M` (induced from `M → R` when $M$ is finite, in general the finest topology making every `map f` from a finite simplex continuous), with `continuous_iff`, `continuous_map`, `continuous_weights_apply`, `isEmbedding_toFun_comp_weights` and `isClosedEmbedding_toFun_comp_weights`;
--   - `CompactSpaceStdSimplex.lean`: the bounds and diameter of the image in `M → ℝ`, and the `CompactSpace` instance for finite $M$;
--   - `Barycenter.lean`: `subBarycenter` (the barycenter of a nonempty finite set of vertices) and `barycenter`;
--   - `PathConnectedSpaceStdSimplex.lean`: continuity of the segment `continuous_convexCombPair`, `continuous_duple`, the `PathConnectedSpace` instance, and `homeomorphI`, the homeomorphism of the 1-simplex with the unit interval.
--
--   Part 1 declares every `Convexity.StdSimplex.*` name used anywhere in openai/math (checked against its full source, commit `1581d4c`) that `0df444a` lacks. It does not change `SimplexCategory.toTop`, which no added lemma can.
--
--   **Part 2, `OAI.SStd`, the subtype with the `d13f23b` names (our own code).** `OAI.SStd R X` is the subtype `stdSimplex R X` on a finite type $X$, the topological simplex of this Mathlib's `SimplexCategory.toTop`, with `weights`, `map` (equal to `stdSimplex.map`, so `TopCat.toSSetObjEquiv` and its naturality apply), `single`, `barycenter`, their simp lemmas, the continuity and embedding lemmas, the bounds and diameter of the range, and `equivStdSimplex`, the bijection with `Convexity.StdSimplex R X` preserving weights. A port whose code identifies the simplex with `SimplexCategory.toTop.obj` (singular homology) renames `Convexity.StdSimplex` to `OAI.SStd`. That route needs finite index types and has no convex-space structure.
--
--   **Ports that needed it.** OpenAI's Problem 340 (a $C^1$ counterexample to the entropy conjecture), whose singular homology goes through `SimplexCategory.toTop`, used Part 2 (published inside its own bundle `OAIQWEC000`). The ports of WeakMTWGlobalSupport, MatchingEntropyBounds and SubpolynomialLp each use `Convexity.StdSimplex.range_toFun_comp_weights` and `isEmbedding_toFun_comp_weights` to prove that the probability simplex is compact, and were hand-patched to Mathlib's `isCompact_stdSimplex`; with Part 1 they compile unchanged. The porting tools of the prove2me skill (`p2mlib.oaiport`, option `--stdsimplex`) add this bundle to a port automatically when its source uses `Convexity.StdSimplex`.
-- source:
--   Part 1: Mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612, Mathlib/Geometry/Convex/ConvexSpace/{Defs,Topology,CompactSpaceStdSimplex,Barycenter,PathConnectedSpaceStdSimplex}.lean, https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Geometry/Convex/ConvexSpace (Apache 2.0; Kim Morrison, Andrew Yang, Yaël Dillies, Joël Riou), adapted to Mathlib 0df444a. Part 2 (OAI.SStd): original, written for porting openai/math (https://github.com/openai/math), not OpenAI code.

import Mathlib

/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

@[simp]
lemma total_of_fintype [Fintype X] (w : StdSimplex R X) :
    ∑ i, w.weights i = 1 := by
  have := w.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

@[simp]
lemma total_fin_two (w : StdSimplex R (Fin 2)) :
    w.weights 0 + w.weights 1 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_two]

lemma range_toFun_comp_weights [Fintype X] :
    Set.range (fun t ↦ t.weights : StdSimplex R X → (X → R)) =
    (⋂ (i : X), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.weights_nonneg, by simp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨{
      weights := Finsupp.equivFunOnFinite.symm s
      nonneg m := by simpa using h₁ m
      total := by simpa [Finsupp.sum_fintype] }, by simp⟩

@[simp]
lemma weights_apply_eq_one [Subsingleton X] (s : StdSimplex R X) (m : X) :
    s.weights m = 1 := by
  rw [← s.total, Finsupp.sum_eq_single m
    (fun _ _ h ↦ (h (by subsingleton)).elim) (by simp)]

instance instSubsingleton [Subsingleton X] : Subsingleton (StdSimplex R X) where
  allEq := by
    intro a b
    ext m
    simp

variable [IsStrictOrderedRing R]

lemma single_injective : Function.Injective (single (R := R) (M := X)) :=
  fun _ _ h ↦ by simpa using congr_arg (Finsupp.support ∘ weights) h

@[simp]
lemma weights_apply_le_one
    (s : StdSimplex R X) (m : X) : s.weights m ≤ 1 := by
  by_cases hm : s.weights m = 0
  · simpa only [hm] using zero_le_one' R
  · rw [← s.total, Finsupp.sum]
    exact Finset.single_le_sum (fun i _ => s.weights_nonneg i) (Finsupp.mem_support_iff.mpr hm)

instance instInhabited [Inhabited X] : Inhabited (StdSimplex R X) where
  default := .single default

instance instNonempty [Nonempty X] : Nonempty (StdSimplex R X) :=
  ⟨.single (Classical.arbitrary _)⟩

instance instNontrivial [Nontrivial X] : Nontrivial (StdSimplex R X) := by
  obtain ⟨x, y, h⟩ := exists_pair_ne X
  exact ⟨.single x, .single y, single_injective.ne h⟩

instance instUnique [Unique X] : Unique (StdSimplex R X) where
  uniq := by subsingleton

lemma map_id' : map (R := R) (id : X → X) = id := by
  funext f
  exact map_id f

lemma map_comp' (g₁ : X → Y) (g₂ : Y → Z) :
    map (R := R) (g₂ ∘ g₁) = map g₂ ∘ map g₁ := by
  funext f
  exact map_comp f g₁ g₂

lemma mem_range_map_iff
    (f : X → Y) (s : StdSimplex R Y) :
    s ∈ Set.range (map f) ↔ ∀ (x : Y), x ∉ Set.range f → s.weights x = 0 := by
  classical
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    intro x hx
    simpa using Finsupp.mapDomain_of_notMem_range s.weights x hx
  · have (i : s.weights.support) : ∃ (m : X), f m = i := by
      by_contra hne
      simp only [not_exists] at hne
      exact (Finsupp.mem_support_iff.mp i.2) (h i (by rintro ⟨m, hm⟩; exact hne m hm))
    choose m hm using this
    refine ⟨{
      weights := ∑ (y : s.weights.support), .single (m y) (s.weights y)
      nonneg := by
        intro x
        simp only [Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.coe_zero, Pi.zero_apply]
        refine Finset.sum_nonneg fun y _ ↦ ?_
        rw [Finsupp.single_apply]
        split_ifs
        · exact s.weights_nonneg _
        · exact le_rfl
      total := by
        rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
        simp only [Finsupp.sum_single_index]
        rw [← s.total, Finsupp.sum, Finset.univ_eq_attach]
        exact Finset.sum_attach s.weights.support (fun y => s.weights y) }, ?_⟩
    ext y
    by_cases hy : y ∈ s.weights.support
    · simp only [Finset.univ_eq_attach, weights_map, Finsupp.mapDomain_finsetSum,
        Finsupp.mapDomain_single, Finsupp.coe_finsetSum, Finset.sum_apply, hm]
      rw [Finset.sum_eq_single ⟨y, hy⟩ ?_ (by simp)]
      · simp
      · intro z _ hz'
        rw [Finsupp.single_apply, if_neg]
        intro hzy
        exact hz' (Subtype.ext hzy)
    · rw [Finsupp.notMem_support_iff] at hy
      rw [hy]
      simp only [Finset.univ_eq_attach, weights_map, Finsupp.mapDomain_finsetSum,
        Finsupp.mapDomain_single, Finsupp.coe_finsetSum, Finset.sum_apply, hm]
      refine Finset.sum_eq_zero (fun z _ ↦ Finsupp.single_eq_of_ne ?_)
      rintro rfl
      exact (Finsupp.mem_support_iff.mp z.2) hy

end Semiring

section

variable {R' : Type*} [Ring R'] [PartialOrder R'] [IsStrictOrderedRing R']

/-- The bijection between the one dimensional standard simplex and the interval `[0, 1]`. -/
@[simps -isSimp]
def equivIcc : StdSimplex R' (Fin 2) ≃ Set.Icc (0 : R') 1 where
  toFun s := ⟨s.weights 1, s.weights_nonneg 1, s.weights_apply_le_one 1⟩
  invFun t := duple (s := 1 - t) (t := t) 0 1 (sub_nonneg.mpr t.2.2) t.2.1 (by simp)
  left_inv s := by
    ext i
    fin_cases i
    · have := s.total_fin_two
      simp
      exact (eq_sub_of_add_eq this).symm
    · simp
  right_inv t := by
    ext
    simp [Finsupp.single_apply]

attribute [local simp] equivIcc_apply_coe

@[simp]
lemma equivIcc_single_zero : equivIcc (.single (R := R') 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma equivIcc_single_one : equivIcc (.single (R := R') 1) = 1 := by
  ext
  simp

@[simp]
lemma equivIcc_symm_zero : equivIcc.symm 0 = .single (R := R') 0 :=
  equivIcc.injective (by simp)

@[simp]
lemma equivIcc_symm_one : equivIcc.symm 1 = .single (R := R') 1 :=
  equivIcc.injective (by simp)

end

section ConvexSpace

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {I : Type*}

@[simp]
lemma iConvexComb_single (x : StdSimplex R I) :
    x.iConvexComb single = x := by
  ext : 1
  simp [weights_iConvexComb, Finsupp.smul_single_one, Finsupp.sum_single]

end ConvexSpace

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

/-- The topology on `StdSimplex R ι` that is induced by the embedding
`StdSimplex R ι → (ι → R)`. This is the correct topoplogy only when
`ι` is finite, see `StdSimplex.isEmbedding_toFun_comp_weights`. -/
abbrev topologicalSpaceInduced (ι : Type*) : TopologicalSpace (StdSimplex R ι) :=
  .induced (fun t ↦ t.weights : StdSimplex R ι → ι → R) inferInstance

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

@[fun_prop]
lemma continuous_weights_apply {ι : Type*} (i : ι) :
    Continuous (fun (t : StdSimplex R ι) ↦ t.weights i) :=
  (continuous_apply i).comp (by rw [continuous_iff_le_induced])

open Classical in
@[fun_prop]
lemma continuous_map_weights_apply
    [IsStrictOrderedRing R] [IsTopologicalRing R] {ι₁ ι₂ : Type*}
    [Finite ι₁] (f : ι₁ → ι₂) (i₂ : ι₂) :
    Continuous (fun t ↦ (map (R := R) f t).weights i₂) := by
  have := Fintype.ofFinite ι₁
  have (t : StdSimplex R ι₁) :
      (map (R := R) f t).weights i₂ =
        ∑ i₁ with f i₁ = i₂, t.weights i₁ := by
    rw [weights_map, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
      Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, Finset.sum_filter]
  simp only [this]
  fun_prop

lemma continuous_map [IsStrictOrderedRing R] [IsTopologicalRing R]
    {ι₁ ι₂ : Type*} [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] topologicalSpaceInduced in
/-- The topology on `StdSimplex R M`: the supremum of the coinduced topologies for the maps
`StdSimplex.map f : StdSimplex R ι → StdSimplex R M` with `ι` finite. When `M` is finite it is the
topology induced by the embedding `StdSimplex R M → (M → R)`. -/
noncomputable instance topologicalSpace (M : Type v) :
    TopologicalSpace (StdSimplex R M) :=
  ⨆ (ι : Type v) (_ : Finite ι) (f : ι → M), .coinduced (map f) inferInstance

lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [map_id']
    rfl

variable {R} in
lemma continuous_iff
    {M : Type v} {T : Type*} [TopologicalSpace T] (f : StdSimplex R M → T) :
    Continuous f ↔
      ∀ (ι : Type v) [Finite ι] (g : ι → M), Continuous (f ∘ map g) := by
  rw [continuous_iSup_dom]
  refine forall_congr' (fun ι ↦ ?_)
  rw [continuous_iSup_dom]
  refine forall_congr' (fun _ ↦ ?_)
  rw [continuous_iSup_dom]
  refine forall_congr' (fun M ↦ ?_)
  rw [continuous_coinduced_dom, topologicalSpace_eq]

@[fun_prop]
lemma continuous_map {M : Type*} {N : Type v} (f : M → N) :
    Continuous (map (R := R) f) := by
  wlog h : Finite M generalizing M
  · rw [continuous_iff]
    intro ι _ g
    rw [← map_comp']
    exact this (f ∘ g) inferInstance
  have H {ι : Type v} [Finite ι] (g : ι → N) : Continuous (map (R := R) g) := by
    rw [continuous_iff_coinduced_le]
    refine le_trans ?_ (le_iSup _ ι)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ g)
    rw [topologicalSpace_eq]
  obtain ⟨ι, _, ⟨e⟩⟩ : ∃ (ι : Type v) (_ : Finite ι), Nonempty (M ≃ ι) :=
    ⟨_, inferInstance, ⟨(Finite.equivFin M).trans Equiv.ulift.{v}.symm⟩⟩
  have : Continuous (map (R := R) e) := by
    rw [topologicalSpace_eq, topologicalSpace_eq]
    apply topologicalSpaceInduced.continuous_map
  convert (H (f ∘ e.symm)).comp this
  rw [← map_comp', Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

open Classical in
/-- Same as `StdSimplex.continuous_iff` but only for inclusions of finite subsets of `M`. -/
lemma continuous_iff'
    {M T : Type*} [TopologicalSpace T] (f : StdSimplex R M → T) :
    Continuous f ↔ ∀ (s : Finset M), Continuous (f ∘ map (Subtype.val : s → M)) := by
  rw [continuous_iff]
  refine ⟨fun h s ↦ h _ _, fun h ι _ g ↦ ?_⟩
  have := Fintype.ofFinite ι
  have := (h (Finset.image g .univ)).comp
    (continuous_map R (fun i ↦ (⟨g i, by simp⟩ : (Finset.image g .univ : Set M))))
  rwa [Function.comp_assoc, ← map_comp'] at this

open topologicalSpaceInduced in
@[fun_prop]
lemma continuous_weights_apply {M : Type*} (m : M) :
    Continuous (fun (t : StdSimplex R M) ↦ t.weights m) := by
  rw [continuous_iff]
  intro ι _ g
  rw [topologicalSpace_eq]
  exact continuous_map_weights_apply R g m

lemma isEmbedding_toFun_comp_weights (M : Type*) [Finite M] :
    IsEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h

lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

namespace StdSimplex

section Real

variable (M : Type*)

lemma range_toFun_comp_weights_subset_closedBall [Fintype M] :
    Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ) ⊆ Metric.closedBall 0 1 := by
  rintro _ ⟨x, rfl⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [x.weights_nonneg i], x.weights_apply_le_one i⟩

lemma isBounded_range_toFun_comp_weights [Finite M] :
    Bornology.IsBounded (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) := by
  have := Fintype.ofFinite M
  exact Bornology.IsBounded.subset Metric.isBounded_closedBall
    (range_toFun_comp_weights_subset_closedBall M)

lemma diam_range_toFun_comp_weights_subset_closedBall [Fintype M] :
    Metric.diam (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) ≤ 1 :=
  Metric.diam_le_of_forall_dist_le (by simp) (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [dist_pi_le_iff zero_le_one]
    intro i
    rw [Real.dist_eq, abs_le]
    have := x.weights_nonneg i
    have := y.weights_nonneg i
    have := x.weights_apply_le_one i
    have := y.weights_apply_le_one i
    constructor <;> linarith)

lemma diam_range_toFun_comp_weights_subset_closedBall_eq_zero
    [Fintype M] [Subsingleton M] :
    Metric.diam (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) = 0 :=
  Metric.diam_subsingleton (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    obtain rfl : x = y := by subsingleton
    simp)

open Classical in
lemma diam_range_toFun_comp_weights_subset_closedBall_eq_one
    [Fintype M] [Nontrivial M] :
    Metric.diam (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) = 1 := by
  obtain ⟨x, y, h⟩ := exists_pair_ne M
  refine le_antisymm (diam_range_toFun_comp_weights_subset_closedBall M) ?_
  have hd : dist (⇑(single (R := ℝ) x).weights) (⇑(single (R := ℝ) y).weights) ≤
      Metric.diam (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) :=
    Metric.dist_le_diam_of_mem (isBounded_range_toFun_comp_weights _)
      ⟨.single x, rfl⟩ ⟨.single y, rfl⟩
  refine le_trans ?_ hd
  refine le_trans ?_ (dist_le_pi_dist _ _ x)
  simp [weights_single, Finsupp.single_apply, h, Real.dist_eq]

end Real

instance compactSpace (R M : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R] [OrderClosedTopology R]
    [Finite M] :
    CompactSpace (StdSimplex R M) where
  isCompact_univ := by
    rw [(isEmbedding_toFun_comp_weights R M).isCompact_iff, Set.image_univ]
    refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
      (isClosedEmbedding_toFun_comp_weights R M).isClosed_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fun i => x.weights_nonneg i, fun i => x.weights_apply_le_one i⟩

end StdSimplex

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

namespace StdSimplex

variable {K M : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the standard simplex with vertices `M`, the barycenter of a nonempty finite subset `S`. -/
@[simps -isSimp]
noncomputable def subBarycenter (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m (S.card : K)⁻¹)
  nonneg := Finset.sum_nonneg (fun m _ => by
    classical
    intro i
    rw [Finsupp.single_apply]
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_pos.mpr hS).ne')

lemma subBarycenter_weights_apply_eq_zero
    (S : Finset M) (hS : S.Nonempty) (m : M) (hm : m ∉ S) :
    (subBarycenter (K := K) S hS).weights m = 0 := by
  simp only [weights_subBarycenter, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_zero]
  intro x hx
  rw [Finsupp.single_apply_eq_zero]
  rintro rfl
  exact (hm hx).elim

@[simp]
lemma subBarycenter_singleton (m : M) :
    subBarycenter (K := K) {m} (by simp) = .single m := by
  ext
  simp [weights_subBarycenter]

/-- The barycenter of the standard simplex. -/
noncomputable abbrev barycenter [Nonempty M] [Fintype M] : StdSimplex K M :=
  subBarycenter .univ (by simp)

lemma weights_barycenter_apply [Nonempty M] [Fintype M] (m : M) :
    (barycenter (K := K) (M := M)).weights m = (Fintype.card M : K)⁻¹ := by
  classical
  simp [barycenter, weights_subBarycenter, Finsupp.single_apply]

lemma barycenter_of_unique [Unique M] :
    barycenter (K := K) (M := M) = .single default := by
  subsingleton

@[simp]
lemma barycenter_fin_one :
    barycenter (K := K) (M := Fin 1) = .single 0 :=
  barycenter_of_unique

end StdSimplex

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

namespace StdSimplex

open Classical in
@[fun_prop]
lemma continuous_convexCombPair {M : Type*} (x y : StdSimplex ℝ M) :
    Continuous (fun t ↦ convexCombPair (R := ℝ) (unitInterval.symm t) t
        (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) x y) := by
  wlog hM : Finite M
  · let s : Finset M := x.weights.support ∪ y.weights.support
    let ι : s → M := Subtype.val
    obtain ⟨x', hx⟩ := (mem_range_map_iff ι x).2 (by
      intro m hm
      by_contra hne
      exact hm ⟨⟨m, Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hne)⟩, rfl⟩)
    obtain ⟨y', hy⟩ := (mem_range_map_iff ι y).2 (by
      intro m hm
      by_contra hne
      exact hm ⟨⟨m, Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hne)⟩, rfl⟩)
    simp only [← hx, ← hy]
    convert (StdSimplex.continuous_map ℝ ι).comp
      (this x' y' (by dsimp [s]; infer_instance)) using 1
    ext t : 1
    exact ((isAffineMap_map ℝ ι).map_convexCombPair ..).symm
  rw [(StdSimplex.isEmbedding_toFun_comp_weights _ _).continuous_iff]
  unfold Function.comp
  refine continuous_pi (fun i ↦ ?_)
  simp only [unitInterval.coe_symm_eq, weights_convexCombPair, Finsupp.coe_add,
    Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

@[fun_prop]
lemma continuous_duple {M : Type*} (x y : M) :
    Continuous (fun t ↦ duple (R := ℝ) x y
      (unitInterval.nonneg (unitInterval.symm t)) (unitInterval.nonneg t) (by simp)) := by
  convert continuous_convexCombPair (.single x) (.single y) using 1
  ext t : 1
  ext : 1
  simp [weights_convexCombPair]

instance pathConnectedSpace
    (M : Type*) [Nonempty M] : PathConnectedSpace (StdSimplex ℝ M) where
  nonempty := by infer_instance
  joined x y :=
  ⟨{toContinuousMap := ⟨_, continuous_convexCombPair x y⟩
    source' := by simp [convexCombPair_one]
    target' := by simp [convexCombPair_zero] }⟩

/-- The standard one-dimensional simplex is homeomorphic to the unit interval. -/
noncomputable def homeomorphI : StdSimplex ℝ (Fin 2) ≃ₜ unitInterval where
  toEquiv := equivIcc
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_weights_apply ℝ 1
  continuous_invFun := by
    rw [(isEmbedding_toFun_comp_weights ℝ (Fin 2)).continuous_iff]
    refine continuous_pi (fun i ↦ ?_)
    fin_cases i
    · simp [equivIcc, Finsupp.single_apply]
      fun_prop
    · simp [equivIcc, Finsupp.single_apply]
      fun_prop

@[local simp]
lemma homeomorphI_apply_coe (s : StdSimplex ℝ (Fin 2)) :
    (homeomorphI s).val = s.weights 1 := by
  rfl

@[simp]
lemma homeomorphI_single_zero : homeomorphI (.single 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma homeomorphI_single_one : homeomorphI (.single 1) = 1 := by
  ext
  simp

@[simp]
lemma homeomorphI_symm_zero : homeomorphI.symm 0 = .single 0 :=
  homeomorphI.injective (by simp)

@[simp]
lemma homeomorphI_symm_one : homeomorphI.symm 1 = .single 1 :=
  homeomorphI.injective (by simp)

end StdSimplex

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

namespace OAI

/-- The standard simplex on a finite type, as the subtype `stdSimplex R X`
(the topological simplex of this Mathlib's `SimplexCategory.toTop`). -/
abbrev SStd (R : Type*) [Semiring R] [PartialOrder R] (X : Type*) [Fintype X] : Type _ :=
  ↥(stdSimplex R X)

namespace SStd

section Semiring

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- The weights as a finitely supported function. -/
noncomputable def weights (s : SStd R X) : X →₀ R := Finsupp.equivFunOnFinite.symm s.1

lemma weights_apply (s : SStd R X) (x : X) : s.weights x = s.1 x := rfl

lemma coe_weights (s : SStd R X) : ⇑s.weights = s.1 := rfl

lemma weights_nonneg (s : SStd R X) (x : X) : 0 ≤ s.weights x := s.2.1 x

lemma total_of_fintype (s : SStd R X) : ∑ x, s.weights x = 1 := s.2.2

lemma ext {s t : SStd R X} (h : s.weights = t.weights) : s = t :=
  Subtype.ext (congrArg (fun f : X →₀ R => (f : X → R)) h)

@[simp] lemma weights_inj {s t : SStd R X} : s.weights = t.weights ↔ s = t :=
  ⟨ext, fun h => h ▸ rfl⟩

lemma weights_apply_le_one [IsOrderedAddMonoid R] (s : SStd R X) (x : X) : s.weights x ≤ 1 := by
  rw [← s.total_of_fintype]
  exact Finset.single_le_sum (fun y _ => s.weights_nonneg y) (Finset.mem_univ x)

/-- The structure `Convexity.StdSimplex` with the same weights. -/
noncomputable def toStdSimplex (s : SStd R X) : Convexity.StdSimplex R X where
  weights := s.weights
  nonneg := fun x => s.weights_nonneg x
  total := by rw [Finsupp.sum_fintype _ _ (by simp)]; exact s.total_of_fintype

/-- The point of the subtype with the weights of a `Convexity.StdSimplex`. -/
def ofStdSimplex (s : Convexity.StdSimplex R X) : SStd R X :=
  ⟨⇑s.weights, fun x => s.weights_nonneg x, by
    have := s.total
    rwa [Finsupp.sum_fintype _ _ (by simp)] at this⟩

@[simp] lemma weights_toStdSimplex (s : SStd R X) : s.toStdSimplex.weights = s.weights := rfl

@[simp] lemma weights_ofStdSimplex (s : Convexity.StdSimplex R X) :
    (ofStdSimplex s).weights = s.weights := by
  ext x
  rfl

/-- `SStd R X` and `Convexity.StdSimplex R X` are in bijection, weights preserved. -/
noncomputable def equivStdSimplex : SStd R X ≃ Convexity.StdSimplex R X where
  toFun := toStdSimplex
  invFun := ofStdSimplex
  left_inv s := ext (by simp)
  right_inv s := by
    ext : 1
    simp

end Semiring

section OrderedRing

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Push a simplex point forward along a map of index types (this Mathlib's `stdSimplex.map`). -/
noncomputable def map (g : X → Y) (s : SStd R X) : SStd R Y := stdSimplex.map g s

lemma map_val_apply [DecidableEq Y] (g : X → Y) (s : SStd R X) (y : Y) :
    (map g s).1 y = ∑ x ∈ Finset.univ.filter (fun x => g x = y), s.1 x := by
  change (FunOnFinite.linearMap R R g s.1) y = _
  rw [FunOnFinite.linearMap_apply_apply]

@[simp] lemma weights_map (g : X → Y) (s : SStd R X) :
    (map g s).weights = s.weights.mapDomain g := by
  classical
  ext y
  rw [weights_apply, map_val_apply, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
    Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, Finset.sum_filter, weights_apply]

lemma map_comp (s : SStd R X) (g₁ : X → Y) (g₂ : Y → Z) :
    map (g₂ ∘ g₁) s = map g₂ (map g₁ s) :=
  (stdSimplex.map_comp_apply g₁ g₂ s).symm

@[simp] lemma map_id (s : SStd R X) : map id s = s := stdSimplex.map_id_apply s

lemma map_map (s : SStd R X) (g₁ : X → Y) (g₂ : Y → Z) :
    map g₂ (map g₁ s) = map (fun x => g₂ (g₁ x)) s :=
  (map_comp s g₁ g₂).symm

/-- The vertex (point mass) at `x`. -/
noncomputable def single (x : X) : SStd R X := by
  classical
  exact ⟨Pi.single x 1, single_mem_stdSimplex R x⟩

@[simp] lemma weights_single (x : X) : (single (R := R) x).weights = Finsupp.single x 1 := by
  classical
  ext y
  simp only [weights_apply, single, Finsupp.single_apply, Pi.single_apply, eq_comm]

@[simp] lemma single_val_apply [DecidableEq X] (x y : X) :
    (single (R := R) x).1 y = if x = y then 1 else 0 := by
  classical
  simp only [single, Pi.single_apply, eq_comm]

@[simp] lemma single_coe_apply [DecidableEq X] (x y : X) :
    DFunLike.coe (F := stdSimplex R X) (single (R := R) x) y = if x = y then 1 else 0 :=
  single_val_apply x y

@[simp] lemma map_single (x : X) (f : X → Y) : map f (single (R := R) x) = single (f x) := by
  classical
  apply ext
  rw [weights_map, weights_single, weights_single, Finsupp.mapDomain_single]

@[simp] lemma map_const [Nontrivial R] (s : SStd R X) (y : Y) :
    map (fun _ => y) s = single y := by
  classical
  apply ext
  ext z
  rw [weights_map, weights_single, Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  by_cases h : y = z
  · simp [h, ← coe_weights, s.total_of_fintype]
  · simp [h]

lemma single_injective [Nontrivial R] : Function.Injective (single (R := R) (X := X)) := by
  intro x y h
  have := congrArg (fun s : SStd R X => s.weights x) h
  classical
  by_contra hxy
  simp [weights_single, Finsupp.single_apply, Ne.symm hxy] at this

end OrderedRing

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [Fintype X]

/-- The barycenter, with every weight `(card X)⁻¹`. -/
noncomputable def barycenter [Nonempty X] : SStd 𝕜 X := stdSimplex.barycenter

lemma weights_barycenter_apply [Nonempty X] (x : X) :
    (barycenter : SStd 𝕜 X).weights x = (Fintype.card X : 𝕜)⁻¹ := rfl

@[simp] lemma barycenter_val_apply [Nonempty X] (x : X) :
    (barycenter : SStd 𝕜 X).1 x = (Fintype.card X : 𝕜)⁻¹ := rfl

@[simp] lemma barycenter_coe_apply [Nonempty X] (x : X) :
    DFunLike.coe (F := stdSimplex 𝕜 X) (barycenter : SStd 𝕜 X) x = (Fintype.card X : 𝕜)⁻¹ := rfl

lemma barycenter_fin_one : (barycenter : SStd 𝕜 (Fin 1)) = single 0 := Subsingleton.elim _ _

end Field

section Topology

variable (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [IsTopologicalRing R]

lemma continuous_map {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y) :
    Continuous (map (R := R) f) := stdSimplex.continuous_map f

lemma continuous_weights_apply {X : Type*} [Fintype X] (x : X) :
    Continuous (fun s : SStd R X => s.weights x) :=
  (continuous_apply x).comp continuous_subtype_val

variable (M : Type*) [Fintype M]

lemma isEmbedding_toFun_comp_weights :
    Topology.IsEmbedding (fun t ↦ t.weights : SStd R M → M → R) :=
  Topology.IsEmbedding.subtypeVal

lemma range_toFun_comp_weights :
    Set.range (fun t ↦ t.weights : SStd R M → (M → R)) =
      (⋂ (i : M), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext f
  simp only [Set.mem_range, coe_weights, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.2.1, s.2.2⟩
  · intro hf
    exact ⟨⟨f, hf⟩, rfl⟩

lemma isClosedEmbedding_toFun_comp_weights [OrderClosedTopology R] :
    Topology.IsClosedEmbedding (fun t ↦ t.weights : SStd R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end Topology

section Real

variable (M : Type*) [Fintype M]

lemma range_toFun_comp_weights_eq_stdSimplex :
    Set.range (fun t ↦ t.weights : SStd ℝ M → M → ℝ) = stdSimplex ℝ M := by
  ext f
  simp only [Set.mem_range, coe_weights]
  exact ⟨by rintro ⟨s, rfl⟩; exact s.2, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩

lemma range_toFun_comp_weights_subset_closedBall :
    Set.range (fun t ↦ t.weights : SStd ℝ M → M → ℝ) ⊆ Metric.closedBall 0 1 := by
  rw [range_toFun_comp_weights_eq_stdSimplex]
  exact stdSimplex_subset_closedBall

lemma isBounded_range_toFun_comp_weights :
    Bornology.IsBounded (Set.range (fun t ↦ t.weights : SStd ℝ M → M → ℝ)) :=
  Metric.isBounded_closedBall.subset (range_toFun_comp_weights_subset_closedBall M)

lemma diam_range_toFun_comp_weights_subset_closedBall :
    Metric.diam (Set.range (fun t ↦ t.weights : SStd ℝ M → M → ℝ)) ≤ 1 := by
  rw [range_toFun_comp_weights_eq_stdSimplex]
  exact diam_stdSimplex_le

end Real

end SStd

end OAI

end StdSimplexCompat


