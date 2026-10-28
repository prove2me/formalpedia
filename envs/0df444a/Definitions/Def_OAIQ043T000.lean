-- Prove2me | Definitions.Def_OAIQ043T000
-- name    : OAIQ043T000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T09:39:28.595989+00:00
-- url     : https://prove2.me/theorems/ef6271ff-049c-46e5-997d-8b0e20af5fd4
-- title:
--   Definitions bundle OAIQ043T000 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 689 declarations of OpenAI's Lean: 229 definitions, 7 inductive types or structures, 27 instances and 426 theorems. The definitions and types are `Convexity.StdSimplex.equivIcc`, `Convexity.StdSimplex.subBarycenter`, `Convexity.StdSimplex.topologicalSpaceInduced`, `OAI.SStd`, `OAI.SStd.equivStdSimplex`, `OAI.SStd.homeoStdSimplex`, `OAI.SStd.ofStdSimplex`, `OAI.SStd.toStdSimplex`, `OAI.SStd.weights`, `OAI.Thomason.AbstractTransfer.Boundaries.Admissible`, `OAI.Thomason.AbstractTransfer.Boundaries.arrow`, `OAI.Thomason.AbstractTransfer.Cof`, `OAI.Thomason.AbstractTransfer.Fib`, `OAI.Thomason.AbstractTransfer.Horns.Admissible`, `OAI.Thomason.AbstractTransfer.Horns.arrow`, `OAI.Thomason.AbstractTransfer.Horns.oldCoprodIso`, `OAI.Thomason.AbstractTransfer.Horns.posetCoprodIso`, `OAI.Thomason.AbstractTransfer.L`, `OAI.Thomason.AbstractTransfer.PosetComparison`, `OAI.Thomason.AbstractTransfer.R`, `OAI.Thomason.AbstractTransfer.W`, `OAI.Thomason.AbstractTransfer.inc`, `OAI.Thomason.AbstractTransfer.posetObj`, `OAI.Thomason.AbstractTransfer.transferredAdjunction`, `OAI.Thomason.AttachmentComparison.upward`, `OAI.Thomason.BoundaryProperness.PosetAttachment`, `OAI.Thomason.CoherentGluing.toHomotopy`, `OAI.Thomason.DependentPosets.branch`, `OAI.Thomason.DependentPosets.componentIso`, `OAI.Thomason.DependentPosets.incl`, `OAI.Thomason.DependentPosets.isColimit`, `OAI.Thomason.DependentPosets.iso`, `OAI.Thomason.DependentPosets.old`, `OAI.Thomason.DependentPosets.oldIso`, `OAI.Thomason.DependentPosets.oldNerveIso`, `OAI.Thomason.DependentPosets.oldRetraction`, `OAI.Thomason.DependentPosets.oldUp`, `OAI.Thomason.DependentPosets.restricted`, `OAI.Thomason.GeometricRecognition.Approximation.affineMap`, `OAI.Thomason.GeometricRecognition.Contiguity.BasedHomotopy` and 196 more.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: `StdSimplexTopCompat`, `Thomason_BarycentricMesh`, `Thomason_CoherentGluing`, `Thomason_CubicalGeometry`, `Thomason_CubicalRecognition`, `Thomason_DimensionOne`, `Thomason_ExtensionAnodyne`, `Thomason_FiberRecognition`, `Thomason_Globes`, `Thomason_GlobularComplexes`, `Thomason_HomotopyExtension`, `Thomason_KanQuillen`, `Thomason_KanTowers`, `Thomason_ModelTransfer`, `Thomason_PartialPrisms`, `Thomason_Polyhedra`, `Thomason_PosetalColimits`, `Thomason_PosetalReduction`, `Thomason_ProperTransfer`, `Thomason_RelativeContiguity`, `Thomason_RelativeRepresentation`, `Thomason_SieveAttachments`, `Thomason_SimplexBoxes`, `Thomason_SimplicialApproximation`, `Thomason_SubdividedUnit`, `Thomason_SubdivisionFaces`, `Thomason_SubdivisionMaps`, `Thomason_SubdivisionNerves`, `Thomason_SubdivisionPairing`, `Thomason_SubdivisionWeak`.
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ043T002` and `OAIQ043T003`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures

section
-- module Solutions.OAIQ043_TH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
/-- Mathlib d13f23b's `Finsupp.mapDomain_fintype`: on a finite index type `mapDomain f v` is the
sum of the point masses at the images (Thomason Polyhedra, oaiq-043). -/
theorem _root_.Finsupp.mapDomain_fintype {α β M : Type*} [Fintype α] [AddCommMonoid M]
    (f : α → β) (v : α →₀ M) : Finsupp.mapDomain f v = ∑ i, Finsupp.single (f i) (v i) := by
  rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp)]

end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ043_TH.StdSimplexCompat
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

instance instUnique [Unique X] : Unique (StdSimplex R X) where
  uniq := by subsingleton

lemma map_id' : map (R := R) (id : X → X) = id := by
  funext f
  exact map_id f

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

@[simp]
lemma subBarycenter_singleton (m : M) :
    subBarycenter (K := K) {m} (by simp) = .single m := by
  ext
  simp [weights_subBarycenter]

end StdSimplex

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

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

lemma weights_nonneg (s : SStd R X) (x : X) : 0 ≤ s.weights x := s.2.1 x

lemma total_of_fintype (s : SStd R X) : ∑ x, s.weights x = 1 := s.2.2

lemma ext {s t : SStd R X} (h : s.weights = t.weights) : s = t :=
  Subtype.ext (congrArg (fun f : X →₀ R => (f : X → R)) h)

@[simp] lemma weights_inj {s t : SStd R X} : s.weights = t.weights ↔ s = t :=
  ⟨ext, fun h => h ▸ rfl⟩

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

end SStd

end OAI

end StdSimplexCompat
end

section
-- module Solutions.OAIQ043_TH.StdSimplexTopCompat
open CategoryTheory Simplicial

noncomputable section

/-! ## Part 3: `SimplexCategory.toTopHomeoD`, `toTopHomeo` with the structure `Convexity.StdSimplex` -/

namespace OAI.SStd

/-- The subtype `stdSimplex ℝ X` and the structure `Convexity.StdSimplex ℝ X` are homeomorphic. -/
noncomputable def homeoStdSimplex (X : Type*) [Fintype X] :
    SStd ℝ X ≃ₜ Convexity.StdSimplex ℝ X where
  toEquiv := equivStdSimplex
  continuous_toFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ X).continuous_iff.mpr
    exact continuous_pi fun k => (continuous_apply k).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun k => ?_
    exact Convexity.StdSimplex.continuous_weights_apply ℝ k

end OAI.SStd
end
end

section
-- module Solutions.OAIQ043_TH.Thomason_Polyhedra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polyhedra. -/

noncomputable section
universe u v w z


namespace Thomason.GeometricRecognition

@[ext] structure PolyPoint (P : Type u) [PartialOrder P] where
  weights : P →₀ ℝ
  nonneg : ∀ p, 0 ≤ weights p
  total : weights.sum (fun _ r => r) = 1
  chain : IsChain (· ≤ ·) (weights.support : Set P)

namespace PolyPoint
variable {P : Type u} [PartialOrder P]
local instance polyhedraDecidableEq : DecidableEq P := Classical.decEq P

def Face (s : Finset P) := {x : PolyPoint P // x.weights.support ⊆ s}

instance faceTopology (s : Finset P) : TopologicalSpace (Face s) :=
  TopologicalSpace.induced (fun x p => x.val.weights p) inferInstance

structure ChainIndex (P : Type u) [PartialOrder P] where
  carrier : Finset P
  chain : IsChain (· ≤ ·) (carrier : Set P)
  nonempty : carrier.Nonempty

instance weakTopology : TopologicalSpace (PolyPoint P) :=
  TopologicalSpace.coinduced
    (fun x : Σ s : ChainIndex P, Face s.carrier => x.2.val) inferInstance

lemma isClosed_iff_faces (A : Set (PolyPoint P)) :
    IsClosed A ↔ ∀ s : ChainIndex P,
      IsClosed ((fun x : Face s.carrier => x.val) ⁻¹' A) := by
  rw [isClosed_coinduced, isClosed_sigma_iff]
  rfl

lemma continuous_chainFace_val (s : ChainIndex P) :
    Continuous (fun x : Face s.carrier => x.val) := by
  have h : Continuous (fun x : Σ s : ChainIndex P, Face s.carrier => x.2.val) :=
    continuous_coinduced_rng
  exact h.comp (continuous_sigmaMk (i := s))

lemma continuous_weights (p : P) : Continuous (fun x : PolyPoint P => x.weights p) := by
  rw [continuous_coinduced_dom]
  apply continuous_sigma
  intro s
  exact (continuous_apply p).comp continuous_induced_dom

instance instT2Space : T2Space (PolyPoint P) :=
  T2Space.of_injective_continuous (f := fun x : PolyPoint P => (fun p => x.weights p))
    (by intro x y h; exact PolyPoint.ext (Finsupp.ext (congrFun h)))
    (continuous_pi continuous_weights)

def evalWeights {ι : Type*} [Fintype ι] (a : ι → P) (x : Convexity.StdSimplex ℝ ι) : P →₀ ℝ :=
  ∑ i, Finsupp.single (a i) (x.weights i)

omit [PartialOrder P] in
lemma evalWeights_support {ι : Type*} [Fintype ι] (a : ι → P) (x : Convexity.StdSimplex ℝ ι) :
    (evalWeights a x).support ⊆ Finset.univ.image a := by
  classical
  intro p hp
  by_contra h
  apply Finsupp.mem_support_iff.mp hp
  rw [evalWeights, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact Finsupp.single_eq_of_ne (by
    intro he
    apply h
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩)

def eval {ι : Type*} [Fintype ι] [LinearOrder ι] (a : ι →o P)
    (x : Convexity.StdSimplex ℝ ι) : PolyPoint P where
  weights := evalWeights a x
  nonneg p := by
    classical
    rw [evalWeights, Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg (fun i _ => by
      rw [Finsupp.single_apply]
      split_ifs
      · exact x.weights_nonneg i
      · exact le_rfl)
  total := by
    rw [evalWeights, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simpa only [Finsupp.sum_single_index] using x.total_of_fintype
  chain := by
    classical
    intro p hp q hq hpq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (evalWeights_support a x hp)
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (evalWeights_support a x hq)
    rcases le_total i j with h | h
    · exact Or.inl (a.monotone h)
    · exact Or.inr (a.monotone h)

lemma continuous_eval {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] (a : ι →o P) :
    Continuous (eval a) := by
  classical
  let s := Finset.univ.image a
  let f : Convexity.StdSimplex ℝ ι → Face s := fun x => ⟨eval a x, evalWeights_support a x⟩
  have hf : Continuous f := by
    rw [continuous_induced_rng]
    apply continuous_pi
    intro p
    change Continuous (fun x : Convexity.StdSimplex ℝ ι => (evalWeights a x) p)
    simp only [evalWeights, Finsupp.finsetSum_apply, Finsupp.single_apply]
    apply continuous_finsetSum
    intro i hi
    split_ifs
    · exact Convexity.StdSimplex.continuous_weights_apply ℝ i
    · exact continuous_const
  let c : ChainIndex P := ⟨s, by
    intro p hp q hq hpq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    rcases le_total i j with h | h
    · exact Or.inl (a.monotone h)
    · exact Or.inr (a.monotone h),
    Finset.image_nonempty.mpr Finset.univ_nonempty⟩
  exact (continuous_chainFace_val c).comp hf

omit [PartialOrder P] in
lemma evalWeights_apply_image {ι : Type*} [Fintype ι] (a : ι → P)
    (ha : Function.Injective a) (x : Convexity.StdSimplex ℝ ι) (i : ι) :
    evalWeights a x (a i) = x.weights i := by
  classical
  simp only [evalWeights, Finsupp.finsetSum_apply, Finsupp.single_apply, ha.eq_iff]
  simp

namespace ChainIndex

instance carrierLinearOrder (s : ChainIndex P) : LinearOrder s.carrier := by
  classical
  exact s.chain.linearOrder

def dimension (s : ChainIndex P) : ℕ := s.carrier.card - 1

lemma card_eq (s : ChainIndex P) : Fintype.card s.carrier = s.dimension + 1 := by
  rw [Fintype.card_coe]
  have h := Finset.card_pos.mpr s.nonempty
  dsimp [dimension]
  omega

def enumerate (s : ChainIndex P) : Fin (s.dimension + 1) ≃o s.carrier :=
  Fintype.orderIsoFinOfCardEq s.carrier s.card_eq

def vertices (s : ChainIndex P) : Fin (s.dimension + 1) →o P :=
  (OrderHom.Subtype.val _).comp s.enumerate.toOrderEmbedding.toOrderHom

lemma vertices_injective (s : ChainIndex P) : Function.Injective s.vertices :=
  Subtype.val_injective.comp s.enumerate.injective

lemma vertices_mem (s : ChainIndex P) (i : Fin (s.dimension + 1)) :
    s.vertices i ∈ s.carrier := (s.enumerate i).property

lemma vertices_surjective (s : ChainIndex P) {p : P} (hp : p ∈ s.carrier) :
    ∃ i, s.vertices i = p := by
  obtain ⟨i,hi⟩ := s.enumerate.surjective ⟨p,hp⟩
  exact ⟨i,congrArg Subtype.val hi⟩

def coordinates (s : ChainIndex P) (x : Face s.carrier) :
    Convexity.StdSimplex ℝ (Fin (s.dimension + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (fun index => x.val.weights (s.vertices index))
  nonneg index := x.val.nonneg (s.vertices index)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ index, x.val.weights (s.vertices index) = 1
    calc
      ∑ i, x.val.weights (s.vertices i) = ∑ p : s.carrier, x.val.weights p.val :=
        Equiv.sum_comp s.enumerate.toEquiv (fun p : s.carrier => x.val.weights p.val)
      _ = ∑ p ∈ s.carrier, x.val.weights p := Finset.sum_attach _ _
      _ = 1 := (x.val.weights.sum_of_support_subset x.property (fun _ r => r)
        (fun _ _ => rfl)).symm.trans x.val.total

lemma eval_coordinates (s : ChainIndex P) (x : Face s.carrier) :
    eval s.vertices (s.coordinates x) = x.val := by
  apply PolyPoint.ext
  ext p
  by_cases hp : p ∈ s.carrier
  · obtain ⟨i,rfl⟩ := s.vertices_surjective hp
    exact evalWeights_apply_image s.vertices s.vertices_injective _ i
  · change evalWeights s.vertices (s.coordinates x) p = x.val.weights p
    have hz : x.val.weights p = 0 := Finsupp.notMem_support_iff.mp
      (fun h => hp (x.property h))
    rw [hz]
    apply Finsupp.notMem_support_iff.mp
    intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (evalWeights_support s.vertices _ h)
    exact hp (he ▸ s.vertices_mem i)

end ChainIndex

def supportIndex (x : PolyPoint P) : ChainIndex P :=
  ⟨x.weights.support, x.chain, by
    apply Finsupp.support_nonempty_iff.mpr
    intro h
    have ht := x.total
    rw [h, Finsupp.sum_zero_index] at ht
    norm_num at ht⟩

end PolyPoint

open CategoryTheory Limits Simplicial Opposite

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Simplicial Opposite PartialOrder

namespace Thomason.GeometricRecognition
namespace PolyPoint
variable {P : Type u} [PartialOrder P]
local instance barycenterDecidableEq : DecidableEq P := Classical.decEq P

def barycenter (s : NonemptyFiniteChains P) : PolyPoint P where
  weights := ∑ p ∈ s.finset, Finsupp.single p (s.finset.card : ℝ)⁻¹
  nonneg p := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg (fun q hq => by simp [Finsupp.single_apply]; positivity)
  total := by
    rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simp only [Finsupp.sum_single_index, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_ne_zero.mpr s.nonempty))
  chain := by
    have hs : (∑ p ∈ s.finset, Finsupp.single p (s.finset.card : ℝ)⁻¹).support ⊆ s.finset := by
      intro p hp
      by_contra h
      apply Finsupp.mem_support_iff.mp hp
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro q hq
      exact Finsupp.single_eq_of_ne (fun he => h (he ▸ hq))
    intro p hp q hq hpq
    exact s.comparable ⟨p,hs hp⟩ ⟨q,hs hq⟩

lemma barycenter_apply (s : NonemptyFiniteChains P) (p : P) :
    (barycenter s).weights p = if p ∈ s.finset then (s.finset.card : ℝ)⁻¹ else 0 := by
  classical
  simp [barycenter, Finsupp.finsetSum_apply, Finsupp.single_apply]

def barycentricLinear : (NonemptyFiniteChains P →₀ ℝ) →ₗ[ℝ] (P →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun s => (barycenter s).weights)

lemma barycentricLinear_apply (g : NonemptyFiniteChains P →₀ ℝ) (p : P) :
    barycentricLinear g p =
      g.sum (fun s r => r * (barycenter s).weights p) := by
  simp [barycentricLinear, Finsupp.linearCombination_apply, Finsupp.sum_apply]

lemma barycentricLinear_total (g : NonemptyFiniteChains P →₀ ℝ) :
    (barycentricLinear g).sum (fun _ r => r) = g.sum (fun _ r => r) := by
  rw [barycentricLinear, Finsupp.linearCombination_apply,
    Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  apply Finsupp.sum_congr
  intro s hs
  rw [Finsupp.sum_smul_index (fun _ => rfl)]
  change (barycenter s).weights.sum (fun _ r => g s * r) = g s
  rw [Finsupp.sum, ← Finset.mul_sum]
  simpa only [Finsupp.sum, mul_one] using
    congrArg (fun r : ℝ => g s * r) (barycenter s).total

lemma barycentric_cone_step (f : P →₀ ℝ) (hn : ∀ p, 0 ≤ f p)
    (hc : IsChain (· ≤ ·) (f.support : Set P)) (hf : f ≠ 0) :
    ∃ (s : NonemptyFiniteChains P) (c : ℝ) (h : P →₀ ℝ),
      s.finset = f.support ∧ 0 < c ∧ (∀ p, 0 ≤ h p) ∧
      h.support ⊂ f.support ∧ f = h + c • (barycenter s).weights := by
  classical
  have hne : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image f.support f hne
  let s : NonemptyFiniteChains P :=
    ⟨f.support, hne, fun p q => hc.total p.property q.property⟩
  let c : ℝ := f p * (f.support.card : ℝ)
  let h : P →₀ ℝ := f - c • (barycenter s).weights
  have hcard : (f.support.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  have hpos : 0 < f p := lt_of_le_of_ne (hn p) (Ne.symm (Finsupp.mem_support_iff.mp hp))
  have hcpos : 0 < c := mul_pos hpos (by exact_mod_cast Finset.card_pos.mpr hne)
  have heval (q : P) : h q = if q ∈ f.support then f q - f p else 0 := by
    simp only [h, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, barycenter_apply]
    change f q - c * (if q ∈ f.support then (f.support.card : ℝ)⁻¹ else 0) = _
    split_ifs with hq
    · dsimp [c]
      rw [mul_assoc, mul_inv_cancel₀ hcard, mul_one]
    · rw [Finsupp.notMem_support_iff.mp hq]
      simp
  have hsub : h.support ⊆ f.support.erase p := by
    intro q hq
    rw [Finsupp.mem_support_iff, heval] at hq
    by_cases hqs : q ∈ f.support
    · refine Finset.mem_erase.mpr ⟨?_, hqs⟩
      intro he
      subst q
      simp [hp] at hq
    · simp [hqs] at hq
  refine ⟨s,c,h,rfl,hcpos,?_,?_,?_⟩
  · intro q
    rw [heval]
    split_ifs with hq
    · exact sub_nonneg.mpr (hmin q hq)
    · exact le_rfl
  · exact Finset.ssubset_of_subset_of_ssubset hsub (Finset.erase_ssubset hp)
  · dsimp [h]
    abel

lemma exists_barycentric_decomposition (f : P →₀ ℝ) (hn : ∀ p, 0 ≤ f p)
    (hc : IsChain (· ≤ ·) (f.support : Set P)) :
    ∃ g : NonemptyFiniteChains P →₀ ℝ,
      (∀ s, 0 ≤ g s) ∧ IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains P)) ∧
      (∀ s ∈ g.support, s.finset ⊆ f.support) ∧ barycentricLinear g = f := by
  classical
  suffices ∀ (S : Finset P) (f : P →₀ ℝ), f.support = S →
      (∀ p, 0 ≤ f p) → IsChain (· ≤ ·) (f.support : Set P) →
      ∃ g : NonemptyFiniteChains P →₀ ℝ,
        (∀ s, 0 ≤ g s) ∧ IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains P)) ∧
        (∀ s ∈ g.support, s.finset ⊆ f.support) ∧ barycentricLinear g = f by
    exact this _ f rfl hn hc
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro f hS hn hc
    by_cases hf : f = 0
    · subst f
      refine ⟨0, by simp, ?_, by simp, by simp⟩
      simp
    obtain ⟨s,c,h,hs,hcpos,hnn,hsub,heq⟩ := barycentric_cone_step f hn hc hf
    obtain ⟨g,hgn,hgc,hgs,hge⟩ := ih h.support (hS ▸ hsub) h rfl hnn
      (hc.mono (by simpa using hsub.subset))
    let g' : NonemptyFiniteChains P →₀ ℝ := g + Finsupp.single s c
    have hmem (t : NonemptyFiniteChains P) (ht : t ∈ g'.support) :
        t ∈ g.support ∨ t = s := by
      have hm := Finsupp.support_add ht
      rcases Finset.mem_union.mp hm with ht0 | ht0
      · exact Or.inl ht0
      · right
        by_contra htne
        exact (Finsupp.mem_support_iff.mp ht0) (Finsupp.single_eq_of_ne htne)
    have hle (t : NonemptyFiniteChains P) (ht : t ∈ g.support) : t ≤ s := by
      change t.finset ⊆ s.finset
      rw [hs]
      exact (hgs t ht).trans hsub.subset
    refine ⟨g', ?_, ?_, ?_, ?_⟩
    · intro t
      dsimp [g']
      exact add_nonneg (hgn t) (by simp [Finsupp.single_apply]; positivity)
    · intro a ha b hb hab
      rcases hmem a ha with ha0 | ha0
      · rcases hmem b hb with hb0 | hb0
        · exact hgc ha0 hb0 hab
        · exact Or.inl (hb0.symm ▸ hle a ha0)
      · rcases hmem b hb with hb0 | hb0
        · exact Or.inr (ha0.symm ▸ hle b hb0)
        · exact (hab (ha0.trans hb0.symm)).elim
    · intro t ht
      rcases hmem t ht with ht | rfl
      · exact (hgs t ht).trans hsub.subset
      · exact hs ▸ Finset.Subset.refl _
    · dsimp [g']
      rw [map_add, hge]
      rw [barycentricLinear, Finsupp.linearCombination_single]
      exact heq.symm

lemma barycentricLinear_nonneg (g : NonemptyFiniteChains P →₀ ℝ)
    (hg : ∀ s, 0 ≤ g s) (p : P) : 0 ≤ barycentricLinear g p := by
  rw [barycentricLinear_apply, Finsupp.sum]
  exact Finset.sum_nonneg (fun s hs => mul_nonneg (hg s) ((barycenter s).nonneg p))

lemma barycentricLinear_support (g : NonemptyFiniteChains P →₀ ℝ) :
    (barycentricLinear g).support ⊆ g.support.biUnion NonemptyFiniteChains.finset := by
  classical
  intro p hp
  by_contra hnot
  apply Finsupp.mem_support_iff.mp hp
  rw [barycentricLinear_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro s hs
  have hpnot : p ∉ s.finset := fun h => hnot (Finset.mem_biUnion.mpr ⟨s,hs,h⟩)
  simp [barycenter_apply, hpnot]

lemma flagCarrier_chain (S : Finset (NonemptyFiniteChains P))
    (hc : IsChain (· ≤ ·) (S : Set (NonemptyFiniteChains P))) :
    IsChain (· ≤ ·) ((S.biUnion NonemptyFiniteChains.finset : Finset P) : Set P) := by
  classical
  intro p hp q hq hpq
  obtain ⟨s,hs,hps⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨t,ht,hqt⟩ := Finset.mem_biUnion.mp hq
  rcases hc.total hs ht with hst | hts
  · exact t.comparable ⟨p,hst hps⟩ ⟨q,hqt⟩
  · exact s.comparable ⟨p,hps⟩ ⟨q,hts hqt⟩

def subdivide (x : PolyPoint (NonemptyFiniteChains P)) : PolyPoint P where
  weights := barycentricLinear x.weights
  nonneg := barycentricLinear_nonneg x.weights x.nonneg
  total := (barycentricLinear_total x.weights).trans x.total
  chain := (flagCarrier_chain x.weights.support x.chain).mono
    (fun _ hp => barycentricLinear_support x.weights hp)

lemma subdivide_surjective : Function.Surjective (@subdivide P _) := by
  intro x
  obtain ⟨g,hn,hc,hs,hg⟩ := exists_barycentric_decomposition x.weights x.nonneg x.chain
  have ht : g.sum (fun _ r => r) = 1 := by
    rw [← barycentricLinear_total, hg]
    exact x.total
  exact ⟨⟨g,hn,ht,hc⟩, PolyPoint.ext hg⟩

lemma continuous_subdivide : Continuous (@subdivide P _) := by
  classical
  rw [continuous_coinduced_dom]
  apply continuous_sigma
  intro s
  let t : ChainIndex P :=
    ⟨s.carrier.biUnion NonemptyFiniteChains.finset, flagCarrier_chain s.carrier s.chain, by
      obtain ⟨a,ha⟩ := s.nonempty
      obtain ⟨p,hp⟩ := a.nonempty
      exact ⟨p, Finset.mem_biUnion.mpr ⟨a,ha,hp⟩⟩⟩
  let f : Face s.carrier → Face t.carrier := fun x => ⟨subdivide x.val, by
    intro p hp
    obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp (barycentricLinear_support x.val.weights hp)
    exact Finset.mem_biUnion.mpr ⟨a,x.property ha,hpa⟩⟩
  have hf : Continuous f := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro p
    have he (x : Face s.carrier) :
        (f x).val.weights p = ∑ a ∈ s.carrier, x.val.weights a * (barycenter a).weights p := by
      change barycentricLinear x.val.weights p = _
      rw [barycentricLinear_apply]
      exact Finsupp.sum_of_support_subset _ x.property _ (by simp)
    have hc : Continuous (fun x : Face s.carrier =>
        ∑ a ∈ s.carrier, x.val.weights a * (barycenter a).weights p) := by
      apply continuous_finsetSum
      intro a ha
      have hca : Continuous (fun x : Face s.carrier => x.val.weights a) :=
        (continuous_apply a).comp continuous_induced_dom
      exact hca.mul continuous_const
    exact hc.congr (fun x => (he x).symm)
  exact (continuous_chainFace_val t).comp hf

end PolyPoint
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_BarycentricMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Barycentric Mesh. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.PolyPoint
variable {P : Type u} [PartialOrder P]
local instance barycentricMeshDecidableEq : DecidableEq P := Classical.decEq P

lemma barycentricLinear_support_eq (g : NonemptyFiniteChains P →₀ ℝ)
    (hg : ∀ s, 0 ≤ g s) :
    (barycentricLinear g).support = g.support.biUnion NonemptyFiniteChains.finset := by
  classical
  apply Finset.Subset.antisymm (barycentricLinear_support g)
  intro p hp
  obtain ⟨s,hs,hps⟩ := Finset.mem_biUnion.mp hp
  rw [Finsupp.mem_support_iff]
  apply ne_of_gt
  rw [barycentricLinear_apply, Finsupp.sum]
  apply (Finset.sum_pos_iff_of_nonneg (fun t ht =>
    mul_nonneg (hg t) ((barycenter t).nonneg p))).mpr
  refine ⟨s,hs,mul_pos ?_ ?_⟩
  · exact lt_of_le_of_ne (hg s) (Ne.symm (Finsupp.mem_support_iff.mp hs))
  · rw [barycenter_apply, ite_eq_left hps]
    exact inv_pos.mpr (by exact_mod_cast Finset.card_pos.mpr s.nonempty)

lemma barycentricLinear_eq_zero_iff (g : NonemptyFiniteChains P →₀ ℝ)
    (hg : ∀ s, 0 ≤ g s) : barycentricLinear g = 0 ↔ g = 0 := by
  classical
  constructor
  · intro he
    by_contra hg0
    obtain ⟨s,hs⟩ := Finsupp.support_nonempty_iff.mpr hg0
    obtain ⟨p,hp⟩ := s.nonempty
    have hmem : p ∈ (barycentricLinear g).support := by
      rw [barycentricLinear_support_eq g hg]
      exact Finset.mem_biUnion.mpr ⟨s,hs,hp⟩
    simp [he] at hmem
  · rintro rfl
    exact map_zero _

lemma flag_has_max (S : Finset (NonemptyFiniteChains P))
    (hc : IsChain (· ≤ ·) (S : Set (NonemptyFiniteChains P))) (hne : S.Nonempty) :
    ∃ s ∈ S, ∀ t ∈ S, t ≤ s := by
  obtain ⟨s,hs,hm⟩ := Finset.exists_max_image S (fun t => t.finset.card) hne
  refine ⟨s,hs,fun t ht => ?_⟩
  rcases hc.total ht hs with h | h
  · exact h
  · exact le_of_eq (NonemptyFiniteChains.ext (Finset.eq_of_subset_of_card_le h (hm t ht))).symm

lemma flag_union_eq_max (S : Finset (NonemptyFiniteChains P))
    (s : NonemptyFiniteChains P) (hs : s ∈ S) (hm : ∀ t ∈ S, t ≤ s) :
    S.biUnion NonemptyFiniteChains.finset = s.finset := by
  classical
  ext p
  constructor
  · rintro hp
    obtain ⟨t,ht,hpt⟩ := Finset.mem_biUnion.mp hp
    exact hm t ht hpt
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨s,hs,hp⟩

lemma flag_max_exclusive_vertex (S : Finset (NonemptyFiniteChains P))
    (hc : IsChain (· ≤ ·) (S : Set (NonemptyFiniteChains P)))
    (s : NonemptyFiniteChains P) (_ : s ∈ S) (hm : ∀ t ∈ S, t ≤ s) :
    ∃ p ∈ s.finset, ∀ t ∈ S, p ∈ t.finset → t = s := by
  classical
  by_cases hne : (S.erase s).Nonempty
  · obtain ⟨t,ht,htm⟩ := flag_has_max (S.erase s) (hc.mono (by simp)) hne
    have hts : t ≤ s := hm t (Finset.mem_of_mem_erase ht)
    have hst : ¬s.finset ⊆ t.finset := by
      intro h
      exact (Finset.mem_erase.mp ht).1 (le_antisymm hts h)
    obtain ⟨p,hps,hpt⟩ := Finset.not_subset.mp hst
    refine ⟨p,hps,fun a ha hpa => ?_⟩
    by_contra has
    exact hpt (htm a (Finset.mem_erase.mpr ⟨has,ha⟩) hpa)
  · obtain ⟨p,hp⟩ := s.nonempty
    refine ⟨p,hp,fun t ht hpt => ?_⟩
    by_contra hts
    exact hne ⟨t,Finset.mem_erase.mpr ⟨hts,ht⟩⟩

lemma barycentric_max_minimum (g : NonemptyFiniteChains P →₀ ℝ)
    (hn : ∀ s, 0 ≤ g s) (hc : IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains P)))
    (s : NonemptyFiniteChains P) (hs : s ∈ g.support) (hm : ∀ t ∈ g.support, t ≤ s) :
    (∀ p ∈ s.finset, g s * (s.finset.card : ℝ)⁻¹ ≤ barycentricLinear g p) ∧
    ∃ p ∈ s.finset, barycentricLinear g p = g s * (s.finset.card : ℝ)⁻¹ := by
  classical
  constructor
  · intro p hp
    rw [barycentricLinear_apply, Finsupp.sum]
    have hl := Finset.single_le_sum (f := fun t => g t * (barycenter t).weights p)
      (fun t ht => mul_nonneg (hn t) ((barycenter t).nonneg p)) hs
    simpa only [barycenter_apply, ite_eq_left hp] using hl
  · obtain ⟨p,hps,hex⟩ := flag_max_exclusive_vertex g.support hc s hs hm
    refine ⟨p,hps,?_⟩
    rw [barycentricLinear_apply, Finsupp.sum]
    calc
      ∑ t ∈ g.support, g t * (barycenter t).weights p =
          g s * (barycenter s).weights p := by
        apply Finset.sum_eq_single s
        · intro t ht hts
          have hpnot : p ∉ t.finset := fun h => hts (hex t ht h)
          simp [barycenter_apply, hpnot]
        · exact fun h => (h hs).elim
      _ = _ := by rw [barycenter_apply, ite_eq_left hps]

lemma barycentricLinear_injective_nonneg_flag
    (g h : NonemptyFiniteChains P →₀ ℝ)
    (hgn : ∀ s, 0 ≤ g s) (hhn : ∀ s, 0 ≤ h s)
    (hgc : IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains P)))
    (hhc : IsChain (· ≤ ·) (h.support : Set (NonemptyFiniteChains P)))
    (he : barycentricLinear g = barycentricLinear h) : g = h := by
  classical
  suffices ∀ (n : ℕ) (g h : NonemptyFiniteChains P →₀ ℝ), g.support.card = n →
      (∀ s, 0 ≤ g s) → (∀ s, 0 ≤ h s) →
      IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains P)) →
      IsChain (· ≤ ·) (h.support : Set (NonemptyFiniteChains P)) →
      barycentricLinear g = barycentricLinear h → g = h by
    exact this _ g h rfl hgn hhn hgc hhc he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro g h hcard hgn hhn hgc hhc he
    by_cases hg0 : g = 0
    · subst g
      have hh0 : h = 0 := (barycentricLinear_eq_zero_iff h hhn).mp (by simpa using he.symm)
      exact hh0.symm
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact hg0 ((barycentricLinear_eq_zero_iff g hgn).mp (by simpa using he))
    obtain ⟨s,hs,hsm⟩ := flag_has_max g.support hgc (Finsupp.support_nonempty_iff.mpr hg0)
    obtain ⟨t,ht,htm⟩ := flag_has_max h.support hhc (Finsupp.support_nonempty_iff.mpr hh0)
    have hst : s = t := by
      apply NonemptyFiniteChains.ext
      calc
        s.finset = (barycentricLinear g).support :=
          ((barycentricLinear_support_eq g hgn).trans (flag_union_eq_max _ s hs hsm)).symm
        _ = (barycentricLinear h).support := congrArg Finsupp.support he
        _ = t.finset := (barycentricLinear_support_eq h hhn).trans (flag_union_eq_max _ t ht htm)
    subst t
    obtain ⟨hgl,p,hp,hpe⟩ := barycentric_max_minimum g hgn hgc s hs hsm
    obtain ⟨hhl,q,hq,hqe⟩ := barycentric_max_minimum h hhn hhc s ht htm
    have hcoef : g s = h s := by
      have hp' := hhl p hp
      have hq' := hgl q hq
      rw [← he, hpe] at hp'
      rw [he, hqe] at hq'
      have hc : (s.finset.card : ℝ)⁻¹ > 0 :=
        inv_pos.mpr (by exact_mod_cast Finset.card_pos.mpr s.nonempty)
      exact (mul_right_cancel₀ hc.ne') (le_antisymm hq' hp')
    have herase : barycentricLinear (g.erase s) = barycentricLinear (h.erase s) := by
      have hg := congrArg barycentricLinear (Finsupp.erase_add_single s g)
      have hh := congrArg barycentricLinear (Finsupp.erase_add_single s h)
      rw [map_add] at hg hh
      rw [hcoef, he] at hg
      exact add_right_cancel (hg.trans hh.symm)
    have heraseeq : g.erase s = h.erase s := by
      apply ih (g.erase s).support.card
      · rw [Finsupp.support_erase, ← hcard]
        exact Finset.card_lt_card (Finset.erase_ssubset hs)
      · rfl
      · intro t
        rw [Finsupp.erase_apply]
        split_ifs
        · exact le_rfl
        · exact hgn t
      · intro t
        rw [Finsupp.erase_apply]
        split_ifs
        · exact le_rfl
        · exact hhn t
      · exact hgc.mono (by simp)
      · exact hhc.mono (by simp)
      · exact herase
    calc
      g = g.erase s + Finsupp.single s (g s) := (Finsupp.erase_add_single s g).symm
      _ = h.erase s + Finsupp.single s (h s) := by rw [heraseeq,hcoef]
      _ = h := Finsupp.erase_add_single s h

lemma subdivide_injective : Function.Injective (@subdivide P _) := by
  intro x y h
  apply PolyPoint.ext
  apply barycentricLinear_injective_nonneg_flag x.weights y.weights
    x.nonneg y.nonneg x.chain y.chain
  exact congrArg PolyPoint.weights h

end Thomason.GeometricRecognition.PolyPoint

end

noncomputable section
universe u v w z


namespace Thomason.GeometricRecognition
namespace PolyPoint
variable {P : Type u} [PartialOrder P]

instance finiteChainIndex [Finite P] : Finite (ChainIndex P) :=
  Finite.of_injective ChainIndex.carrier (by
    intro s t h
    cases s
    cases t
    cases h
    rfl)

lemma isCompact_chainFace (s : ChainIndex P) :
    IsCompact (Set.range (fun x : Face s.carrier => x.val)) := by
  classical
  have he : Set.range (fun x : Face s.carrier => x.val) = Set.range (eval s.vertices) := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨s.coordinates a, s.eval_coordinates a⟩
    · rintro ⟨a,rfl⟩
      refine ⟨⟨eval s.vertices a, ?_⟩,rfl⟩
      intro p hp
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (evalWeights_support s.vertices a hp)
      exact s.vertices_mem i
  rw [he]
  exact isCompact_range (continuous_eval s.vertices)

instance compactSpace [Finite P] : CompactSpace (PolyPoint P) := by
  classical
  have hc : IsCompact (⋃ s : ChainIndex P, Set.range (fun x : Face s.carrier => x.val)) :=
    isCompact_iUnion isCompact_chainFace
  have he : (⋃ s : ChainIndex P, Set.range (fun x : Face s.carrier => x.val)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨supportIndex x, ⟨⟨x,Finset.Subset.refl _⟩,rfl⟩⟩
  exact ⟨he ▸ hc⟩

instance finiteBoundedChainIndex (s : Finset P) :
    Finite {t : ChainIndex P // t.carrier ⊆ s} := by
  classical
  apply Finite.of_injective
    (fun t : {t : ChainIndex P // t.carrier ⊆ s} =>
      (⟨t.val.carrier,Finset.mem_powerset.mpr t.property⟩ : ↥s.powerset))
  intro a b h
  apply Subtype.ext
  have hc : a.val.carrier = b.val.carrier := congrArg Subtype.val h
  obtain ⟨⟨ca,ha,na⟩,pa⟩ := a
  obtain ⟨⟨cb,hb,nb⟩,pb⟩ := b
  cases hc
  rfl

lemma isCompact_carrier (s : Finset P) :
    IsCompact {x : PolyPoint P | x.weights.support ⊆ s} := by
  classical
  have hc : IsCompact (⋃ t : {t : ChainIndex P // t.carrier ⊆ s},
      Set.range (fun x : Face t.val.carrier => x.val)) :=
    isCompact_iUnion (fun t => isCompact_chainFace t.val)
  have he : (⋃ t : {t : ChainIndex P // t.carrier ⊆ s},
      Set.range (fun x : Face t.val.carrier => x.val)) =
        {x : PolyPoint P | x.weights.support ⊆ s} := by
    ext x
    constructor
    · intro hx
      obtain ⟨t,⟨a,rfl⟩⟩ := Set.mem_iUnion.mp hx
      exact a.property.trans t.property
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨supportIndex x,hx⟩,⟨⟨x,Finset.Subset.refl _⟩,rfl⟩⟩
  exact he ▸ hc

lemma continuous_face_val (s : Finset P) : Continuous (fun x : Face s => x.val) := by
  let : CompactSpace {x : PolyPoint P | x.weights.support ⊆ s} :=
    isCompact_iff_compactSpace.mp (isCompact_carrier s)
  have hc : Continuous (fun x : {x : PolyPoint P | x.weights.support ⊆ s} =>
      (fun p => x.val.weights p)) :=
    continuous_pi (fun p => (continuous_weights p).comp continuous_subtype_val)
  have he : Topology.IsEmbedding
      (fun x : {x : PolyPoint P | x.weights.support ⊆ s} => (fun p => x.val.weights p)) :=
    (hc.isClosedEmbedding (by
      intro x y h
      exact Subtype.ext (PolyPoint.ext (Finsupp.ext (congrFun h))))).isEmbedding
  have hf : Continuous (fun x : Face s =>
      (⟨x.val,x.property⟩ : {x : PolyPoint P | x.weights.support ⊆ s})) :=
    he.continuous_iff.mpr continuous_induced_dom
  exact continuous_subtype_val.comp hf

lemma continuous_of_finite_carrier {A : Type*} [TopologicalSpace A]
    (f : A → PolyPoint P) (s : Finset P) (h : ∀ a, (f a).weights.support ⊆ s)
    (hf : ∀ p, Continuous (fun a => (f a).weights p)) : Continuous f := by
  let g : A → Face s := fun a => ⟨f a,h a⟩
  have hg : Continuous g := continuous_induced_rng.mpr (continuous_pi hf)
  exact (continuous_face_val s).comp hg

end PolyPoint
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.PolyPoint
variable {P : Type u} [PartialOrder P]

local instance boundedFacesDecidableEq_rced991_1 : DecidableEq P := Classical.decEq P
instance finiteBoundedFaces (s : Finset P) :
    Finite {t : NonemptyFiniteChains P // t.finset ⊆ s} := by
  classical
  apply Finite.of_injective
    (fun t : {t : NonemptyFiniteChains P // t.finset ⊆ s} =>
      (⟨t.val.finset,Finset.mem_powerset.mpr t.property⟩ : ↥s.powerset))
  intro a b h
  exact Subtype.ext (NonemptyFiniteChains.ext (congrArg Subtype.val h))

def allFaces (s : Finset P) : Finset (NonemptyFiniteChains P) :=
  letI : Finite ↑{t : NonemptyFiniteChains P | t.finset ⊆ s} := finiteBoundedFaces s
  (Set.toFinite {t : NonemptyFiniteChains P | t.finset ⊆ s}).toFinset

@[simp] lemma mem_allFaces (s : Finset P) (t : NonemptyFiniteChains P) :
    t ∈ allFaces s ↔ t.finset ⊆ s := by simp [allFaces]

lemma subdivide_carrier_iff (x : PolyPoint (NonemptyFiniteChains P)) (s : Finset P) :
    (subdivide x).weights.support ⊆ s ↔ x.weights.support ⊆ allFaces s := by
  classical
  change (barycentricLinear x.weights).support ⊆ s ↔ _
  rw [barycentricLinear_support_eq x.weights x.nonneg]
  constructor
  · intro h t ht
    rw [mem_allFaces]
    exact fun p hp => h (Finset.mem_biUnion.mpr ⟨t,ht,hp⟩)
  · intro h p hp
    obtain ⟨t,ht,hpt⟩ := Finset.mem_biUnion.mp hp
    exact (mem_allFaces s t).mp (h ht) hpt

lemma isClosedMap_subdivide : IsClosedMap (@subdivide P _) := by
  classical
  intro A hA
  rw [isClosed_iff_faces]
  intro s
  let K : Set (PolyPoint (NonemptyFiniteChains P)) :=
    {x | x.weights.support ⊆ allFaces s.carrier}
  have hK : IsCompact K := isCompact_carrier _
  have hAK : IsCompact (A ∩ K) := hK.inter_left hA
  have he : (fun y : Face s.carrier => y.val) ⁻¹' (subdivide '' A) =
      (fun y : Face s.carrier => y.val) ⁻¹' (subdivide '' (A ∩ K)) := by
    ext y
    constructor
    · rintro ⟨x,hx,hxy⟩
      refine ⟨x,⟨hx,?_⟩,hxy⟩
      exact (subdivide_carrier_iff x s.carrier).mp
        (by rw [hxy]; exact y.property)
    · rintro ⟨x,⟨hx,hKx⟩,hxy⟩
      exact ⟨x,hx,hxy⟩
  rw [he]
  exact (hAK.image continuous_subdivide).isClosed.preimage (continuous_chainFace_val s)

def subdivisionHomeomorph : PolyPoint (NonemptyFiniteChains P) ≃ₜ PolyPoint P :=
  (Equiv.ofBijective subdivide ⟨subdivide_injective,subdivide_surjective⟩).toHomeomorphOfContinuousClosed
    continuous_subdivide isClosedMap_subdivide
end Thomason.GeometricRecognition.PolyPoint

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Mesh
variable {P : Type u} [PartialOrder P]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

instance finiteChains [Finite P] : Finite (NonemptyFiniteChains P) :=
  Finite.of_injective NonemptyFiniteChains.finset
    (fun _ _ h => NonemptyFiniteChains.ext h)

@[reducible] def level (P : PartOrd.{u}) : ℕ → PartOrd.{u}
  | 0 => P
  | n + 1 => PartOrd.of (NonemptyFiniteChains (level P n))

end Mesh
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Globes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globes. -/

noncomputable section
universe u v w z


namespace Thomason.SmallObject

open CategoryTheory Limits Opposite

lemma commonPresentabilityCardinal {C : Type v} [Category.{u} C]
    {ι : Type u} (X : ι → C) [∀ i, IsPresentable.{u} (X i)] :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular), ∀ i, IsCardinalPresentable (X i) κ := by
  classical
  choose κ hκ hp using fun i =>
    CategoryTheory.Functor.IsAccessible.exists_cardinal (F := coyoneda.obj (Opposite.op (X i)))
  obtain ⟨k, hk, hb⟩ := HasCardinalLT.exists_regular_cardinal_forall.{u}
    (fun i => (κ i).out)
  let : Fact k.IsRegular := ⟨hk⟩
  refine ⟨k, inferInstance, fun i => ?_⟩
  let := hκ i
  let := hp i
  have hi : κ i < k := by
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_out] using hb i
  exact isCardinalPresentable_of_le (X i) hi.le

lemma smallObjectArgument {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C]
    (I : MorphismProperty C) [MorphismProperty.IsSmall.{u} I] :
    MorphismProperty.HasSmallObjectArgument.{u} I := by
  obtain ⟨ι, A, B, f, rfl⟩ := (MorphismProperty.isSmall_iff_eq_ofHoms.{u} I).mp inferInstance
  obtain ⟨κ, hκ, hp⟩ := commonPresentabilityCardinal A
  let := hκ
  have : Nonempty κ.ord.ToType := by simpa using Cardinal.IsRegular.ne_zero hκ.out
  let := WellFoundedLT.toOrderBot κ.ord.ToType
  let : MorphismProperty.IsCardinalForSmallObjectArgument (MorphismProperty.ofHoms f) κ := {
    preservesColimit := by
      intro X Y Z W i hi p hf
      obtain ⟨j⟩ := hi
      let := hp j
      have := preservesColimitsOfShape_of_isCardinalPresentable (A j) κ κ.ord.ToType
      infer_instance }
  exact ⟨κ, inferInstance, inferInstance, inferInstance⟩

lemma weakFactorizationSystem {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C]
    (I : MorphismProperty C) [MorphismProperty.IsSmall.{u} I] :
    MorphismProperty.IsWeakFactorizationSystem I.rlp.llp I.rlp := by
  let := smallObjectArgument I
  exact { rlp := MorphismProperty.rlp_llp_rlp I, llp := rfl }

end Thomason.SmallObject

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits

instance hornImages_small {C : Type v} [Category.{u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.IsSmall.{u} (hornImages L) := by
  unfold hornImages
  let : ∀ n : ℕ, MorphismProperty.IsSmall.{u}
      (MorphismProperty.ofHoms (fun i : Fin (n+2) => L.map (SSet.horn (n+1) i).ι)) :=
    fun _ => MorphismProperty.isSmall_ofHoms _
  exact MorphismProperty.isSmall_iSup _

lemma hornImages_rlp {C : Type v} [Category.{u} C] {L : SSet.{u} ⥤ C}
    {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    (hornImages L).rlp = simplicialFibrations.inverseImage R := by
  ext X Y f
  constructor
  · intro h A B i hi
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    apply (adj.hasLiftingProperty_iff _ f).mp
    apply h
    simp only [hornImages, MorphismProperty.iSup_iff]
    exact ⟨n, ⟨j⟩⟩
  · intro h A B i hi
    simp only [hornImages, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    apply (adj.hasLiftingProperty_iff _ f).mpr
    apply h
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff]
    exact ⟨n, ⟨j⟩⟩

lemma hornImages_weakFactorization {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.IsWeakFactorizationSystem (hornImages L).rlp.llp
      (hornImages L).rlp := SmallObject.weakFactorizationSystem _

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionMaps
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Maps. -/

noncomputable section
universe u v w z


namespace Thomason.SimplicialCylinder

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory Limits

noncomputable def hornOneIso (i j : Fin 2) (h : j ≠ i) :
    (Δ[0] : SSet.{u}) ≅ SSet.horn 1 i where
  hom := SSet.horn.ι i j h
  inv := SSet.stdSimplex.isTerminalObj₀.from _
  hom_inv_id := SSet.stdSimplex.ext₀
  inv_hom_id := by
    apply SSet.horn.hom_ext'
    intro k hk
    have he : k = j := by fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    subst k
    rw [← Category.assoc, SSet.stdSimplex.ext₀ (f := SSet.horn.ι i j h ≫
      SSet.stdSimplex.isTerminalObj₀.from _) (g := 𝟙 _)]
    simp

lemma delta_one_anodyne (j : Fin 2) :
    SSet.anodyneExtensions.{u} (SSet.stdSimplex.δ (n := 0) j) := by
  let i : Fin 2 := j.rev
  have h : j ≠ i := by fin_cases j <;> decide
  have hh := SSet.anodyneExtensions.comp_mem (hornOneIso i j h).hom (SSet.horn 1 i).ι
    (SSet.anodyneExtensions.of_isIso _) (SSet.anodyneExtensions.horn_ι i)
  simpa only [hornOneIso, SSet.horn.ι_ι] using hh

noncomputable def zeroFactorIso (X : SSet.{u}) : X ≅ X ⊗ Δ[0] where
  hom := lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _)
  inv := fst _ _
  hom_inv_id := by simp
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · exact SSet.stdSimplex.ext₀

lemma endpoint_anodyne (X : SSet.{u}) :
    SSet.anodyneExtensions (SSet.ι₀ (X := X)) ∧
    SSet.anodyneExtensions (SSet.ι₁ (X := X)) := by
  have h (j : Fin 2) := SSet.anodyneExtensions.comp_mem (zeroFactorIso X).hom
    (X ◁ SSet.stdSimplex.δ (n := 0) j) (SSet.anodyneExtensions.of_isIso _)
    ((delta_one_anodyne j).whiskerLeft X)
  have h0 : (zeroFactorIso X).hom ≫ X ◁ SSet.stdSimplex.δ (n := 0) 1 = SSet.ι₀ := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro z
      rfl
  have h1 : (zeroFactorIso X).hom ≫ X ◁ SSet.stdSimplex.δ (n := 0) 0 = SSet.ι₁ := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro z
      rfl
  exact ⟨h0 ▸ h 1,h1 ▸ h 0⟩

end Thomason.SimplicialCylinder

end

noncomputable section
universe u v w z


namespace Thomason.SimplicialCylinder

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory Limits

def Ends (X : SSet.{u}) : SSet.{u} where
  obj k := X.obj k ⊕ X.obj k
  map f := ↾(Sum.map (X.map f) (X.map f))
  map_id k := by ext x; cases x <;> simp
  map_comp f g := by ext x; cases x <;> simp

def endsMap {X Y : SSet.{u}} (f g : X ⟶ Y) : Ends X ⟶ Y where
  app k := ↾(Sum.elim (f.app k) (g.app k))
  naturality k l a := by
    ext x
    cases x with
    | inl x => exact NatTrans.naturality_apply f a x
    | inr x => exact NatTrans.naturality_apply g a x

noncomputable def endsInclusion (X : SSet.{u}) : Ends X ⟶ X ⊗ Δ[1] :=
  endsMap SSet.ι₀ SSet.ι₁

instance endsInclusion_mono (X : SSet.{u}) : Mono (endsInclusion X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (congrArg Prod.fst hab)
    | inr b =>
      have h := congrArg (fun z : (X ⊗ Δ[1]).obj k => SSet.stdSimplex.asOrderHom z.2 0) hab
      exact (zero_ne_one h).elim
  | inr a =>
    cases b with
    | inl b =>
      have h := congrArg (fun z : (X ⊗ Δ[1]).obj k => SSet.stdSimplex.asOrderHom z.2 0) hab
      exact (one_ne_zero h).elim
    | inr b => exact congrArg Sum.inr (congrArg Prod.fst hab)

end Thomason.SimplicialCylinder

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory PartialOrder

variable {X : Type u} {Y : Type v} [PartialOrder X] [PartialOrder Y]

lemma chain_has_greatest (s : NonemptyFiniteChains X) :
    ∃ x, x ∈ s.finset ∧ ∀ y ∈ s.finset, y ≤ x := by
  obtain ⟨x, hx, hm⟩ := s.finset.exists_maximal s.nonempty
  refine ⟨x, hx, fun y hy => ?_⟩
  rcases s.comparable ⟨x, hx⟩ ⟨y, hy⟩ with h | h
  · exact hm hy h
  · exact h

noncomputable def chainGreatest (s : NonemptyFiniteChains X) : X :=
  (chain_has_greatest s).choose

lemma chainGreatest_mem (s : NonemptyFiniteChains X) : chainGreatest s ∈ s.finset :=
  (chain_has_greatest s).choose_spec.1

lemma le_chainGreatest (s : NonemptyFiniteChains X) {x : X} (hx : x ∈ s.finset) :
    x ≤ chainGreatest s := (chain_has_greatest s).choose_spec.2 x hx

noncomputable def chainLast : NonemptyFiniteChains X →o X where
  toFun := chainGreatest
  monotone' s t h := le_chainGreatest t (h (chainGreatest_mem s))

lemma chainGreatest_map (s : NonemptyFiniteChains X) (f : X →o Y) :
    chainGreatest (s.map f) = f (chainGreatest s) := by
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := (NonemptyFiniteChains.mem_map_iff s f _).mp
      (chainGreatest_mem (s.map f))
    rw [← he]
    exact f.monotone (le_chainGreatest s hx)
  · exact le_chainGreatest (s.map f)
      ((NonemptyFiniteChains.mem_map_iff s f _).mpr ⟨_, chainGreatest_mem s, rfl⟩)

noncomputable def chainLastNat : PartOrd.nonemptyFiniteChainsFunctor.{u} ⟶ 𝟭 PartOrd where
  app X := PartOrd.ofHom chainLast
  naturality X Y f := by
    apply PartOrd.hom_ext
    apply OrderHom.ext
    funext s
    exact chainGreatest_map s f.hom

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

noncomputable def simplexNerveIso : SSet.stdSimplex.{u} ≅
    SimplexCategory.toPartOrd ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents (fun n => SSet.stdSimplex.isoNerve n.len) (by
    intro n m f
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    apply ComposableArrows.ext (fun _ => rfl)
    intros
    apply Subsingleton.elim)

noncomputable def simplexLastVertex : SimplexCategory.sd.{u} ⟶ SSet.stdSimplex :=
  Functor.whiskerLeft SimplexCategory.toPartOrd (Functor.whiskerRight chainLastNat PartOrd.nerveFunctor) ≫
    simplexNerveIso.inv

noncomputable def lastVertex : SSet.sd.{u} ⟶ 𝟭 SSet :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv (𝟭 SSet) simplexLastVertex

lemma lastVertex_stdSimplex (n : SimplexCategory) :
    lastVertex.app (SSet.stdSimplex.obj n) =
      (SSet.stdSimplex.sdIso.app n).hom ≫ simplexLastVertex.app n := by
  apply (cancel_epi (SSet.stdSimplex.sdIso.app n).inv).mp
  simpa only [lastVertex, Iso.app_inv, Iso.app_hom, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
    SSet.sd.descOfIsLeftKanExtension_fac_app SSet.stdSimplex.sdIso.inv
      (𝟭 SSet) simplexLastVertex n

noncomputable def exComparison : 𝟭 SSet.{u} ⟶ SSet.ex where
  app X := SSet.sdExAdjunction.homEquiv X X (lastVertex.app X)
  naturality X Y f := by
    change f ≫ SSet.sdExAdjunction.homEquiv Y Y (lastVertex.app Y) =
      SSet.sdExAdjunction.homEquiv X X (lastVertex.app X) ≫ SSet.ex.map f
    rw [← SSet.sdExAdjunction.homEquiv_naturality_left,
      ← SSet.sdExAdjunction.homEquiv_naturality_right]
    exact congrArg (SSet.sdExAdjunction.homEquiv X Y) (lastVertex.naturality f)

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionNerves
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Nerves. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

noncomputable def initialFlag (n : SimplexCategory) :
    SimplexCategory.toPartOrd.obj n →o
      NonemptyFiniteChains (SimplexCategory.toPartOrd.obj n) := by
  classical
  letI : Fintype (SimplexCategory.toPartOrd.obj n) :=
    inferInstanceAs (Fintype (ULift (Fin (n.len+1))))
  letI : LinearOrder (SimplexCategory.toPartOrd.obj n) :=
    inferInstanceAs (LinearOrder (ULift (Fin (n.len+1))))
  exact {
    toFun := fun i => {
      finset := Finset.univ.filter (· ≤ i)
      nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩⟩
      comparable := fun a b => le_total a.val b.val }
    monotone' := fun i j h k hk => by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans (Finset.mem_filter.mp hk).2 h⟩ }

lemma chainLast_initialFlag (n : SimplexCategory) (i : SimplexCategory.toPartOrd.obj n) :
    chainLast (initialFlag n i) = i := by
  classical
  let _ : Fintype (SimplexCategory.toPartOrd.obj n) :=
    inferInstanceAs (Fintype (ULift (Fin (n.len+1))))
  let _ : LinearOrder (SimplexCategory.toPartOrd.obj n) :=
    inferInstanceAs (LinearOrder (ULift (Fin (n.len+1))))
  apply le_antisymm
  · have h := chainGreatest_mem (initialFlag n i)
    exact (Finset.mem_filter.mp h).2
  · exact le_chainGreatest (initialFlag n i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩)

noncomputable def simplexLastVertexSection (n : SimplexCategory) :
    SSet.stdSimplex.obj n ⟶ SimplexCategory.sd.obj n :=
  simplexNerveIso.hom.app n ≫ PartOrd.nerveFunctor.map (PartOrd.ofHom (initialFlag n))

lemma simplexLastVertexSection_comp (n : SimplexCategory) :
    simplexLastVertexSection n ≫ simplexLastVertex.app n = 𝟙 _ := by
  have h : PartOrd.ofHom (initialFlag n) ≫ chainLastNat.app (SimplexCategory.toPartOrd.obj n) =
      𝟙 _ := by
    apply PartOrd.hom_ext
    apply OrderHom.ext
    funext i
    exact chainLast_initialFlag n i
  change (simplexNerveIso.hom.app n ≫ PartOrd.nerveFunctor.map _) ≫
    (PartOrd.nerveFunctor.map _ ≫ simplexNerveIso.inv.app n) = _
  have hh := congrArg PartOrd.nerveFunctor.map h
  have hh' : PartOrd.nerveFunctor.map (PartOrd.ofHom (initialFlag n)) ≫
      PartOrd.nerveFunctor.map (chainLastNat.app (SimplexCategory.toPartOrd.obj n)) = 𝟙 _ := by
    exact (PartOrd.nerveFunctor.map_comp _ _).symm.trans
      (hh.trans (PartOrd.nerveFunctor.map_id _))
  calc
    _ = simplexNerveIso.hom.app n ≫
        (PartOrd.nerveFunctor.map (PartOrd.ofHom (initialFlag n)) ≫
        PartOrd.nerveFunctor.map (chainLastNat.app (SimplexCategory.toPartOrd.obj n))) ≫
        simplexNerveIso.inv.app n := by simp only [Category.assoc]; rfl
    _ = _ := by erw [hh', Category.id_comp]; exact simplexNerveIso.hom_inv_id_app n

noncomputable def lastVertexSection (n : SimplexCategory) :
    SSet.stdSimplex.obj n ⟶ SSet.sd.obj (SSet.stdSimplex.obj n) :=
  simplexLastVertexSection n ≫ (SSet.stdSimplex.sdIso.app n).inv

lemma lastVertexSection_comp (n : SimplexCategory) :
    lastVertexSection n ≫ lastVertex.app (SSet.stdSimplex.obj n) = 𝟙 _ := by
  rw [lastVertexSection, lastVertex_stdSimplex, Category.assoc,
    ← Category.assoc (SSet.stdSimplex.sdIso.app n).inv,
    Iso.inv_hom_id, Category.id_comp, simplexLastVertexSection_comp]

instance exComparison_mono (X : SSet.{u}) : Mono (exComparison.app X) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro k
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  let f : SSet.stdSimplex.obj k.unop ⟶ X := SSet.yonedaEquiv.symm a
  let g : SSet.stdSimplex.obj k.unop ⟶ X := SSet.yonedaEquiv.symm b
  have he : f ≫ exComparison.app X = g ≫ exComparison.app X := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, f, g, Equiv.apply_symm_apply] using hab
  have hm : lastVertex.app (SSet.stdSimplex.obj k.unop) ≫ f =
      lastVertex.app (SSet.stdSimplex.obj k.unop) ≫ g := by
    apply (SSet.sdExAdjunction.homEquiv _ X).injective
    rw [SSet.sdExAdjunction.homEquiv_naturality_right,
      SSet.sdExAdjunction.homEquiv_naturality_right]
    change exComparison.app (SSet.stdSimplex.obj k.unop) ≫ SSet.ex.map f =
      exComparison.app (SSet.stdSimplex.obj k.unop) ≫ SSet.ex.map g
    rw [← exComparison.naturality f, ← exComparison.naturality g]
    exact he
  have hfg : f = g := by
    have h := congrArg (fun t => lastVertexSection k.unop ≫ t) hm
    simpa only [← Category.assoc, lastVertexSection_comp, Category.id_comp] using h
  simpa only [f, g, Equiv.apply_symm_apply] using congrArg SSet.yonedaEquiv hfg

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

variable {E : Type u} [PartialOrder E]

noncomputable def simplexChain {n : ℕ} (s : (nerve E) _⦋n⦌) :
    NonemptyFiniteChains E := by
  classical
  exact {
    finset := Finset.univ.image s.obj
    nonempty := ⟨s.obj 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
    comparable := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      rcases le_total i j with h | h
      · exact Or.inl (s.monotone h)
      · exact Or.inr (s.monotone h) }

lemma mem_simplexChain {n : ℕ} (s : (nerve E) _⦋n⦌) (x : E) :
    x ∈ (simplexChain s).finset ↔ ∃ i, s.obj i = x := by
  classical
  simp [simplexChain]

lemma simplexChain_le_iff (s t : (nerve E).N) :
    simplexChain s.simplex ≤ simplexChain t.simplex ↔ s ≤ t := by
  constructor
  · intro h
    have ht := (mem_nerve_nonDegenerate_iff_strictMono t.simplex).mp t.nonDegenerate
    have hs := (mem_nerve_nonDegenerate_iff_strictMono s.simplex).mp s.nonDegenerate
    have hex (i : Fin (s.dim+1)) : ∃ j, t.simplex.obj j = s.simplex.obj i :=
      (mem_simplexChain _ _).mp (h ((mem_simplexChain _ _).mpr ⟨i, rfl⟩))
    let f : Fin (s.dim+1) →o Fin (t.dim+1) := {
      toFun i := (hex i).choose
      monotone' := by
        intro i j hij
        apply ht.le_iff_le.mp
        rw [(hex i).choose_spec, (hex j).choose_spec]
        exact hs.monotone hij }
    let φ : ⦋s.dim⦌ ⟶ ⦋t.dim⦌ := SimplexCategory.mkHom f
    have hm : Mono φ := by
      apply SimplexCategory.mono_iff_injective.mpr
      intro i j hij
      apply hs.injective
      exact ((hex i).choose_spec).symm.trans
        ((congrArg t.simplex.obj hij).trans (hex j).choose_spec)
    apply SSet.N.le_iff_exists_mono.mpr
    refine ⟨φ, hm, ?_⟩
    apply nerve.ext_of_isThin
    funext i
    exact (hex i).choose_spec
  · intro h x hx
    obtain ⟨φ, _, he⟩ := SSet.N.le_iff_exists_mono.mp h
    obtain ⟨i, rfl⟩ := (mem_simplexChain _ _).mp hx
    apply (mem_simplexChain _ _).mpr
    refine ⟨φ i, ?_⟩
    exact congrArg (fun q => q.obj i) he

noncomputable def chainSimplex (s : NonemptyFiniteChains E) : (nerve E).N := by
  classical
  let _ : LinearOrder s.finset := Relation.linearOrderOfSymmGen s.comparable
  let n := s.finset.card - 1
  have hc : Fintype.card s.finset = n+1 := by
    rw [Fintype.card_coe]
    dsimp [n]
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr s.nonempty)).symm
  let e : Fin (n+1) ≃o s.finset := Fintype.orderIsoFinOfCardEq s.finset hc
  let f : Fin (n+1) →o E := {
    toFun i := (e i).val
    monotone' := fun _ _ h => e.monotone h }
  exact SSet.N.mk f.monotone.functor
    ((mem_nerve_nonDegenerate_iff_strictMono _).mpr
      (fun _ _ h => e.strictMono h))

lemma simplexChain_chainSimplex (s : NonemptyFiniteChains E) :
    simplexChain (chainSimplex s).simplex = s := by
  classical
  let _ : LinearOrder s.finset := Relation.linearOrderOfSymmGen s.comparable
  apply NonemptyFiniteChains.ext
  ext x
  rw [mem_simplexChain]
  dsimp [chainSimplex]
  constructor
  · rintro ⟨i, rfl⟩
    exact (Fintype.orderIsoFinOfCardEq s.finset _ i).property
  · intro hx
    exact ⟨(Fintype.orderIsoFinOfCardEq s.finset _).symm ⟨x, hx⟩,
      congrArg Subtype.val ((Fintype.orderIsoFinOfCardEq s.finset _).apply_symm_apply _)⟩

noncomputable def nerveNondegenerateChains : (nerve E).N ≃o NonemptyFiniteChains E where
  toFun s := simplexChain s.simplex
  invFun := chainSimplex
  left_inv s := by
    apply le_antisymm
    · apply (simplexChain_le_iff _ _).mp
      rw [simplexChain_chainSimplex]
    · apply (simplexChain_le_iff _ _).mp
      rw [simplexChain_chainSimplex]
  right_inv := simplexChain_chainSimplex
  map_rel_iff' := simplexChain_le_iff _ _

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E]

lemma chains_map_injective {A : Type v} [PartialOrder A] (f : A →o E)
    (hf : Function.Injective f) : Function.Injective (NonemptyFiniteChains.orderHomMap f) := by
  classical
  intro s t h
  apply NonemptyFiniteChains.ext
  exact Finset.image_injective hf (congrArg NonemptyFiniteChains.finset h)

lemma chains_map_le_iff {A : Type v} [PartialOrder A] (f : A →o E)
    (hf : Function.Injective f) (s t : NonemptyFiniteChains A) :
    s.map f ≤ t.map f ↔ s ≤ t := by
  constructor
  · intro h a ha
    obtain ⟨b, hb, he⟩ := (NonemptyFiniteChains.mem_map_iff t f _).mp
      (h ((NonemptyFiniteChains.mem_map_iff s f _).mpr ⟨a, ha, rfl⟩))
    exact hf he ▸ hb
  · intro h; exact (NonemptyFiniteChains.orderHomMap f).monotone h

lemma chains_map_surjective_on {A : Type v} [PartialOrder A] (f : A ↪o E)
    (s : NonemptyFiniteChains E) (hs : ∀ x ∈ s.finset, ∃ a, f a = x) :
    ∃ t : NonemptyFiniteChains A, t.map f.toOrderHom = s := by
  classical
  let g (x : s.finset) : A := (hs x.val x.property).choose
  have hg (x : s.finset) : f (g x) = x := (hs x.val x.property).choose_spec
  let t : NonemptyFiniteChains A := {
    finset := s.finset.attach.image g
    nonempty := by
      obtain ⟨x, hx⟩ := s.nonempty
      exact ⟨g ⟨x,hx⟩, Finset.mem_image.mpr ⟨⟨x,hx⟩, Finset.mem_attach _ _, rfl⟩⟩
    comparable := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
      rcases s.comparable x y with h | h
      · left; apply f.le_iff_le.mp; simpa only [hg] using (show x.val ≤ y.val from h)
      · right; apply f.le_iff_le.mp; simpa only [hg] using (show y.val ≤ x.val from h) }
  refine ⟨t, NonemptyFiniteChains.ext ?_⟩
  ext x
  rw [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp ha
    simpa only [OrderEmbedding.toOrderHom_coe, hg] using y.property
  · intro hx
    refine ⟨g ⟨x,hx⟩, Finset.mem_image.mpr ⟨⟨x,hx⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    exact hg ⟨x,hx⟩

def simplexVertices {n : ℕ} (s : (nerve E) _⦋n⦌) :
    SimplexCategory.toPartOrd.obj ⦋n⦌ →o E where
  toFun i := s.obj i.down
  monotone' _ _ h := s.monotone h

lemma simplexVertices_injective (s : (nerve E).N) :
    Function.Injective (simplexVertices s.simplex) := by
  intro i j h
  apply ULift.ext
  exact ((mem_nerve_nonDegenerate_iff_injective _).mp s.nonDegenerate) h

noncomputable def simplexVerticesEmbedding (s : (nerve E).N) :
    SimplexCategory.toPartOrd.obj ⦋s.dim⦌ ↪o E where
  toFun := simplexVertices s.simplex
  inj' := simplexVertices_injective s
  map_rel_iff' := by
    intro i j
    exact ((mem_nerve_nonDegenerate_iff_strictMono _).mp s.nonDegenerate).le_iff_le

noncomputable def sdNerveLeg (s : (nerve E).N) :
    SimplexCategory.sd.obj ⦋s.dim⦌ ⟶ nerve (NonemptyFiniteChains E) :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom
    (NonemptyFiniteChains.orderHomMap (simplexVertices s.simplex)))

lemma sdNerveLeg_naturality {s t : (nerve E).N} (h : s ≤ t) :
    SimplexCategory.sd.map (SSet.N.monoOfLE h) ≫ sdNerveLeg t = sdNerveLeg s := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  funext j
  apply NonemptyFiniteChains.ext
  classical
  change Finset.image _ (Finset.image _ _) = Finset.image _ _
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i hi
  exact congrArg (fun q => q.obj i.down) (SSet.N.map_monoOfLE h)

noncomputable def sdNerveCocone :
    Cocone ((nerve E).functorN' ⋙ SSet.sd) where
  pt := nerve (NonemptyFiniteChains E)
  ι.app s := (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom ≫ sdNerveLeg s
  ι.naturality s t f := by
    change SSet.sd.map (SSet.stdSimplex.map (SSet.N.monoOfLE (leOfHom f))) ≫
      ((SSet.stdSimplex.sdIso.app _).hom ≫ sdNerveLeg t) = _
    simp only [Functor.const_obj_map]
    erw [← Category.assoc, SSet.stdSimplex.sdIso.hom.naturality,
      Category.assoc, sdNerveLeg_naturality]
    exact (Category.comp_id _).symm

noncomputable def sdNerveMap :
    SSet.sd.obj (nerve E) ⟶ nerve (NonemptyFiniteChains E) :=
  (isColimitOfPreserves SSet.sd (nerve E).isColimitCoconeN').desc sdNerveCocone

lemma sdNerveMap_fac (s : (nerve E).N) :
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ sdNerveMap =
      (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom ≫ sdNerveLeg s :=
  (isColimitOfPreserves SSet.sd (nerve E).isColimitCoconeN').fac sdNerveCocone s

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E]

noncomputable def sdNerveInjection (s : (nerve E).N) :
    SimplexCategory.sd.obj ⦋s.dim⦌ ⟶ SSet.sd.obj (nerve E) :=
  (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv ≫
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex)

lemma sdNerveInjection_comp (s : (nerve E).N) :
    sdNerveInjection s ≫ sdNerveMap = sdNerveLeg s := by
  rw [sdNerveInjection, Category.assoc, sdNerveMap_fac,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma sdNerveInjection_naturality {s t : (nerve E).N} (h : s ≤ t) :
    SimplexCategory.sd.map (SSet.N.monoOfLE h) ≫ sdNerveInjection t =
      sdNerveInjection s := by
  unfold sdNerveInjection
  erw [← Category.assoc, SSet.stdSimplex.sdIso.inv.naturality,
    Category.assoc, ← SSet.sd.map_comp,
    SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex]
  rfl

lemma sdNerveInjection_jointly_surjective (k : SimplexCategoryᵒᵖ)
    (z : (SSet.sd.obj (nerve E)).obj k) :
    ∃ (s : (nerve E).N) (x : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k),
      (sdNerveInjection s).app k x = z := by
  have hc := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj k)
    (isColimitOfPreserves SSet.sd (nerve E).isColimitCoconeN')
  obtain ⟨s, x, hx⟩ := Types.jointly_surjective_of_isColimit hc z
  refine ⟨s, (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x, ?_⟩
  change (SSet.sd.map (SSet.yonedaEquiv.symm s.simplex)).app k
    ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv.app k
      ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x)) = z
  have he := congrArg (fun f => f.app k x) (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom_inv_id
  change (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv.app k
      ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x) = x at he
  rw [he]
  exact hx

lemma sdNerveLeg_app_injective (s : (nerve E).N) (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((sdNerveLeg s).app k) := by
  intro x y h
  apply nerve.ext_of_isThin
  funext i
  exact chains_map_injective _ (simplexVertices_injective s)
    (congrArg (fun q => q.obj i) h)

lemma sdNerveLeg_obj_le (s : (nerve E).N) (k : SimplexCategoryᵒᵖ)
    (x : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k) (j : Fin (k.unop.len+1)) :
    ((sdNerveLeg s).app k x).obj j ≤ simplexChain s.simplex := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp ha
  exact (mem_simplexChain _ _).mpr ⟨i.down, rfl⟩

lemma sdNerveLeg_surjective_on (s : (nerve E).N) (k : SimplexCategoryᵒᵖ)
    (q : (nerve (NonemptyFiniteChains E)).obj k)
    (h : ∀ i, q.obj i ≤ simplexChain s.simplex) :
    ∃ p : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k, (sdNerveLeg s).app k p = q := by
  have hex (i : Fin (k.unop.len+1)) :
      ∃ p : NonemptyFiniteChains (SimplexCategory.toPartOrd.obj ⦋s.dim⦌),
        p.map (simplexVertices s.simplex) = q.obj i := by
    apply chains_map_surjective_on (simplexVerticesEmbedding s)
    intro x hx
    obtain ⟨j, hj⟩ := (mem_simplexChain _ _).mp (h i hx)
    exact ⟨ULift.up j, hj⟩
  let f : Fin (k.unop.len+1) →o
      NonemptyFiniteChains (SimplexCategory.toPartOrd.obj ⦋s.dim⦌) := {
    toFun i := (hex i).choose
    monotone' := by
      intro i j hij
      apply (chains_map_le_iff (simplexVertices s.simplex) (simplexVertices_injective s) _ _).mp
      rw [(hex i).choose_spec, (hex j).choose_spec]
      exact q.monotone hij }
  refine ⟨f.monotone.functor, ?_⟩
  apply nerve.ext_of_isThin
  funext i
  exact (hex i).choose_spec

lemma sdNerveMap_app_surjective (k : SimplexCategoryᵒᵖ) :
    Function.Surjective ((sdNerveMap (E := E)).app k) := by
  intro q
  let s := chainSimplex (q.obj (Fin.last k.unop.len))
  have h (i) : q.obj i ≤ simplexChain s.simplex := by
    rw [simplexChain_chainSimplex]
    exact q.monotone (Fin.le_last i)
  obtain ⟨p, hp⟩ := sdNerveLeg_surjective_on s k q h
  refine ⟨(sdNerveInjection s).app k p, ?_⟩
  exact (congrArg (fun f => f.app k p) (sdNerveInjection_comp s)).trans hp

lemma sdNerveMap_app_injective (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((sdNerveMap (E := E)).app k) := by
  intro x y hxy
  obtain ⟨s, p, rfl⟩ := sdNerveInjection_jointly_surjective k x
  obtain ⟨t, q, rfl⟩ := sdNerveInjection_jointly_surjective k y
  have hs := congrArg (fun f => f.app k p) (sdNerveInjection_comp s)
  have ht := congrArg (fun f => f.app k q) (sdNerveInjection_comp t)
  have he : (sdNerveLeg s).app k p = (sdNerveLeg t).app k q := hs.symm.trans (hxy.trans ht)
  let v := (sdNerveLeg s).app k p
  let a := chainSimplex (v.obj (Fin.last k.unop.len))
  have has : a ≤ s := by
    apply (simplexChain_le_iff _ _).mp
    rw [simplexChain_chainSimplex]
    exact sdNerveLeg_obj_le s k p _
  have hat : a ≤ t := by
    apply (simplexChain_le_iff _ _).mp
    rw [simplexChain_chainSimplex]
    dsimp only [v]
    rw [he]
    exact sdNerveLeg_obj_le t k q _
  obtain ⟨r, hr⟩ := sdNerveLeg_surjective_on a k v (fun i => by
    rw [simplexChain_chainSimplex]
    exact v.monotone (Fin.le_last i))
  have hps : (SimplexCategory.sd.map (SSet.N.monoOfLE has)).app k r = p := by
    apply sdNerveLeg_app_injective s k
    exact (congrArg (fun f => f.app k r) (sdNerveLeg_naturality has)).trans hr
  have hqt : (SimplexCategory.sd.map (SSet.N.monoOfLE hat)).app k r = q := by
    apply sdNerveLeg_app_injective t k
    exact (congrArg (fun f => f.app k r) (sdNerveLeg_naturality hat)).trans (hr.trans he)
  rw [← hps, ← hqt]
  exact (congrArg (fun f => f.app k r) (sdNerveInjection_naturality has)).trans
    (congrArg (fun f => f.app k r) (sdNerveInjection_naturality hat)).symm

instance sdNerveMap_isIso : IsIso (sdNerveMap (E := E)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro k
  exact (CategoryTheory.isIso_iff_bijective _).mpr
    ⟨sdNerveMap_app_injective k, sdNerveMap_app_surjective k⟩

noncomputable def sdNerveIso : SSet.sd.obj (nerve E) ≅ nerve (NonemptyFiniteChains E) :=
  asIso sdNerveMap

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)

def subcomplexN (s : (K : SSet).N) : (nerve E).N :=
  SSet.N.mk s.simplex.val ((K.mem_nonDegenerate_iff _).mp s.nonDegenerate)

lemma subcomplexN_le_iff (s t : (K : SSet).N) : subcomplexN K s ≤ subcomplexN K t ↔ s ≤ t := by
  constructor
  · intro h
    obtain ⟨f, hf, he⟩ := SSet.N.le_iff_exists_mono.mp h
    exact SSet.N.le_iff_exists_mono.mpr ⟨f, hf, Subtype.ext he⟩
  · intro h
    obtain ⟨f, hf, he⟩ := SSet.N.le_iff_exists_mono.mp h
    exact SSet.N.le_iff_exists_mono.mpr ⟨f, hf, congrArg Subtype.val he⟩

lemma subcomplexN_injective : Function.Injective (subcomplexN K) := by
  intro s t h
  exact le_antisymm ((subcomplexN_le_iff K s t).mp h.le)
    ((subcomplexN_le_iff K t s).mp h.ge)

lemma subcomplexN_downward (s : (K : SSet).N) (t : (nerve E).N)
    (h : t ≤ subcomplexN K s) : ∃ a : (K : SSet).N, subcomplexN K a = t := by
  obtain ⟨f, _, he⟩ := SSet.N.le_iff_exists_mono.mp h
  have ht : t.simplex ∈ K.obj (op ⦋t.dim⦌) := he ▸ K.map f.op s.simplex.property
  let a : (K : SSet).N := SSet.N.mk ⟨t.simplex, ht⟩
    ((K.mem_nonDegenerate_iff _).mpr t.nonDegenerate)
  exact ⟨a, rfl⟩

def AllowedChains := {c : NonemptyFiniteChains E // ∃ s : (K : SSet).N,
  simplexChain (subcomplexN K s).simplex = c}

instance instPartialOrderAllowedChains : PartialOrder (AllowedChains K) := inferInstanceAs (PartialOrder {_c // _})

def allowedChainInclusion : AllowedChains K →o NonemptyFiniteChains E :=
  OrderHom.Subtype.val _

noncomputable def subcomplexChain (s : (K : SSet).N) : AllowedChains K :=
  ⟨simplexChain (subcomplexN K s).simplex, s, rfl⟩

lemma allowedChains_downward {c d : NonemptyFiniteChains E} (h : c ≤ d)
    (hd : ∃ s : (K : SSet).N, simplexChain (subcomplexN K s).simplex = d) :
    ∃ s : (K : SSet).N, simplexChain (subcomplexN K s).simplex = c := by
  obtain ⟨s, rfl⟩ := hd
  obtain ⟨a, ha⟩ := subcomplexN_downward K s (chainSimplex c)
    ((simplexChain_le_iff _ _).mp (by rwa [simplexChain_chainSimplex]))
  exact ⟨a, by rw [ha, simplexChain_chainSimplex]⟩

noncomputable def allowedChainSimplex (c : AllowedChains K) : (K : SSet).N := c.property.choose

lemma subcomplexChain_allowedChainSimplex (c : AllowedChains K) :
    subcomplexChain K (allowedChainSimplex K c) = c :=
  Subtype.ext c.property.choose_spec

noncomputable def subcomplexNondegenerateChains : (K : SSet).N ≃o AllowedChains K where
  toFun := subcomplexChain K
  invFun := allowedChainSimplex K
  left_inv s := by
    apply subcomplexN_injective K
    apply nerveNondegenerateChains.injective
    exact congrArg Subtype.val (subcomplexChain_allowedChainSimplex K (subcomplexChain K s))
  right_inv := subcomplexChain_allowedChainSimplex K
  map_rel_iff' := fun {s t} => (simplexChain_le_iff _ _).trans (subcomplexN_le_iff K s t)

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)

noncomputable def sdSubcomplexVertices (s : (K : SSet).N) :
    NonemptyFiniteChains (SimplexCategory.toPartOrd.obj ⦋s.dim⦌) →o AllowedChains K where
  toFun c := ⟨c.map (simplexVertices s.simplex.val), allowedChains_downward K (by
    intro a ha
    obtain ⟨i, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp ha
    exact (mem_simplexChain _ _).mpr ⟨i.down, rfl⟩) ⟨s, rfl⟩⟩
  monotone' _ _ h := (NonemptyFiniteChains.orderHomMap _).monotone h

noncomputable def sdSubcomplexLeg (s : (K : SSet).N) :
    SimplexCategory.sd.obj ⦋s.dim⦌ ⟶ nerve (AllowedChains K) :=
  nerveMap (sdSubcomplexVertices K s).monotone.functor

abbrev allowedChainsForget : nerve (AllowedChains K) ⟶ nerve (NonemptyFiniteChains E) :=
  nerveMap (allowedChainInclusion K).monotone.functor

lemma allowedChainsForget_app_injective (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((allowedChainsForget K).app k) := by
  intro x y h
  apply nerve.ext_of_isThin
  funext i
  exact Subtype.ext (congrArg (fun q => q.obj i) h)

instance instMonoSSetAllowedChainsForget : Mono (allowedChainsForget K) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  exact (CategoryTheory.mono_iff_injective _).mpr (allowedChainsForget_app_injective K k)

lemma sdSubcomplexLeg_forget (s : (K : SSet).N) :
    sdSubcomplexLeg K s ≫ allowedChainsForget K = sdNerveLeg (subcomplexN K s) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  rfl

lemma subcomplexN_monoOfLE {s t : (K : SSet).N} (h : s ≤ t) :
    SSet.N.monoOfLE ((subcomplexN_le_iff K s t).mpr h) = SSet.N.monoOfLE h := by
  apply SSet.Nonsingular.injective_map (subcomplexN K t).simplex (subcomplexN K t).nonDegenerate
  rw [SSet.N.map_monoOfLE]
  exact (congrArg Subtype.val (SSet.N.map_monoOfLE h)).symm

lemma sdSubcomplexLeg_naturality {s t : (K : SSet).N} (h : s ≤ t) :
    SimplexCategory.sd.map (SSet.N.monoOfLE h) ≫ sdSubcomplexLeg K t = sdSubcomplexLeg K s := by
  apply (cancel_mono (allowedChainsForget K)).mp
  rw [Category.assoc, sdSubcomplexLeg_forget, sdSubcomplexLeg_forget]
  rw [← subcomplexN_monoOfLE K h]
  exact sdNerveLeg_naturality _

noncomputable def sdSubcomplexCocone : Cocone ((K : SSet).functorN' ⋙ SSet.sd) where
  pt := nerve (AllowedChains K)
  ι.app s := (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom ≫ sdSubcomplexLeg K s
  ι.naturality s t f := by
    change SSet.sd.map (SSet.stdSimplex.map (SSet.N.monoOfLE (leOfHom f))) ≫
      ((SSet.stdSimplex.sdIso.app ⦋t.dim⦌).hom ≫ sdSubcomplexLeg K t) = _
    simp only [Functor.const_obj_map]
    erw [← Category.assoc, SSet.stdSimplex.sdIso.hom.naturality,
      Category.assoc, sdSubcomplexLeg_naturality]
    exact (Category.comp_id _).symm

noncomputable def sdSubcomplexMap : SSet.sd.obj (K : SSet) ⟶ nerve (AllowedChains K) :=
  (isColimitOfPreserves SSet.sd (K : SSet).isColimitCoconeN').desc (sdSubcomplexCocone K)

lemma sdSubcomplexMap_fac (s : (K : SSet).N) :
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ sdSubcomplexMap K =
      (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom ≫ sdSubcomplexLeg K s :=
  (isColimitOfPreserves SSet.sd (K : SSet).isColimitCoconeN').fac (sdSubcomplexCocone K) s

noncomputable def sdSubcomplexInjection (s : (K : SSet).N) :
    SimplexCategory.sd.obj ⦋s.dim⦌ ⟶ SSet.sd.obj (K : SSet) :=
  (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv ≫
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex)

lemma sdSubcomplexInjection_comp (s : (K : SSet).N) :
    sdSubcomplexInjection K s ≫ sdSubcomplexMap K = sdSubcomplexLeg K s := by
  rw [sdSubcomplexInjection, Category.assoc, sdSubcomplexMap_fac,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma sdSubcomplexInjection_naturality {s t : (K : SSet).N} (h : s ≤ t) :
    SimplexCategory.sd.map (SSet.N.monoOfLE h) ≫ sdSubcomplexInjection K t =
      sdSubcomplexInjection K s := by
  unfold sdSubcomplexInjection
  erw [← Category.assoc, SSet.stdSimplex.sdIso.inv.naturality,
    Category.assoc, ← SSet.sd.map_comp,
    SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex]
  rfl

lemma sdSubcomplexInjection_jointly_surjective (k : SimplexCategoryᵒᵖ)
    (z : (SSet.sd.obj (K : SSet)).obj k) :
    ∃ (s : (K : SSet).N) (x : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k),
      (sdSubcomplexInjection K s).app k x = z := by
  have hc := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj k)
    (isColimitOfPreserves SSet.sd (K : SSet).isColimitCoconeN')
  obtain ⟨s, x, hx⟩ := Types.jointly_surjective_of_isColimit hc z
  refine ⟨s, (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x, ?_⟩
  change (SSet.sd.map (SSet.yonedaEquiv.symm s.simplex)).app k
    ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv.app k
      ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x)) = z
  have he := congrArg (fun f => f.app k x) (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom_inv_id
  change (SSet.stdSimplex.sdIso.app ⦋s.dim⦌).inv.app k
      ((SSet.stdSimplex.sdIso.app ⦋s.dim⦌).hom.app k x) = x at he
  rw [he]
  exact hx

lemma sdSubcomplexLeg_app_injective (s : (K : SSet).N) (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((sdSubcomplexLeg K s).app k) := by
  intro x y h
  exact sdNerveLeg_app_injective (subcomplexN K s) k
    (congrArg ((allowedChainsForget K).app k) h)

lemma sdSubcomplexLeg_obj_le (s : (K : SSet).N) (k : SimplexCategoryᵒᵖ)
    (x : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k) (j : Fin (k.unop.len+1)) :
    ((sdSubcomplexLeg K s).app k x).obj j ≤ subcomplexChain K s :=
  sdNerveLeg_obj_le (subcomplexN K s) k x j

lemma sdSubcomplexLeg_surjective_on (s : (K : SSet).N) (k : SimplexCategoryᵒᵖ)
    (q : (nerve (AllowedChains K)).obj k) (h : ∀ i, q.obj i ≤ subcomplexChain K s) :
    ∃ p : (SimplexCategory.sd.obj ⦋s.dim⦌).obj k, (sdSubcomplexLeg K s).app k p = q := by
  obtain ⟨p, hp⟩ := sdNerveLeg_surjective_on (subcomplexN K s) k
    ((allowedChainsForget K).app k q) h
  exact ⟨p, allowedChainsForget_app_injective K k hp⟩

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)

lemma sdSubcomplexMap_app_surjective (k : SimplexCategoryᵒᵖ) :
    Function.Surjective ((sdSubcomplexMap K).app k) := by
  intro q
  let s := allowedChainSimplex K (q.obj (Fin.last k.unop.len))
  have h (i) : q.obj i ≤ subcomplexChain K s := by
    rw [subcomplexChain_allowedChainSimplex]
    exact q.monotone (Fin.le_last i)
  obtain ⟨p, hp⟩ := sdSubcomplexLeg_surjective_on K s k q h
  refine ⟨(sdSubcomplexInjection K s).app k p, ?_⟩
  exact (congrArg (fun f => f.app k p) (sdSubcomplexInjection_comp K s)).trans hp

lemma sdSubcomplexMap_app_injective (k : SimplexCategoryᵒᵖ) :
    Function.Injective ((sdSubcomplexMap K).app k) := by
  intro x y hxy
  obtain ⟨s, p, rfl⟩ := sdSubcomplexInjection_jointly_surjective K k x
  obtain ⟨t, q, rfl⟩ := sdSubcomplexInjection_jointly_surjective K k y
  have hs := congrArg (fun f => f.app k p) (sdSubcomplexInjection_comp K s)
  have ht := congrArg (fun f => f.app k q) (sdSubcomplexInjection_comp K t)
  have he : (sdSubcomplexLeg K s).app k p = (sdSubcomplexLeg K t).app k q := hs.symm.trans (hxy.trans ht)
  let v := (sdSubcomplexLeg K s).app k p
  let a := allowedChainSimplex K (v.obj (Fin.last k.unop.len))
  have has : a ≤ s := by
    apply (subcomplexNondegenerateChains K).le_iff_le.mp
    change subcomplexChain K a ≤ subcomplexChain K s
    rw [subcomplexChain_allowedChainSimplex]
    exact sdSubcomplexLeg_obj_le K s k p _
  have hat : a ≤ t := by
    apply (subcomplexNondegenerateChains K).le_iff_le.mp
    change subcomplexChain K a ≤ subcomplexChain K t
    rw [subcomplexChain_allowedChainSimplex]
    dsimp only [v]
    rw [he]
    exact sdSubcomplexLeg_obj_le K t k q _
  obtain ⟨r, hr⟩ := sdSubcomplexLeg_surjective_on K a k v (fun i => by
    rw [subcomplexChain_allowedChainSimplex]
    exact v.monotone (Fin.le_last i))
  have hps : (SimplexCategory.sd.map (SSet.N.monoOfLE has)).app k r = p := by
    apply sdSubcomplexLeg_app_injective K s k
    exact (congrArg (fun f => f.app k r) (sdSubcomplexLeg_naturality K has)).trans hr
  have hqt : (SimplexCategory.sd.map (SSet.N.monoOfLE hat)).app k r = q := by
    apply sdSubcomplexLeg_app_injective K t k
    exact (congrArg (fun f => f.app k r) (sdSubcomplexLeg_naturality K hat)).trans (hr.trans he)
  rw [← hps, ← hqt]
  exact (congrArg (fun f => f.app k r) (sdSubcomplexInjection_naturality K has)).trans
    (congrArg (fun f => f.app k r) (sdSubcomplexInjection_naturality K hat)).symm

instance sdSubcomplexMap_isIso : IsIso (sdSubcomplexMap K) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro k
  exact (CategoryTheory.isIso_iff_bijective _).mpr
    ⟨sdSubcomplexMap_app_injective K k, sdSubcomplexMap_app_surjective K k⟩

noncomputable def sdSubcomplexIso : SSet.sd.obj (K : SSet) ≅ nerve (AllowedChains K) :=
  asIso (sdSubcomplexMap K)

lemma sdSubcomplexMap_naturality : SSet.sd.map K.ι ≫ sdNerveMap =
    sdSubcomplexMap K ≫ allowedChainsForget K := by
  apply (isColimitOfPreserves SSet.sd (K : SSet).isColimitCoconeN').hom_ext
  intro s
  change SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫
      (SSet.sd.map K.ι ≫ sdNerveMap) =
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ (sdSubcomplexMap K ≫ _)
  erw [← Category.assoc, ← SSet.sd.map_comp, SSet.yonedaEquiv_symm_comp,
    sdNerveMap_fac (subcomplexN K s), ← Category.assoc, sdSubcomplexMap_fac, Category.assoc]
  rw [sdSubcomplexLeg_forget]
  rfl

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GlobularComplexes
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globular Complexes. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {X : Type u} [PartialOrder X]

variable {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)

noncomputable def orderedSimplexSubcomplex {m : ℕ} (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (nerve (ULift.{u} (Fin (m+1)))).Subcomplex :=
  SSet.Subcomplex.range (K.ι ≫ (SSet.stdSimplex.isoNerve.{u} m).hom)

noncomputable def orderedSimplexSubcomplexIso {m : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (K : SSet.{u}) ≅ (orderedSimplexSubcomplex K : SSet) :=
  by
  let f : (K : SSet.{u}) ⟶ nerve (ULift.{u} (Fin (m+1))) :=
    K.ι ≫ (SSet.stdSimplex.isoNerve.{u} m).hom
  haveI : Mono f := mono_comp _ _
  let t : (K : SSet.{u}) ⟶ (SSet.Subcomplex.range f : SSet.{u}) := SSet.Subcomplex.toRange f
  haveI : Mono t := mono_of_mono_fac (SSet.Subcomplex.toRange_ι f)
  haveI : Epi t := inferInstanceAs (Epi (Subfunctor.toRange f))
  haveI : IsIso t := isIso_of_mono_of_epi t
  exact @asIso SSet.{u} (inferInstance) _ _ t ‹IsIso t›

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionFaces
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Faces. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

abbrev OrdinalVertices (n : ℕ) := SimplexCategory.toPartOrd.{u}.obj ⦋n⦌
local instance instLinearOrderCarrierOrdinalVertices (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))
abbrev OrdinalChains (n : ℕ) := NonemptyFiniteChains (OrdinalVertices.{u} n)
def ordinalVertex (n : ℕ) (i : Fin (n + 1)) : OrdinalVertices.{u} n := ULift.up i

lemma le_initialFlag (n : ℕ) (s : OrdinalChains.{u} n) (a : OrdinalVertices.{u} n) :
    s ≤ initialFlag ⦋n⦌ a ↔ chainLast s ≤ a := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp (h (chainGreatest_mem s))).2
  · intro h x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (le_chainGreatest s hx).trans h⟩

noncomputable def partialLastVertex (n : ℕ) (k : OrdinalVertices.{u} n) :
    OrdinalChains.{u} n →o OrdinalChains.{u} n := by
  exact {
    toFun := fun s => if chainLast s ≤ k then s else initialFlag ⦋n⦌ (chainLast s)
    monotone' := by
      intro s t h
      have hst : chainLast s ≤ chainLast t := chainLast.monotone h
      by_cases hs : chainLast s ≤ k
      · by_cases ht : chainLast t ≤ k
        · simpa only [ite_eq_left hs, ite_eq_left ht] using h
        · simpa only [ite_eq_left hs, ite_eq_right ht] using (le_initialFlag n s (chainLast t)).2 hst
      · have ht : ¬chainLast t ≤ k := fun ht => hs (hst.trans ht)
        simpa only [ite_eq_right hs, ite_eq_right ht] using (initialFlag ⦋n⦌).monotone hst }

lemma partialLastVertex_apply (n : ℕ) (k : OrdinalVertices.{u} n)
    (s : OrdinalChains.{u} n) : partialLastVertex n k s =
      if chainLast s ≤ k then s else initialFlag ⦋n⦌ (chainLast s) := rfl

lemma partialLastVertex_initialFlag (n : ℕ) (k a : OrdinalVertices.{u} n) :
    partialLastVertex n k (initialFlag ⦋n⦌ a) = initialFlag ⦋n⦌ a := by
  rw [partialLastVertex_apply, chainLast_initialFlag]
  split_ifs <;> rfl

lemma partialLastVertex_comp_of_le (n : ℕ) (j k : OrdinalVertices.{u} n) (hjk : j ≤ k) :
    (partialLastVertex n j).comp (partialLastVertex n k) = partialLastVertex n j := by
  apply OrderHom.ext
  funext s
  change partialLastVertex n j (partialLastVertex n k s) = _
  rw [partialLastVertex_apply n k]
  split_ifs with h
  · rfl
  · rw [partialLastVertex_initialFlag, partialLastVertex_apply,
      ite_eq_right (fun hj => h (hj.trans hjk))]

lemma partialLastVertex_top (n : ℕ) :
    partialLastVertex.{u} n ⟨Fin.last n⟩ = OrderHom.id := by
  apply OrderHom.ext
  funext s
  exact ite_eq_left (show (chainLast s).down ≤ Fin.last n from Fin.le_last _)

lemma partialLastVertex_zero (n : ℕ) (s : OrdinalChains.{u} n) :
    partialLastVertex.{u} n (ordinalVertex n 0) s = initialFlag ⦋n⦌ (chainLast s) := by
  rw [partialLastVertex_apply]
  split_ifs with h
  · apply le_antisymm
    · exact (le_initialFlag n s _).2 le_rfl
    · intro x hx
      have hx' : x ≤ chainLast s := (Finset.mem_filter.mp hx).2
      have hzero : chainLast s = ⟨(0 : Fin (n + 1))⟩ := by
        apply ULift.ext
        exact le_antisymm h (Fin.zero_le _)
      have hxzero : x = chainLast s := by
        apply ULift.ext
        exact le_antisymm hx' (by rw [hzero]; exact Fin.zero_le _)
      exact hxzero.symm ▸ chainGreatest_mem s
  · rfl

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma exComparison_apply (X : SSet.{u}) (n : ℕ) (x : X.obj (op ⦋n⦌)) :
    (exComparison.app X).app (op ⦋n⦌) x =
      ULift.up (simplexLastVertex.app ⦋n⦌ ≫ SSet.yonedaEquiv.symm x) := by
  change ((SSet.sdExAdjunction.homEquiv X X) (lastVertex.app X)).app _ x = _
  erw [Presheaf.uliftYonedaAdjunction_homEquiv_app]
  congr 1
  change (SSet.stdSimplex.sdIso.app ⦋n⦌).inv ≫
    SSet.sd.map (SSet.yonedaEquiv.symm x) ≫ lastVertex.app X = _
  erw [lastVertex.naturality, lastVertex_stdSimplex]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

noncomputable def partialLastMap (n : ℕ) (k : OrdinalVertices.{u} n) :
    SimplexCategory.sd.obj ⦋n⦌ ⟶ SimplexCategory.sd.obj ⦋n⦌ :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom (partialLastVertex n k))

lemma partialLastMap_comp_of_le (n : ℕ) (j k : OrdinalVertices.{u} n) (hjk : j ≤ k) :
    partialLastMap n k ≫ partialLastMap n j = partialLastMap n j := by
  erw [partialLastMap, partialLastMap, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  exact partialLastVertex_comp_of_le n j k hjk

lemma partialLastMap_zero (n : ℕ) :
    partialLastMap.{u} n (ordinalVertex n 0) =
      simplexLastVertex.app ⦋n⦌ ≫ simplexLastVertexSection ⦋n⦌ := by
  have h : PartOrd.ofHom (partialLastVertex.{u} n (ordinalVertex n 0)) =
      chainLastNat.app (SimplexCategory.toPartOrd.obj ⦋n⦌) ≫
      PartOrd.ofHom (initialFlag ⦋n⦌) := by
    apply PartOrd.hom_ext
    apply OrderHom.ext
    funext s
    exact partialLastVertex_zero n s
  change _ = (PartOrd.nerveFunctor.map _ ≫ simplexNerveIso.inv.app _) ≫
    (simplexNerveIso.hom.app _ ≫ PartOrd.nerveFunctor.map _)
  simp only [Category.assoc]
  change PartOrd.nerveFunctor.map _ = _
  erw [h, CategoryTheory.Functor.map_comp]
  erw [← Category.assoc (simplexNerveIso.inv.app ⦋n⦌),
    simplexNerveIso.inv_hom_id_app, Category.id_comp]

def ExLevel (X : SSet.{u}) (n : ℕ) (k : OrdinalVertices.{u} n)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) : Prop :=
  partialLastMap n k ≫ x.down = x.down

lemma ExLevel.mono {X : SSet.{u}} {n : ℕ} {j k : OrdinalVertices.{u} n}
    {x : (SSet.ex.obj X).obj (op ⦋n⦌)} (h : ExLevel X n j x) (hjk : j ≤ k) :
    ExLevel X n k x := by
  change partialLastMap n k ≫ x.down = _
  calc
    _ = partialLastMap n k ≫ partialLastMap n j ≫ x.down := by erw [h]
    _ = x.down := by erw [← Category.assoc, partialLastMap_comp_of_le n j k hjk]; exact h

lemma exLevel_top (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ExLevel X n ⟨Fin.last n⟩ x := by
  change PartOrd.nerveFunctor.map (PartOrd.ofHom (partialLastVertex n ⟨Fin.last n⟩)) ≫ _ = _
  erw [partialLastVertex_top]
  change PartOrd.nerveFunctor.map (𝟙 _) ≫ _ = _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

lemma exLevel_zero_iff (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ExLevel X n (ordinalVertex n 0) x ↔
      x ∈ Set.range ((exComparison.app X).app (op ⦋n⦌)) := by
  constructor
  · intro h
    refine ⟨SSet.yonedaEquiv (simplexLastVertexSection ⦋n⦌ ≫ x.down), ?_⟩
    erw [exComparison_apply, Equiv.symm_apply_apply]
    apply ULift.ext
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x.down)
      (partialLastMap_zero n).symm).trans h)
  · rintro ⟨y, rfl⟩
    change partialLastMap n (ordinalVertex n 0) ≫ _ = _
    erw [exComparison_apply]
    change partialLastMap n (ordinalVertex n 0) ≫ (simplexLastVertex.app ⦋n⦌ ≫ _) = _
    erw [partialLastMap_zero]
    simp only [Category.assoc, ← Category.assoc (simplexLastVertexSection ⦋n⦌),
      simplexLastVertexSection_comp, Category.id_comp]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

noncomputable def singletonChain {A : Type*} [PartialOrder A] (a : A) :
    NonemptyFiniteChains A := by
  classical
  exact { finset := {a}
          comparable := by
            rintro ⟨x, hx⟩ ⟨y, hy⟩
            simp only [Finset.mem_singleton] at hx hy
            subst x; subst y
            exact Or.inl le_rfl }

lemma mem_singletonChain {A : Type*} [PartialOrder A] (a x : A) :
    x ∈ (singletonChain a).finset ↔ x = a := Finset.mem_singleton

noncomputable def chainUnionMap {A B : Type*} [PartialOrder A] [LinearOrder B]
    (f : A → NonemptyFiniteChains B) : NonemptyFiniteChains A →o NonemptyFiniteChains B := by
  classical
  exact {
    toFun s := {
      finset := s.finset.biUnion (fun a => (f a).finset)
      nonempty := by
        obtain ⟨a, ha⟩ := s.nonempty
        obtain ⟨b, hb⟩ := (f a).nonempty
        exact ⟨b, Finset.mem_biUnion.mpr ⟨a, ha, hb⟩⟩
      comparable := fun a b => le_total a.val b.val }
    monotone' s t h b hb := by
      obtain ⟨a, ha, hb⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_biUnion.mpr ⟨a, h ha, hb⟩ }

lemma mem_chainUnionMap {A B : Type*} [PartialOrder A] [LinearOrder B]
    (f : A → NonemptyFiniteChains B) (s : NonemptyFiniteChains A) (b : B) :
    b ∈ (chainUnionMap f s).finset ↔ ∃ a ∈ s.finset, b ∈ (f a).finset := by
  classical
  exact Finset.mem_biUnion

lemma chainUnionMap_singleton {A : Type*} [LinearOrder A] (s : NonemptyFiniteChains A) :
    chainUnionMap singletonChain s = s := by
  apply NonemptyFiniteChains.ext
  ext a
  simp only [mem_chainUnionMap, mem_singletonChain]
  exact ⟨fun ⟨b, hb, he⟩ => he.symm ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩

lemma chainUnionMap_map {A B C : Type*} [PartialOrder A] [PartialOrder B] [LinearOrder C]
    (f : B → NonemptyFiniteChains C) (g : A →o B) (s : NonemptyFiniteChains A) :
    chainUnionMap f (s.map g) = chainUnionMap (fun a => f (g a)) s := by
  apply NonemptyFiniteChains.ext
  ext c
  simp only [mem_chainUnionMap, NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, hc⟩
    exact ⟨a, ha, hc⟩
  · rintro ⟨a, ha, hc⟩
    exact ⟨g a, ⟨a, ha, rfl⟩, hc⟩

local instance instLinearOrderCarrierOrdinalVertices_1 (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

noncomputable def extraVertexFace (n : ℕ) (k : Fin (n + 1)) (i : OrdinalVertices.{u} (n + 1)) :
    OrdinalChains.{u} n := by
  classical
  exact if i.down = k.succ then initialFlag ⦋n⦌ (ordinalVertex n k)
  else singletonChain (ordinalVertex n (k.predAbove i.down))

noncomputable def extraVertex (n : ℕ) (k : Fin (n + 1)) :
    OrdinalChains.{u} (n + 1) →o OrdinalChains.{u} n :=
  chainUnionMap (extraVertexFace n k)

lemma predAbove_succ_succAbove {n : ℕ} (k i : Fin (n + 1)) :
    k.predAbove (k.succ.succAbove i) = i := by
  apply Fin.succAbove_right_injective (p := k.succ)
  exact Fin.succ_succAbove_predAbove (Fin.succAbove_ne _ _)

lemma extraVertexFace_gap (n : ℕ) (k : Fin (n + 1)) (i : OrdinalVertices.{u} n) :
    extraVertexFace n k (ordinalVertex (n + 1) (k.succ.succAbove i.down)) = singletonChain i := by
  classical
  unfold extraVertexFace
  erw [ite_eq_right (Fin.succAbove_ne _ _), predAbove_succ_succAbove]
  rfl

noncomputable def faceVertices (n : ℕ) (i : Fin (n + 2)) :
    OrdinalVertices.{u} n →o OrdinalVertices.{u} (n + 1) :=
  (SimplexCategory.toPartOrd.map (SimplexCategory.δ i)).hom

lemma extraVertex_face (n : ℕ) (k : Fin (n + 1)) (s : OrdinalChains.{u} n) :
    extraVertex n k (s.map (faceVertices n k.succ)) = s := by
  change chainUnionMap _ _ = _
  erw [chainUnionMap_map]
  have h : (fun a => extraVertexFace n k (faceVertices n k.succ a)) = singletonChain := by
    funext a
    exact extraVertexFace_gap n k a
  rw [h]
  exact chainUnionMap_singleton s

noncomputable def extraVertexMap (n : ℕ) (k : Fin (n + 1)) :
    SimplexCategory.sd.obj ⦋n + 1⦌ ⟶ SimplexCategory.sd.obj ⦋n⦌ :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom (extraVertex n k))

lemma extraVertexMap_face (n : ℕ) (k : Fin (n + 1)) :
    SimplexCategory.sd.map (SimplexCategory.δ k.succ) ≫ extraVertexMap.{u} n k = 𝟙 _ := by
  have h : PartOrd.nonemptyFiniteChainsFunctor.map
      (SimplexCategory.toPartOrd.map (SimplexCategory.δ k.succ)) ≫
      PartOrd.ofHom (extraVertex.{u} n k) = 𝟙 _ := by
    apply PartOrd.hom_ext
    apply OrderHom.ext
    funext s
    exact extraVertex_face n k s
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ = _
  exact (PartOrd.nerveFunctor.map_comp _ _).symm.trans
    ((congrArg PartOrd.nerveFunctor.map h).trans (PartOrd.nerveFunctor.map_id _))

noncomputable def exPairSimplex (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) : (SSet.ex.obj X).obj (op ⦋n + 1⦌) :=
  ULift.up (extraVertexMap n k ≫ x.down)

lemma exPairSimplex_face (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    (SSet.ex.obj X).δ k.succ (exPairSimplex X n k x) = x := by
  apply ULift.ext
  change SimplexCategory.sd.map (SimplexCategory.δ k.succ) ≫ (extraVertexMap n k ≫ x.down) = _
  erw [← Category.assoc, extraVertexMap_face, Category.id_comp]

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionPairing
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Pairing. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma chainLast_singletonChain {A : Type*} [PartialOrder A] (a : A) :
    chainLast (singletonChain a) = a :=
  Finset.mem_singleton.mp (chainGreatest_mem (singletonChain a))

lemma chainLast_chainUnionMap {A B : Type*} [PartialOrder A] [LinearOrder B]
    (f : A → NonemptyFiniteChains B) (g : A →o B)
    (hg : ∀ a, chainLast (f a) = g a) (s : NonemptyFiniteChains A) :
    chainLast (chainUnionMap f s) = g (chainLast s) := by
  apply le_antisymm
  · obtain ⟨a, ha, hb⟩ := (mem_chainUnionMap f s _).mp
      (chainGreatest_mem (chainUnionMap f s))
    exact (le_chainGreatest (f a) hb).trans ((hg a).le.trans (g.monotone (le_chainGreatest s ha)))
  · apply le_chainGreatest
    apply (mem_chainUnionMap f s _).mpr
    exact ⟨chainLast s, chainGreatest_mem s, hg (chainLast s) ▸ chainGreatest_mem (f (chainLast s))⟩

local instance subdivisionPairingExtraVertexLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma mem_initialFlag (n : ℕ) (a b : OrdinalVertices.{u} n) :
    b ∈ (initialFlag ⦋n⦌ a).finset ↔ b ≤ a := by
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

noncomputable def collapseVertices (n : ℕ) (k : Fin (n + 1)) :
    OrdinalVertices.{u} (n + 1) →o OrdinalVertices.{u} n :=
  (SimplexCategory.toPartOrd.map (SimplexCategory.σ k)).hom

lemma face_collapse_le (n : ℕ) (k : Fin (n + 1)) (a : OrdinalVertices.{u} (n + 1)) :
    faceVertices n k.succ (collapseVertices n k a) ≤ a := by
  change k.succ.succAbove (k.predAbove a.down) ≤ a.down
  by_cases h : a.down = k.succ
  · rw [h, Fin.predAbove_succ_self, Fin.succAbove_succ_self]
    exact k.castSucc_le_succ
  · exact (Fin.succ_succAbove_predAbove h).le

lemma extraVertexFace_last (n : ℕ) (k : Fin (n + 1)) (a : OrdinalVertices.{u} (n + 1)) :
    chainLast (extraVertexFace n k a) = collapseVertices n k a := by
  classical
  unfold extraVertexFace
  split_ifs with h
  · erw [chainLast_initialFlag]
    apply ULift.ext
    change k = k.predAbove a.down
    rw [h, Fin.predAbove_succ_self]
  · exact chainLast_singletonChain _

lemma chainLast_extraVertex (n : ℕ) (k : Fin (n + 1)) (s : OrdinalChains.{u} (n + 1)) :
    chainLast (extraVertex n k s) = collapseVertices n k (chainLast s) :=
  chainLast_chainUnionMap _ _ (extraVertexFace_last n k) s

lemma extraVertex_initialFlag (n : ℕ) (k : Fin (n + 1)) (a : OrdinalVertices.{u} (n + 1)) :
    extraVertex n k (initialFlag ⦋n + 1⦌ a) = initialFlag ⦋n⦌ (collapseVertices n k a) := by
  apply NonemptyFiniteChains.ext
  ext b
  change b ∈ (chainUnionMap _ _).finset ↔ _
  erw [mem_chainUnionMap, mem_initialFlag]
  constructor
  · rintro ⟨c, hc, hb⟩
    have hbc := le_chainGreatest (extraVertexFace n k c) hb
    exact hbc.trans ((extraVertexFace_last n k c).le.trans ((collapseVertices n k).monotone ((mem_initialFlag _ _ _).mp hc)))
  · intro hb
    refine ⟨faceVertices n k.succ b, (mem_initialFlag _ _ _).mpr ?_, ?_⟩
    · exact ((faceVertices n k.succ).monotone hb).trans (face_collapse_le n k a)
    · erw [extraVertexFace_gap]
      exact (mem_singletonChain _ _).mpr rfl

lemma extraVertex_eq_initialFlag_of_last_inserted (n : ℕ) (k : Fin (n + 1))
    (s : OrdinalChains.{u} (n + 1)) (hs : chainLast s = ordinalVertex (n + 1) k.succ) :
    extraVertex n k s = initialFlag ⦋n⦌ (ordinalVertex n k) := by
  classical
  apply le_antisymm
  · apply (le_initialFlag _ _ _).mpr
    rw [chainLast_extraVertex, hs]
    change (ordinalVertex n (k.predAbove k.succ)) ≤ _
    rw [Fin.predAbove_succ_self]
  · intro b hb
    apply (mem_chainUnionMap _ _ _).mpr
    refine ⟨ordinalVertex (n + 1) k.succ, hs ▸ chainGreatest_mem s, ?_⟩
    change b ∈ (extraVertexFace n k (ordinalVertex (n + 1) k.succ)).finset
    have he : extraVertexFace n k (ordinalVertex (n + 1) k.succ) =
        initialFlag ⦋n⦌ (ordinalVertex n k) := ite_eq_left rfl
    exact he.symm ▸ hb

lemma predAbove_le_eq_of_castSucc_lt {n : ℕ} {j k : Fin (n + 1)} (hjk : j ≤ k)
    {i : Fin (n + 2)} (hij : j.castSucc < i) (hdi : k.predAbove i ≤ j) :
    i = k.succ ∧ j = k := by
  unfold Fin.predAbove at hdi
  split_ifs at hdi with h
  · have hi : i.val = k.val + 1 ∧ j.val = k.val := by
      simp only [Fin.le_iff_val_le_val, Fin.lt_def, Fin.val_castSucc,
        Fin.val_pred] at hdi hij hjk h
      omega
    exact ⟨Fin.ext hi.1, Fin.ext hi.2⟩
  · have : False := by
      simp only [Fin.le_iff_val_le_val, Fin.lt_def, Fin.val_castSucc,
        Fin.coe_castPred] at hdi hij
      omega
    exact this.elim

lemma extraVertex_partialLastVertex (n : ℕ) (j k : Fin (n + 1)) (hjk : j ≤ k)
    (s : OrdinalChains.{u} (n + 1)) :
    extraVertex n k (partialLastVertex (n + 1) (ordinalVertex (n + 1) j.castSucc) s) =
      partialLastVertex n (ordinalVertex n j) (extraVertex n k s) := by
  rw [partialLastVertex_apply, partialLastVertex_apply, chainLast_extraVertex]
  by_cases h : chainLast s ≤ ordinalVertex (n + 1) j.castSucc
  · rw [ite_eq_left h]
    have hc : collapseVertices n k (chainLast s) ≤ ordinalVertex n j := by
      have hd := (collapseVertices n k).monotone h
      change collapseVertices n k (chainLast s) ≤ ordinalVertex n (k.predAbove j.castSucc) at hd
      exact hd.trans (by rw [Fin.predAbove_castSucc_of_le _ _ hjk])
    rw [ite_eq_left hc]
  · rw [ite_eq_right h, extraVertex_initialFlag]
    by_cases hc : collapseVertices n k (chainLast s) ≤ ordinalVertex n j
    · rw [ite_eq_left hc]
      obtain ⟨hi, hjk'⟩ := predAbove_le_eq_of_castSucc_lt hjk (lt_of_not_ge h) hc
      subst j
      have hs : chainLast s = ordinalVertex (n + 1) k.succ := ULift.ext _ _ hi
      rw [extraVertex_eq_initialFlag_of_last_inserted n k s hs, hs]
      change initialFlag ⦋n⦌ (ordinalVertex n (k.predAbove k.succ)) = _
      rw [Fin.predAbove_succ_self]
    · rw [ite_eq_right hc]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma extraVertexMap_partialLastMap (n : ℕ) (j k : Fin (n + 1)) (hjk : j ≤ k) :
    partialLastMap (n + 1) (ordinalVertex (n + 1) j.castSucc) ≫ extraVertexMap.{u} n k =
      extraVertexMap n k ≫ partialLastMap n (ordinalVertex n j) := by
  unfold partialLastMap extraVertexMap
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_partialLastVertex n j k hjk s

lemma exPairSimplex_level_iff (X : SSet.{u}) (n : ℕ) (j k : Fin (n + 1)) (hjk : j ≤ k)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ExLevel X (n + 1) (ordinalVertex (n + 1) j.castSucc) (exPairSimplex X n k x) ↔
      ExLevel X n (ordinalVertex n j) x := by
  change (partialLastMap _ _ ≫ (extraVertexMap n k ≫ x.down) = extraVertexMap n k ≫ x.down) ↔ _
  erw [← Category.assoc, extraVertexMap_partialLastMap n j k hjk, Category.assoc]
  constructor
  · intro h
    have hh := congrArg (SimplexCategory.sd.map (SimplexCategory.δ k.succ) ≫ ·) h
    change partialLastMap n (ordinalVertex n j) ≫ x.down = x.down
    simpa only [← Category.assoc, extraVertexMap_face, Category.id_comp] using hh
  · intro h
    erw [h]

lemma map_singletonChain {A B : Type*} [PartialOrder A] [PartialOrder B]
    (g : A →o B) (a : A) : (singletonChain a).map g = singletonChain (g a) := by
  apply NonemptyFiniteChains.ext
  ext b
  simp only [NonemptyFiniteChains.mem_map_iff, mem_singletonChain]
  exact ⟨fun ⟨a', h, e⟩ => h ▸ e.symm, fun h => ⟨a, rfl, h.symm⟩⟩

lemma map_chainUnionMap {A B C : Type*} [PartialOrder A] [LinearOrder B] [LinearOrder C]
    (f : A → NonemptyFiniteChains B) (g : B →o C) (s : NonemptyFiniteChains A) :
    (chainUnionMap f s).map g = chainUnionMap (fun a => (f a).map g) s := by
  apply NonemptyFiniteChains.ext
  ext c
  simp only [NonemptyFiniteChains.mem_map_iff, mem_chainUnionMap]
  exact ⟨fun ⟨b, ⟨a, ha, hb⟩, he⟩ => ⟨a, ha, b, hb, he⟩,
    fun ⟨a, ha, b, hb, he⟩ => ⟨b, ⟨a, ha, hb⟩, he⟩⟩

local instance subdivisionPairingFaceLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma faceVertices_of_lt (n : ℕ) (i : Fin (n + 2)) (a : OrdinalVertices.{u} n)
    (h : a.down.castSucc < i) :
    faceVertices n i a = ordinalVertex (n + 1) a.down.castSucc := by
  change ordinalVertex _ (i.succAbove a.down) = _
  rw [Fin.succAbove_of_castSucc_lt _ _ h]

lemma initialFlag_map_faceVertices (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (h : k.castSucc < i) :
    (initialFlag ⦋n⦌ (ordinalVertex n k)).map (faceVertices n i) =
      initialFlag ⦋n + 1⦌ (ordinalVertex (n + 1) k.castSucc) := by
  apply NonemptyFiniteChains.ext
  ext b
  rw [NonemptyFiniteChains.mem_map_iff, mem_initialFlag]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hak : a.down ≤ k := (mem_initialFlag _ _ _).mp ha
    rw [faceVertices_of_lt _ _ _ ((show a.down.castSucc ≤ k.castSucc from hak).trans_lt h)]
    exact hak
  · intro hb
    have hbn : b.down.val < n + 1 := lt_of_le_of_lt hb k.isLt
    let a := ordinalVertex n (⟨b.down.val, hbn⟩ : Fin (n + 1))
    refine ⟨a, (mem_initialFlag _ _ _).mpr hb, ?_⟩
    rw [faceVertices_of_lt _ _ _ (show a.down.castSucc < i from hb.trans_lt h)]
    rfl

lemma extraVertexFace_highFace (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hki : k.castSucc < i) (a : OrdinalVertices.{u} (n + 1)) :
    extraVertexFace (n + 1) k.castSucc (faceVertices (n + 1) i.succ a) =
      (extraVertexFace n k a).map (faceVertices n i) := by
  classical
  by_cases ha : a.down = k.succ
  · have h : faceVertices (n + 1) i.succ a = ordinalVertex (n + 2) k.castSucc.succ := by
      rw [faceVertices_of_lt]
      · apply ULift.ext
        rw [ha]
        rfl
      · change a.down.val < i.val + 1
        rw [ha]
        exact Nat.succ_lt_succ hki
    rw [h]
    have hleft : extraVertexFace (n + 1) k.castSucc (ordinalVertex (n + 2) k.castSucc.succ) =
        initialFlag ⦋n + 1⦌ (ordinalVertex (n + 1) k.castSucc) := ite_eq_left rfl
    have hright : extraVertexFace n k a = initialFlag ⦋n⦌ (ordinalVertex n k) := ite_eq_left ha
    rw [hleft, hright, initialFlag_map_faceVertices n k i hki]
  · have hne : (faceVertices (n + 1) i.succ a).down ≠ k.castSucc.succ := by
      intro he
      have hh := (Fin.succAbove_right_injective (p := i.succ))
      apply ha
      apply hh
      calc
        i.succ.succAbove a.down = k.castSucc.succ := he
        _ = i.succ.succAbove k.succ := by
          rw [Fin.succAbove_of_castSucc_lt _ _ (show k.succ.castSucc < i.succ from Nat.succ_lt_succ hki)]
          rfl
    unfold extraVertexFace
    erw [ite_eq_right ha, ite_eq_right hne, map_singletonChain]
    congr 1
    have he := congrArg (fun f : ⦋n + 1⦌ ⟶ ⦋n + 1⦌ => f.toOrderHom a.down)
      (SimplexCategory.δ_comp_σ_of_gt hki)
    exact ULift.ext _ _ he

lemma extraVertex_highFace (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hki : k.castSucc < i) (s : OrdinalChains.{u} (n + 1)) :
    extraVertex (n + 1) k.castSucc (s.map (faceVertices (n + 1) i.succ)) =
      (extraVertex n k s).map (faceVertices n i) := by
  change chainUnionMap _ _ = (chainUnionMap _ _).map _
  rw [chainUnionMap_map, map_chainUnionMap]
  congr 2
  funext a
  exact extraVertexFace_highFace n k i hki a

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

local instance subdivisionPairingChainLastLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma chainLast_map {A B : Type*} [PartialOrder A] [PartialOrder B]
    (s : NonemptyFiniteChains A) (f : A →o B) :
    chainLast (s.map f) = f (chainLast s) := chainGreatest_map s f

lemma faceVertices_of_le (n : ℕ) (i : Fin (n + 2)) (a : OrdinalVertices.{u} n)
    (h : i ≤ a.down.castSucc) : faceVertices n i a = ordinalVertex (n + 1) a.down.succ := by
  change ordinalVertex _ (i.succAbove a.down) = _
  rw [Fin.succAbove_of_le_castSucc _ _ h]

lemma collapseVertices_succ_of_le (n : ℕ) (k a : Fin (n + 1)) (h : k ≤ a) :
    collapseVertices n k (ordinalVertex (n + 1) a.succ) = ordinalVertex n a := by
  change ordinalVertex n (k.predAbove a.succ) = _
  rw [Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr h), Fin.pred_succ]

lemma extraVertex_lowFace_saturated (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hik : i ≤ k.castSucc) (s : OrdinalChains.{u} n) (hs : ordinalVertex n k ≤ chainLast s) :
    partialLastVertex n (ordinalVertex n k) (extraVertex n k (s.map (faceVertices n i))) =
      initialFlag ⦋n⦌ (chainLast s) := by
  have hface : chainLast (s.map (faceVertices n i)) =
      ordinalVertex (n + 1) (chainLast s).down.succ := by
    rw [chainLast_map, faceVertices_of_le _ _ _ (hik.trans hs)]
  have hlast : chainLast (extraVertex n k (s.map (faceVertices n i))) = chainLast s := by
    rw [chainLast_extraVertex, hface, collapseVertices_succ_of_le n k _ hs]
    rfl
  by_cases he : chainLast s = ordinalVertex n k
  · have hinput : chainLast (s.map (faceVertices n i)) = ordinalVertex (n + 1) k.succ := by
      rw [hface, he]; rfl
    rw [extraVertex_eq_initialFlag_of_last_inserted n k _ hinput,
      partialLastVertex_initialFlag, he]
  · rw [partialLastVertex_apply, hlast, ite_eq_right (fun h => he (le_antisymm h hs))]

lemma extraVertex_lowFace_partialLastVertex (n : ℕ) (j k : Fin (n + 1))
    (hjk : j.val + 1 = k.val) (i : Fin (n + 2)) (hik : i ≤ k.castSucc)
    (s : OrdinalChains.{u} n) :
    partialLastVertex n (ordinalVertex n k)
      (extraVertex n k ((partialLastVertex n (ordinalVertex n j) s).map (faceVertices n i))) =
    partialLastVertex n (ordinalVertex n k) (extraVertex n k (s.map (faceVertices n i))) := by
  rw [partialLastVertex_apply n (ordinalVertex n j)]
  split_ifs with h
  · rfl
  · have hs : ordinalVertex n k ≤ chainLast s := by
      change k.val ≤ (chainLast s).down.val
      have hh : ¬ (chainLast s).down.val ≤ j.val := h
      omega
    rw [extraVertex_lowFace_saturated n k i hik s hs,
      extraVertex_lowFace_saturated n k i hik (initialFlag ⦋n⦌ (chainLast s))
        (by rw [chainLast_initialFlag]; exact hs), chainLast_initialFlag]

lemma extraVertexMap_lowFace_partialLastMap (n : ℕ) (j k : Fin (n + 1))
    (hjk : j.val + 1 = k.val) (i : Fin (n + 2)) (hik : i ≤ k.castSucc) :
    partialLastMap n (ordinalVertex n j) ≫ SimplexCategory.sd.map (SimplexCategory.δ i) ≫
      extraVertexMap.{u} n k ≫ partialLastMap n (ordinalVertex n k) =
    SimplexCategory.sd.map (SimplexCategory.δ i) ≫ extraVertexMap n k ≫
      partialLastMap n (ordinalVertex n k) := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ ≫
    PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ =
    PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  repeat' erw [← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_lowFace_partialLastVertex n j k hjk i hik s

lemma exPairSimplex_lowFace_level (X : SSet.{u}) (n : ℕ) (j k : Fin (n + 1))
    (hjk : j.val + 1 = k.val) (i : Fin (n + 2)) (hik : i ≤ k.castSucc)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hx : ExLevel X n (ordinalVertex n k) x) :
    ExLevel X n (ordinalVertex n j) ((SSet.ex.obj X).δ i (exPairSimplex X n k x)) := by
  change partialLastMap n (ordinalVertex n j) ≫
    (SimplexCategory.sd.map (SimplexCategory.δ i) ≫ (extraVertexMap n k ≫ x.down)) =
    SimplexCategory.sd.map (SimplexCategory.δ i) ≫ (extraVertexMap n k ≫ x.down)
  have he := congrArg (· ≫ x.down) (extraVertexMap_lowFace_partialLastMap n j k hjk i hik)
  change partialLastMap n (ordinalVertex n k) ≫ x.down = x.down at hx
  simpa only [Category.assoc, hx] using he

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

local instance subdivisionPairingAbsorptionLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma partialLastVertex_map_absorb (n m : ℕ) (j : OrdinalVertices.{u} n)
    (k : OrdinalVertices.{u} m) (f : OrdinalVertices.{u} n →o OrdinalVertices.{u} m)
    (hf : ∀ a, j < a → k < f a) (s : OrdinalChains.{u} n) :
    partialLastVertex m k ((partialLastVertex n j s).map f) =
      partialLastVertex m k (s.map f) := by
  rw [partialLastVertex_apply n j]
  split_ifs with h
  · rfl
  · have hh := hf (chainLast s) (lt_of_not_ge h)
    rw [partialLastVertex_apply, partialLastVertex_apply, chainLast_map,
      chainLast_map, chainLast_initialFlag, ite_eq_right hh.not_ge, ite_eq_right hh.not_ge]

lemma partialLastMap_sd_absorb {n m : ℕ} (j : OrdinalVertices.{u} n)
    (k : OrdinalVertices.{u} m) (f : ⦋n⦌ ⟶ ⦋m⦌)
    (hf : ∀ a, j < a → k < (SimplexCategory.toPartOrd.map f).hom a) :
    partialLastMap n j ≫ SimplexCategory.sd.map f ≫ partialLastMap m k =
      SimplexCategory.sd.map f ≫ partialLastMap m k := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ ≫
    PartOrd.nerveFunctor.map _ = PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  repeat' erw [← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact partialLastVertex_map_absorb n m j k _ hf s

lemma exLevel_map_of {X : SSet.{u}} {n m : ℕ} (j : OrdinalVertices.{u} n)
    (k : OrdinalVertices.{u} m) (f : ⦋n⦌ ⟶ ⦋m⦌)
    (hf : ∀ a, j < a → k < (SimplexCategory.toPartOrd.map f).hom a)
    (x : (SSet.ex.obj X).obj (op ⦋m⦌)) (hx : ExLevel X m k x) :
    ExLevel X n j ((SSet.ex.obj X).map f.op x) := by
  change partialLastMap _ _ ≫ (SimplexCategory.sd.map f ≫ x.down) = SimplexCategory.sd.map f ≫ x.down
  have he := congrArg (· ≫ x.down) (partialLastMap_sd_absorb j k f hf)
  change partialLastMap m k ≫ x.down = x.down at hx
  simpa only [Category.assoc, hx] using he

lemma exLevel_highFace {X : SSet.{u}} {n : ℕ} (k : Fin (n + 1)) (i : Fin (n + 2))
    (x : (SSet.ex.obj X).obj (op ⦋n + 1⦌))
    (hx : ExLevel X (n + 1) (ordinalVertex (n + 1) k.castSucc) x) :
    ExLevel X n (ordinalVertex n k) ((SSet.ex.obj X).δ i x) := by
  apply exLevel_map_of _ _ (SimplexCategory.δ i) _ x hx
  intro a ha
  change k.castSucc < i.succAbove a.down
  unfold Fin.succAbove
  split_ifs
  · exact ha
  · exact (show k.castSucc < a.down.castSucc from ha).trans_le a.down.castSucc_le_succ

lemma exLevel_lowFace {X : SSet.{u}} {n : ℕ} (j : Fin (n + 1)) (i : Fin (n + 2))
    (hi : i ≤ j.succ) (x : (SSet.ex.obj X).obj (op ⦋n + 1⦌))
    (hx : ExLevel X (n + 1) (ordinalVertex (n + 1) j.succ) x) :
    ExLevel X n (ordinalVertex n j) ((SSet.ex.obj X).δ i x) := by
  apply exLevel_map_of _ _ (SimplexCategory.δ i) _ x hx
  intro a ha
  change j.succ < i.succAbove a.down
  rw [Fin.succAbove_of_le_castSucc _ _ (hi.trans (show j.succ ≤ a.down.castSucc from ha))]
  exact Fin.succ_lt_succ_iff.mpr ha

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma extraVertexMap_highFace (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hki : k.castSucc < i) :
    SimplexCategory.sd.map (SimplexCategory.δ i.succ) ≫ extraVertexMap.{u} (n + 1) k.castSucc =
    extraVertexMap n k ≫ SimplexCategory.sd.map (SimplexCategory.δ i) := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ =
      PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_highFace n k i hki s

lemma exPairSimplex_highFace (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hki : k.castSucc < i) (x : (SSet.ex.obj X).obj (op ⦋n + 1⦌)) :
    (SSet.ex.obj X).δ i.succ (exPairSimplex X (n + 1) k.castSucc x) =
      exPairSimplex X n k ((SSet.ex.obj X).δ i x) := by
  apply ULift.ext
  change SimplexCategory.sd.map (SimplexCategory.δ i.succ) ≫ (extraVertexMap (n + 1) k.castSucc ≫ x.down) =
    extraVertexMap n k ≫ (SimplexCategory.sd.map (SimplexCategory.δ i) ≫ x.down)
  erw [← Category.assoc, extraVertexMap_highFace n k i hki, Category.assoc]

lemma chainUnionMap_comp {A B C : Type*} [PartialOrder A] [LinearOrder B] [LinearOrder C]
    (f : B → NonemptyFiniteChains C) (g : A → NonemptyFiniteChains B)
    (s : NonemptyFiniteChains A) :
    chainUnionMap f (chainUnionMap g s) = chainUnionMap (fun a => chainUnionMap f (g a)) s := by
  apply NonemptyFiniteChains.ext
  ext c
  simp only [mem_chainUnionMap]
  exact ⟨fun ⟨b, ⟨a, ha, hb⟩, hc⟩ => ⟨a, ha, b, hb, hc⟩,
    fun ⟨a, ha, b, hb, hc⟩ => ⟨b, ⟨a, ha, hb⟩, hc⟩⟩

lemma chainUnionMap_on_singleton {A B : Type*} [PartialOrder A] [LinearOrder B]
    (f : A → NonemptyFiniteChains B) (a : A) : chainUnionMap f (singletonChain a) = f a := by
  apply NonemptyFiniteChains.ext
  ext b
  simp only [mem_chainUnionMap, mem_singletonChain]
  exact ⟨fun ⟨a', ha, hb⟩ => ha ▸ hb, fun hb => ⟨a, rfl, hb⟩⟩

local instance subdivisionPairingChainUnionLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma predAbove_castSucc_eq_succ {n : ℕ} (k : Fin (n + 1)) (a : Fin (n + 3))
    (ha : a ≠ k.castSucc.succ) : k.castSucc.predAbove a = k.succ.predAbove a := by
  apply Fin.ext
  unfold Fin.predAbove
  split_ifs with h1 h2 h3
  · rfl
  · have hv : a.val = k.val + 1 := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h2
      omega
    exact (ha (Fin.ext hv)).elim
  · have : False := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h3
      omega
    exact this.elim
  · rfl

lemma extraVertexFace_twice (n : ℕ) (k : Fin (n + 1)) (a : OrdinalVertices.{u} (n + 2)) :
    extraVertex n k (extraVertexFace (n + 1) k.castSucc a) =
      extraVertexFace n k (collapseVertices (n + 1) k.succ a) := by
  classical
  by_cases ha : a.down = k.castSucc.succ
  · have hleft : extraVertexFace (n + 1) k.castSucc a =
        initialFlag ⦋n + 1⦌ (ordinalVertex (n + 1) k.castSucc) := ite_eq_left ha
    rw [hleft, extraVertex_initialFlag]
    have hcl : collapseVertices n k (ordinalVertex (n + 1) k.castSucc) = ordinalVertex n k := by
      change ordinalVertex n (k.predAbove k.castSucc) = _
      rw [Fin.predAbove_castSucc_self]
    have hcr : collapseVertices (n + 1) k.succ a = ordinalVertex (n + 1) k.succ := by
      change ordinalVertex (n + 1) (k.succ.predAbove a.down) = _
      rw [ha]
      change ordinalVertex (n + 1) (k.succ.predAbove k.succ.castSucc) = _
      rw [Fin.predAbove_castSucc_self]
    rw [hcl, hcr]
    exact (ite_eq_left rfl).symm
  · have hh : extraVertexFace (n + 1) k.castSucc a =
        singletonChain (collapseVertices (n + 1) k.castSucc a) := ite_eq_right ha
    rw [hh]
    change chainUnionMap _ (singletonChain _) = _
    rw [chainUnionMap_on_singleton]
    congr 1
    exact ULift.ext _ _ (predAbove_castSucc_eq_succ k a.down ha)

lemma extraVertex_twice (n : ℕ) (k : Fin (n + 1)) (s : OrdinalChains.{u} (n + 2)) :
    extraVertex n k (extraVertex (n + 1) k.castSucc s) =
      extraVertex n k (s.map (collapseVertices (n + 1) k.succ)) := by
  change chainUnionMap _ (chainUnionMap _ _) = chainUnionMap _ _
  rw [chainUnionMap_comp, chainUnionMap_map]
  congr 2
  funext a
  exact extraVertexFace_twice n k a

lemma extraVertexMap_twice (n : ℕ) (k : Fin (n + 1)) :
    extraVertexMap.{u} (n + 1) k.castSucc ≫ extraVertexMap n k =
      SimplexCategory.sd.map (SimplexCategory.σ k.succ) ≫ extraVertexMap n k := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ =
      PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_twice n k s

lemma exPairSimplex_twice (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    exPairSimplex X (n + 1) k.castSucc (exPairSimplex X n k x) =
      (SSet.ex.obj X).σ k.succ (exPairSimplex X n k x) := by
  apply ULift.ext
  change extraVertexMap (n + 1) k.castSucc ≫ (extraVertexMap n k ≫ x.down) =
    SimplexCategory.sd.map (SimplexCategory.σ k.succ) ≫ (extraVertexMap n k ≫ x.down)
  erw [← Category.assoc, extraVertexMap_twice, Category.assoc]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

local instance subdivisionPairingCollapseLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma collapseVertices_face (n : ℕ) (i : Fin (n + 1)) (a : OrdinalVertices.{u} n) :
    collapseVertices n i (faceVertices n i.succ a) = a :=
  ULift.ext _ _ (predAbove_succ_succAbove i a.down)

lemma initialFlag_map_collapseVertices (n : ℕ) (i : Fin (n + 1))
    (a : OrdinalVertices.{u} (n + 1)) :
    (initialFlag ⦋n + 1⦌ a).map (collapseVertices n i) =
      initialFlag ⦋n⦌ (collapseVertices n i a) := by
  apply NonemptyFiniteChains.ext
  ext b
  rw [NonemptyFiniteChains.mem_map_iff, mem_initialFlag]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (collapseVertices n i).monotone ((mem_initialFlag _ _ _).mp hc)
  · intro hb
    refine ⟨faceVertices n i.succ b, (mem_initialFlag _ _ _).mpr ?_, collapseVertices_face n i b⟩
    exact ((faceVertices n i.succ).monotone hb).trans (face_collapse_le n i a)

lemma predAbove_eq_succ_low_iff {n : ℕ} (i k : Fin (n + 1)) (hik : i ≤ k)
    (a : Fin (n + 3)) : i.castSucc.predAbove a = k.succ ↔ a = k.succ.succ := by
  constructor
  · intro h
    apply Fin.ext
    have hh := congrArg Fin.val h
    unfold Fin.predAbove at hh
    split_ifs at hh with he
    · simp only [Fin.val_pred, Fin.val_succ] at hh
      have ha := a.isLt
      have hi := i.isLt
      have hhik : i.val ≤ k.val := hik
      simp only [Fin.lt_def, Fin.val_castSucc] at he
      change a.val = k.val + 1 + 1
      omega
    · simp only [Fin.coe_castPred, Fin.val_succ] at hh
      have hhik : i.val ≤ k.val := hik
      simp only [Fin.lt_def, Fin.val_castSucc] at he
      omega
  · intro h
    rw [h, Fin.predAbove_of_castSucc_lt, Fin.pred_succ]
    exact Fin.castSucc_lt_succ_iff.mpr (show i.castSucc ≤ k.succ from (show i.castSucc ≤ k.castSucc from hik).trans k.castSucc_le_succ)

lemma predAbove_eq_succ_high_iff {n : ℕ} (i k : Fin (n + 1)) (hki : k < i)
    (a : Fin (n + 3)) : i.succ.predAbove a = k.succ ↔ a = k.castSucc.succ := by
  constructor
  · intro h
    apply Fin.ext
    have hh := congrArg Fin.val h
    unfold Fin.predAbove at hh
    split_ifs at hh with he
    · simp only [Fin.val_pred, Fin.val_succ] at hh
      have hki' : k.val < i.val := hki
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at he
      change a.val = k.val + 1
      omega
    · simpa only [Fin.coe_castPred, Fin.val_succ, Fin.val_castSucc] using hh
  · intro h
    rw [h]
    change i.succ.predAbove k.succ.castSucc = k.succ
    exact Fin.predAbove_castSucc_of_le _ _ (Fin.succ_le_succ_iff.mpr hki.le)

lemma extraVertexFace_lowDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hik : i ≤ k)
    (a : OrdinalVertices.{u} (n + 2)) :
    (extraVertexFace (n + 1) k.succ a).map (collapseVertices n i) =
      extraVertexFace n k (collapseVertices (n + 1) i.castSucc a) := by
  classical
  by_cases ha : a.down = k.succ.succ
  · have hl : extraVertexFace (n + 1) k.succ a =
        initialFlag ⦋n + 1⦌ (ordinalVertex (n + 1) k.succ) := ite_eq_left ha
    have hr : extraVertexFace n k (collapseVertices (n + 1) i.castSucc a) =
        initialFlag ⦋n⦌ (ordinalVertex n k) :=
      ite_eq_left ((predAbove_eq_succ_low_iff i k hik a.down).mpr ha)
    rw [hl, hr, initialFlag_map_collapseVertices, collapseVertices_succ_of_le n i k hik]
  · have hb := (predAbove_eq_succ_low_iff i k hik a.down).not.mpr ha
    unfold extraVertexFace
    erw [ite_eq_right ha, ite_eq_right hb, map_singletonChain]
    congr 1
    have h := congrArg (fun f : ⦋n + 2⦌ ⟶ ⦋n⦌ => f.toOrderHom a.down)
      (SimplexCategory.σ_comp_σ hik)
    exact ULift.ext _ _ h.symm

lemma extraVertexFace_highDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hki : k < i)
    (a : OrdinalVertices.{u} (n + 2)) :
    (extraVertexFace (n + 1) k.castSucc a).map (collapseVertices n i) =
      extraVertexFace n k (collapseVertices (n + 1) i.succ a) := by
  classical
  by_cases ha : a.down = k.castSucc.succ
  · have hl : extraVertexFace (n + 1) k.castSucc a =
        initialFlag ⦋n + 1⦌ (ordinalVertex (n + 1) k.castSucc) := ite_eq_left ha
    have hr : extraVertexFace n k (collapseVertices (n + 1) i.succ a) =
        initialFlag ⦋n⦌ (ordinalVertex n k) :=
      ite_eq_left ((predAbove_eq_succ_high_iff i k hki a.down).mpr ha)
    rw [hl, hr, initialFlag_map_collapseVertices]
    congr 1
    change ordinalVertex n (i.predAbove k.castSucc) = _
    rw [Fin.predAbove_castSucc_of_le _ _ hki.le]
  · have hb := (predAbove_eq_succ_high_iff i k hki a.down).not.mpr ha
    unfold extraVertexFace
    erw [ite_eq_right ha, ite_eq_right hb, map_singletonChain]
    congr 1
    have h := congrArg (fun f : ⦋n + 2⦌ ⟶ ⦋n⦌ => f.toOrderHom a.down)
      (SimplexCategory.σ_comp_σ hki.le)
    exact ULift.ext _ _ h

lemma extraVertex_lowDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hik : i ≤ k)
    (s : OrdinalChains.{u} (n + 2)) :
    (extraVertex (n + 1) k.succ s).map (collapseVertices n i) =
      extraVertex n k (s.map (collapseVertices (n + 1) i.castSucc)) := by
  change (chainUnionMap _ _).map _ = chainUnionMap _ _
  rw [map_chainUnionMap, chainUnionMap_map]
  congr 2
  funext a
  exact extraVertexFace_lowDegeneracy n i k hik a

lemma extraVertex_highDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hki : k < i)
    (s : OrdinalChains.{u} (n + 2)) :
    (extraVertex (n + 1) k.castSucc s).map (collapseVertices n i) =
      extraVertex n k (s.map (collapseVertices (n + 1) i.succ)) := by
  change (chainUnionMap _ _).map _ = chainUnionMap _ _
  rw [map_chainUnionMap, chainUnionMap_map]
  congr 2
  funext a
  exact extraVertexFace_highDegeneracy n i k hki a

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma exLevel_exists_nat (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ∃ k : ℕ, ∃ h : k < n + 1, ExLevel X n (ordinalVertex n ⟨k, h⟩) x :=
  ⟨n, Nat.lt_succ_self n, exLevel_top X n x⟩

noncomputable def exIndex (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) : Fin (n + 1) := by
  classical
  exact ⟨Nat.find (exLevel_exists_nat X n x), (Nat.find_spec (exLevel_exists_nat X n x)).choose⟩

lemma exIndex_level (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ExLevel X n (ordinalVertex n (exIndex X n x)) x := by
  classical
  exact (Nat.find_spec (exLevel_exists_nat X n x)).choose_spec

lemma exIndex_le_iff (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (k : Fin (n + 1)) :
    exIndex X n x ≤ k ↔ ExLevel X n (ordinalVertex n k) x := by
  classical
  constructor
  · intro h
    exact (exIndex_level X n x).mono h
  · intro h
    exact Nat.find_min' (exLevel_exists_nat X n x) ⟨k.isLt, h⟩

lemma exIndex_zero_iff (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    exIndex X n x = 0 ↔ x ∈ Set.range ((exComparison.app X).app (op ⦋n⦌)) := by
  rw [← exLevel_zero_iff, ← exIndex_le_iff]
  exact ⟨fun h => h.le, fun h => le_antisymm h (Fin.zero_le _)⟩

lemma exIndex_pair (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hx : ExLevel X n (ordinalVertex n k) x) :
    exIndex X (n + 1) (exPairSimplex X n k x) = (exIndex X n x).castSucc := by
  have hxk := (exIndex_le_iff X n x k).mpr hx
  have hk : exIndex X (n + 1) (exPairSimplex X n k x) ≤ k.castSucc :=
    (exIndex_le_iff _ _ _ _).mpr ((exPairSimplex_level_iff X n k k le_rfl x).mpr hx)
  let l : Fin (n + 1) := ⟨(exIndex X (n + 1) (exPairSimplex X n k x)).val,
    lt_of_le_of_lt hk k.isLt⟩
  have hl : exIndex X (n + 1) (exPairSimplex X n k x) = l.castSucc := Fin.ext rfl
  apply Fin.ext
  apply le_antisymm
  · exact (exIndex_le_iff _ _ _ _).mpr
      ((exPairSimplex_level_iff X n (exIndex X n x) k hxk x).mpr (exIndex_level X n x))
  · have hlev : ExLevel X (n + 1) (ordinalVertex (n + 1) l.castSucc) (exPairSimplex X n k x) := by
      rw [← hl]
      exact exIndex_level _ _ _
    exact (exIndex_le_iff X n x l).mpr
      ((exPairSimplex_level_iff X n l k (show l ≤ k from hk) x).mp hlev)

def ExTypeI (X : SSet.{u}) : (n : ℕ) → (SSet.ex.obj X).obj (op ⦋n⦌) → Prop := fun n => match n with
  | 0 => fun _ => False
  | n + 1 => fun x => ∃ k : Fin (n + 1), ∃ y : (SSet.ex.obj X).obj (op ⦋n⦌),
      exIndex X (n + 1) x = k.castSucc ∧ exPairSimplex X n k y = x

def ExTypeII (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) : Prop :=
  x ∈ (SSet.ex.obj X).nonDegenerate n ∧ 0 < (exIndex X n x).val ∧ ¬ ExTypeI X n x

lemma exPairSimplex_typeI (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ExTypeI X (n + 1) (exPairSimplex X n (exIndex X n x) x) :=
  ⟨exIndex X n x, x, exIndex_pair X n _ x (exIndex_level X n x), rfl⟩

lemma exTypeI_preimage_index (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌))
    (h : exIndex X (n + 1) (exPairSimplex X n k x) = k.castSucc) :
    exIndex X n x = k := by
  have hx : ExLevel X n (ordinalVertex n k) x := by
    apply (exPairSimplex_level_iff X n k k le_rfl x).mp
    rw [← h]
    exact exIndex_level _ _ _
  have he := (exIndex_pair X n k x hx).symm.trans h
  exact Fin.ext (congrArg (fun t : Fin (n + 2) => t.val) he)

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ExtensionAnodyne
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension Anodyne. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma nonDegenerate_of_unique_face {X : SSet.{u}} {n : ℕ}
    (x : X.obj (op ⦋n⦌)) (hx : x ∈ X.nonDegenerate n)
    (y : X.obj (op ⦋n + 1⦌)) (j : Fin (n + 2)) (hj : X.δ j y = x)
    (hunique : ∀ i : Fin (n + 2), X.δ i y = x → i = j) :
    y ∈ X.nonDegenerate (n + 1) := by
  by_contra hy
  rw [← X.mem_degenerate_iff_notMem_nonDegenerate,
    X.degenerate_eq_iUnion_range_σ] at hy
  simp only [Set.mem_iUnion, Set.mem_range] at hy
  obtain ⟨i, z, rfl⟩ := hy
  have hm : X.map (SimplexCategory.δ j ≫ SimplexCategory.σ i).op z = x := by
    rw [op_comp, CategoryTheory.Functor.map_comp]
    exact hj
  have : Mono (SimplexCategory.δ j ≫ SimplexCategory.σ i) :=
    X.mono_of_nonDegenerate ⟨x, hx⟩ _ z hm
  have he : z = x := by
    rw [SimplexCategory.eq_id_of_mono (SimplexCategory.δ j ≫ SimplexCategory.σ i), op_id, CategoryTheory.Functor.map_id] at hm
    exact hm
  have h1 : X.δ i.castSucc (X.σ i z) = x := by
    rw [← CategoryTheory.comp_apply, SimplicialObject.δ_comp_σ_self]
    exact he
  have h2 : X.δ i.succ (X.σ i z) = x := by
    rw [← CategoryTheory.comp_apply, SimplicialObject.δ_comp_σ_succ]
    exact he
  have hh := (hunique i.castSucc h1).trans (hunique i.succ h2).symm
  exact (Fin.ne_of_lt i.castSucc_lt_succ) hh

lemma exPairSimplex_face_unique (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hk : exIndex X n x = k)
    (hpos : 0 < k.val) (hI : ¬ ExTypeI X n x) (i : Fin (n + 2))
    (hi : (SSet.ex.obj X).δ i (exPairSimplex X n k x) = x) : i = k.succ := by
  have hx : ExLevel X n (ordinalVertex n k) x := hk ▸ exIndex_level X n x
  by_cases hil : i ≤ k.castSucc
  · let j : Fin (n + 1) := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    have hjk : j.val + 1 = k.val := by dsimp [j]; omega
    have hlev := exPairSimplex_lowFace_level X n j k hjk i hil x hx
    rw [hi] at hlev
    have hh := (exIndex_le_iff X n x j).mpr hlev
    rw [hk] at hh
    have hval : k.val ≤ j.val := hh
    omega
  · by_contra hine
    have hgt : k.succ < i := by
      have h1 : k.val < i.val := lt_of_not_ge hil
      have h2 : i.val ≠ k.val + 1 := fun h => hine (Fin.ext h)
      change k.val + 1 < i.val
      omega
    cases n with
    | zero => have hk0 := k.isLt; omega
    | succ n =>
      cases k using Fin.lastCases with
      | last => have hi0 := i.isLt; have hgt0 : n + 2 < i.val := hgt; omega
      | cast k =>
        cases i using Fin.cases with
        | zero => exact (not_lt_of_ge (Fin.zero_le _) hgt).elim
        | succ i =>
          have hki : k.castSucc < i := by
            change k.val < i.val
            change k.val + 1 < i.val + 1 at hgt
            omega
          have he := exPairSimplex_highFace X n k i hki x
          apply hI
          exact ⟨k, (SSet.ex.obj X).δ i x, hk, he.symm.trans hi⟩

lemma exPairSimplex_nonDegenerate (X : SSet.{u}) (n : ℕ)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hx : ExTypeII X n x) :
    exPairSimplex X n (exIndex X n x) x ∈ (SSet.ex.obj X).nonDegenerate (n + 1) :=
  nonDegenerate_of_unique_face x hx.1 _ _ (exPairSimplex_face X n _ x)
    (exPairSimplex_face_unique X n _ x rfl hx.2.1 hx.2.2)

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma extraVertexMap_lowDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hik : i ≤ k) :
    extraVertexMap.{u} (n + 1) k.succ ≫ SimplexCategory.sd.map (SimplexCategory.σ i) =
      SimplexCategory.sd.map (SimplexCategory.σ i.castSucc) ≫ extraVertexMap n k := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ =
    PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_lowDegeneracy n i k hik s

lemma extraVertexMap_highDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hki : k < i) :
    extraVertexMap.{u} (n + 1) k.castSucc ≫ SimplexCategory.sd.map (SimplexCategory.σ i) =
      SimplexCategory.sd.map (SimplexCategory.σ i.succ) ≫ extraVertexMap n k := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ =
    PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_highDegeneracy n i k hki s

lemma exPairSimplex_lowDegeneracy (X : SSet.{u}) (n : ℕ) (i k : Fin (n + 1)) (hik : i ≤ k)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    exPairSimplex X (n + 1) k.succ ((SSet.ex.obj X).σ i x) =
      (SSet.ex.obj X).σ i.castSucc (exPairSimplex X n k x) := by
  apply ULift.ext
  change extraVertexMap (n + 1) k.succ ≫ (SimplexCategory.sd.map (SimplexCategory.σ i) ≫ x.down) =
    SimplexCategory.sd.map (SimplexCategory.σ i.castSucc) ≫ (extraVertexMap n k ≫ x.down)
  erw [← Category.assoc, extraVertexMap_lowDegeneracy n i k hik, Category.assoc]

lemma exPairSimplex_highDegeneracy (X : SSet.{u}) (n : ℕ) (i k : Fin (n + 1)) (hki : k < i)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    exPairSimplex X (n + 1) k.castSucc ((SSet.ex.obj X).σ i x) =
      (SSet.ex.obj X).σ i.succ (exPairSimplex X n k x) := by
  apply ULift.ext
  change extraVertexMap (n + 1) k.castSucc ≫ (SimplexCategory.sd.map (SimplexCategory.σ i) ≫ x.down) =
    SimplexCategory.sd.map (SimplexCategory.σ i.succ) ≫ (extraVertexMap n k ≫ x.down)
  erw [← Category.assoc, extraVertexMap_highDegeneracy n i k hki, Category.assoc]

lemma exLevel_highDegeneracy {X : SSet.{u}} {n : ℕ} (i k : Fin (n + 1)) (hki : k < i)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hx : ExLevel X n (ordinalVertex n k) x) :
    ExLevel X (n + 1) (ordinalVertex (n + 1) k.castSucc) ((SSet.ex.obj X).σ i x) := by
  apply exLevel_map_of _ _ (SimplexCategory.σ i) _ x hx
  intro a ha
  change k < i.predAbove a.down
  unfold Fin.predAbove
  split_ifs with h
  · change k.val < a.down.val - 1
    have h1 : k.val < i.val := hki
    have h2 : i.val < a.down.val := h
    omega
  · exact ha

lemma exIndex_degeneracy_ne_self (X : SSet.{u}) (n : ℕ) (i : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hpos : 0 < i.val) :
    exIndex X (n + 1) ((SSet.ex.obj X).σ i x) ≠ i.castSucc := by
  intro he
  let j : Fin (n + 1) := ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  have hji : j.succ = i.castSucc := Fin.ext (by dsimp [j]; omega)
  have hx : ExLevel X n (ordinalVertex n j) x := by
    have h := exLevel_lowFace j i.castSucc (by rw [hji]) ((SSet.ex.obj X).σ i x)
      (by rw [hji, ← he]; exact exIndex_level _ _ _)
    have hh : (SSet.ex.obj X).δ i.castSucc ((SSet.ex.obj X).σ i x) = x := by
      rw [← CategoryTheory.comp_apply, SimplicialObject.δ_comp_σ_self]
      rfl
    rwa [hh] at h
  have hji' : j < i := by change i.val - 1 < i.val; omega
  have hlev := exLevel_highDegeneracy i j hji' x hx
  have hh := (exIndex_le_iff _ _ _ _).mpr hlev
  rw [he] at hh
  have hh' : i.val ≤ j.val := hh
  have hj' : j.val < i.val := hji'
  omega

lemma exPairSimplex_reflects_nonDegenerate (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hk : exIndex X n x = k) (hp : 0 < k.val)
    (hx : exPairSimplex X n k x ∈ (SSet.ex.obj X).nonDegenerate (n + 1)) :
    x ∈ (SSet.ex.obj X).nonDegenerate n := by
  cases n with
  | zero => simp
  | succ n =>
    by_contra hdeg
    rw [← (SSet.ex.obj X).mem_degenerate_iff_notMem_nonDegenerate,
      (SSet.ex.obj X).degenerate_eq_iUnion_range_σ] at hdeg
    simp only [Set.mem_iUnion, Set.mem_range] at hdeg
    obtain ⟨i, y, rfl⟩ := hdeg
    by_cases hik : i.val < k.val
    · let j : Fin (n + 1) := ⟨k.val - 1, by have := k.isLt; omega⟩
      have hj : j.succ = k := Fin.ext (by dsimp [j]; omega)
      have hij : i ≤ j := by change i.val ≤ k.val - 1; omega
      rw [← hj, exPairSimplex_lowDegeneracy X n i j hij y] at hx
      exact hx ((SSet.ex.obj X).σ_mem_degenerate _ _)
    · have hki : k.val ≤ i.val := Nat.le_of_not_gt hik
      let j : Fin (n + 1) := ⟨k.val, lt_of_le_of_lt hki i.isLt⟩
      have hj : j.castSucc = k := Fin.ext rfl
      rcases lt_or_eq_of_le hki with hjlt | hjeq
      · rw [← hj, exPairSimplex_highDegeneracy X n i j hjlt y] at hx
        exact hx ((SSet.ex.obj X).σ_mem_degenerate _ _)
      · have hk' : k = i.castSucc := Fin.ext hjeq
        exact exIndex_degeneracy_ne_self X n i y (by rw [← hjeq]; exact hp) (hk.trans hk')

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma exPairSimplex_input_not_typeI (X : SSet.{u}) (n : ℕ)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌))
    (hx : exPairSimplex X n (exIndex X n x) x ∈ (SSet.ex.obj X).nonDegenerate (n + 1)) :
    ¬ ExTypeI X n x := by
  cases n with
  | zero => exact not_false
  | succ n =>
    rintro ⟨k, y, hk, rfl⟩
    rw [hk, exPairSimplex_twice] at hx
    exact hx ((SSet.ex.obj X).σ_mem_degenerate _ _)

lemma exTypeI_preimage_typeII (X : SSet.{u}) (n : ℕ)
    (x : (SSet.ex.obj X).obj (op ⦋n + 1⦌))
    (hx : x ∈ (SSet.ex.obj X).nonDegenerate (n + 1))
    (hp : 0 < (exIndex X (n + 1) x).val) (hI : ExTypeI X (n + 1) x) :
    ∃ y : (SSet.ex.obj X).obj (op ⦋n⦌), ExTypeII X n y ∧
      exPairSimplex X n (exIndex X n y) y = x := by
  obtain ⟨k, y, hk, rfl⟩ := hI
  have hyk := exTypeI_preimage_index X n k y hk
  have hpk : 0 < k.val := by simpa only [hk, Fin.val_castSucc] using hp
  refine ⟨y, ⟨exPairSimplex_reflects_nonDegenerate X n k y hyk hpk hx, ?_, ?_⟩, ?_⟩
  · rwa [hyk]
  · apply exPairSimplex_input_not_typeI
    rwa [hyk]
  · rw [hyk]

lemma exPairSimplex_injective (X : SSet.{u}) (n : ℕ)
    (x y : (SSet.ex.obj X).obj (op ⦋n⦌))
    (h : exPairSimplex X n (exIndex X n x) x =
      exPairSimplex X n (exIndex X n y) y) : x = y := by
  have hk : exIndex X n x = exIndex X n y := by
    have he := congrArg (exIndex X (n + 1)) h
    rw [exIndex_pair _ _ _ _ (exIndex_level _ _ _),
      exIndex_pair _ _ _ _ (exIndex_level _ _ _)] at he
    exact Fin.ext (congrArg (fun t : Fin (n + 2) => t.val) he)
  have he := congrArg (fun z => (SSet.ex.obj X).δ (exIndex X n x).succ z) h
  rw [exPairSimplex_face, hk, exPairSimplex_face] at he
  exact he

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

abbrev ExPairIndices (X : SSet.{u}) := Σ n : ℕ, {x : (SSet.ex.obj X).obj (op ⦋n⦌) // ExTypeII X n x}

lemma exIndex_pos_of_notMem (X : SSet.{u}) (n : ℕ)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌))
    (hx : x ∉ (SSet.Subcomplex.range (exComparison.app X)).obj (op ⦋n⦌)) :
    0 < (exIndex X n x).val := by
  apply Nat.pos_of_ne_zero
  intro h
  have he : exIndex X n x = 0 := Fin.ext h
  exact hx ((exIndex_zero_iff X n x).mp he)

lemma exIndex_notMem_of_pos (X : SSet.{u}) (n : ℕ)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hx : 0 < (exIndex X n x).val) :
    x ∉ (SSet.Subcomplex.range (exComparison.app X)).obj (op ⦋n⦌) := by
  intro h
  have he := (exIndex_zero_iff X n x).mpr h
  simp only [he, Fin.val_zero, lt_self_iff_false] at hx

noncomputable def exPairingCore (X : SSet.{u}) :
    (SSet.Subcomplex.range (exComparison.app X)).PairingCore where
  ι := ExPairIndices X
  dim s := s.1
  simplex s := exPairSimplex X s.1 (exIndex X s.1 s.2.1) s.2.1
  index s := (exIndex X s.1 s.2.1).succ
  nonDegenerate₁ s := exPairSimplex_nonDegenerate X s.1 s.2.1 s.2.2
  nonDegenerate₂ s := by rw [exPairSimplex_face]; exact s.2.2.1
  notMem₁ s := exIndex_notMem_of_pos X _ _ (by
    rw [exIndex_pair _ _ _ _ (exIndex_level _ _ _)]
    exact s.2.2.2.1)
  notMem₂ s := by
    rw [exPairSimplex_face]
    exact exIndex_notMem_of_pos X _ _ s.2.2.2.1
  injective_type₁' {s t} h := by
    obtain ⟨n, ⟨x, hx⟩⟩ := s
    obtain ⟨m, ⟨y, hy⟩⟩ := t
    have hnm : n = m := Nat.add_right_cancel (SSet.S.dim_eq_of_mk_eq h)
    subst m
    have he := exPairSimplex_injective X n x y ((SSet.S.ext_iff _ _).mp h)
    subst y
    rfl
  injective_type₂' {s t} h := by
    simp only [exPairSimplex_face] at h
    obtain ⟨n, ⟨x, hx⟩⟩ := s
    obtain ⟨m, ⟨y, hy⟩⟩ := t
    have hnm : n = m := SSet.S.dim_eq_of_mk_eq h
    subst m
    have he := (SSet.S.ext_iff _ _).mp h
    change x = y at he
    subst y
    rfl
  type₁_ne_type₂' s t h := by
    simp only [exPairSimplex_face] at h
    obtain ⟨n, ⟨x, hx⟩⟩ := s
    obtain ⟨m, ⟨y, hy⟩⟩ := t
    have hnm : n + 1 = m := SSet.S.dim_eq_of_mk_eq h
    subst m
    have he := (SSet.S.ext_iff _ _).mp h
    change exPairSimplex X n (exIndex X n x) x = y at he
    exact hy.2.2 (he ▸ exPairSimplex_typeI X n x)
  surjective' x := by
    obtain ⟨n, x, hnd, hn, rfl⟩ := x.mk_surjective
    have hp := exIndex_pos_of_notMem X n x hn
    by_cases hI : ExTypeI X n x
    · cases n with
      | zero => exact hI.elim
      | succ n =>
        obtain ⟨y, hy, he⟩ := exTypeI_preimage_typeII X n x hnd hp hI
        exact ⟨⟨n, ⟨y, hy⟩⟩, Or.inl (congrArg SSet.S.mk he.symm)⟩
    · refine ⟨⟨n, ⟨x, hnd, hp, hI⟩⟩, Or.inr ?_⟩
      simp only [exPairSimplex_face]
      rfl

instance exPairingCore_isProper (X : SSet.{u}) : (exPairingCore X).IsProper where
  isUniquelyCodimOneFace s := by
    apply (SSet.S.IsUniquelyCodimOneFace.iff _ _).mpr
    change ∃! i, (SSet.ex.obj X).δ i (exPairSimplex X s.1 (exIndex X s.1 s.2.1) s.2.1) =
      (SSet.ex.obj X).δ (exIndex X s.1 s.2.1).succ
        (exPairSimplex X s.1 (exIndex X s.1 s.2.1) s.2.1)
    rw [exPairSimplex_face]
    exact ⟨_, exPairSimplex_face X _ _ _,
      exPairSimplex_face_unique X _ _ _ rfl s.2.2.2.1 s.2.2.2.2⟩

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma exPairSimplex_other_face_index_lt (X : SSet.{u}) (n : ℕ)
    (y x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hy : ExTypeII X n y) (hx : ExTypeII X n x)
    (hxy : x ≠ y) (i : Fin (n + 2))
    (hi : (SSet.ex.obj X).δ i (exPairSimplex X n (exIndex X n y) y) = x) :
    exIndex X n x < exIndex X n y := by
  let k := exIndex X n y
  have hp : 0 < k.val := hy.2.1
  have hlev : ExLevel X n (ordinalVertex n k) y := exIndex_level _ _ _
  by_cases hil : i ≤ k.castSucc
  · let j : Fin (n + 1) := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    have hjk : j.val + 1 = k.val := by dsimp [j]; omega
    have h := exPairSimplex_lowFace_level X n j k hjk i hil y hlev
    rw [hi] at h
    apply lt_of_le_of_lt ((exIndex_le_iff X n x j).mpr h)
    change k.val - 1 < k.val
    omega
  · have hine : i ≠ k.succ := by
      intro he
      rw [he, exPairSimplex_face] at hi
      exact hxy hi.symm
    have hgt : k.succ < i := by
      have h1 : k.val < i.val := lt_of_not_ge hil
      have h2 : i.val ≠ k.val + 1 := fun h => hine (Fin.ext h)
      change k.val + 1 < i.val
      omega
    have hle : exIndex X n x ≤ k := by
      apply (exIndex_le_iff X n x k).mpr
      rw [← hi]
      exact exLevel_highFace k i _ ((exPairSimplex_level_iff X n k k le_rfl y).mpr hlev)
    apply lt_of_le_of_ne hle
    intro he
    cases n with
    | zero => have hk0 := k.isLt; omega
    | succ n =>
      cases hk : k using Fin.lastCases with
      | last =>
        have hgt0 : n + 2 < i.val := by
          rw [hk] at hgt
          exact hgt
        have hi0 := i.isLt
        omega
      | cast j =>
        cases i using Fin.cases with
        | zero => exact (not_lt_of_ge (Fin.zero_le _) hgt).elim
        | succ i =>
          have hji : j.castSucc < i := by
            rw [hk] at hgt
            change j.val + 1 < i.val + 1 at hgt
            change j.val < i.val
            omega
          apply hx.2.2
          refine ⟨j, (SSet.ex.obj X).δ i y, he.trans hk, ?_⟩
          change (SSet.ex.obj X).δ i.succ (exPairSimplex X (n + 1) k y) = x at hi
          rw [hk] at hi
          exact (exPairSimplex_highFace X n j i hji y).symm.trans hi

noncomputable def exPairRank (X : SSet.{u}) (s : ExPairIndices X) : ℕ :=
  s.1 * (s.1 + 1) + (exIndex X s.1 s.2.1).val

lemma exPairRank_decreases (X : SSet.{u}) (s t : ExPairIndices X)
    (h : (exPairingCore X).AncestralRel s t) : exPairRank X s < exPairRank X t := by
  have hd : s.1 < t.1 + 1 := SSet.N.dim_lt_of_lt h.2
  obtain ⟨n, ⟨x, hx⟩⟩ := s
  obtain ⟨m, ⟨y, hy⟩⟩ := t
  change n < m + 1 at hd
  rcases (Nat.lt_succ_iff.mp hd).lt_or_eq with hnm | hnm
  · have hn := (exIndex X n x).isLt
    have hm := (exIndex X m y).isLt
    change n * (n + 1) + (exIndex X n x).val < m * (m + 1) + (exIndex X m y).val
    nlinarith
  · subst m
    have hxy : x ≠ y := by
      intro he
      subst y
      exact h.1 rfl
    have hle := (SSet.N.le_iff_exists_mono).mp h.2.le
    obtain ⟨f, hf, he⟩ := hle
    change ⦋n⦌ ⟶ ⦋n + 1⦌ at f
    have : Mono f := hf
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    change (SSet.ex.obj X).δ i (exPairSimplex X n (exIndex X n y) y) =
      (SSet.ex.obj X).δ (exIndex X n x).succ (exPairSimplex X n (exIndex X n x) x) at he
    rw [exPairSimplex_face] at he
    have hk := exPairSimplex_other_face_index_lt X n y x hy hx hxy i he
    exact Nat.add_lt_add_left hk _

instance exPairingCore_isRegular (X : SSet.{u}) : (exPairingCore X).IsRegular where
  wf := Subrelation.wf (fun {s t} h => exPairRank_decreases X s t h) (measure (exPairRank X)).wf

theorem exComparison_strongAnodyne (X : SSet.{u}) :
    SSet.strongAnodyneExtensions (exComparison.app X) :=
  ⟨inferInstance, (exPairingCore X).pairing, inferInstance⟩

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory

lemma exComparison_anodyne (X : SSet.{u}) : SSet.anodyneExtensions (exComparison.app X) :=
  SSet.strongAnodyneExtensions_le_anodyneExtensions _ (exComparison_strongAnodyne X)

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

def HornFaces (n : ℕ) (k : Fin (n+1)) : Set (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))) :=
  {s | ∃ a : Fin (n+1), a ≠ k ∧ ULift.up a ∉ s.finset}

noncomputable def hornFacePoint {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) : HornFaces.{u} n k := by
  classical
  refine ⟨⟨{ULift.up k}, by simp, by simp⟩, ?_⟩
  have hex : ∃ a : Fin (n+1), a ≠ k := by
    by_cases hk : k = 0
    · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val (h.trans hk); simp at this⟩
    · exact ⟨0, Ne.symm hk⟩
  obtain ⟨a, ha⟩ := hex
  exact ⟨a, ha, by simpa using ha⟩

noncomputable def hornFaceCone {n : ℕ} (k : Fin (n+1)) : HornFaces.{u} n k →o HornFaces.{u} n k where
  toFun s := ⟨⟨insert (ULift.up k) s.val.finset, by simp, by
    intro a b
    exact le_total a.val b.val⟩, by
    obtain ⟨a, hak, ha⟩ := s.property
    exact ⟨a, hak, by simpa using And.intro hak ha⟩⟩
  monotone' s t h := by
    intro a ha
    rcases Finset.mem_insert.mp ha with ha | ha
    · exact Finset.mem_insert.mpr (Or.inl ha)
    · exact Finset.mem_insert.mpr (Or.inr (h ha))

lemma le_hornFaceCone {n : ℕ} (k : Fin (n+1)) (s : HornFaces.{u} n k) :
    s.val ≤ (hornFaceCone k s).val := by
  intro a ha
  exact Finset.mem_insert_of_mem ha

lemma hornFacePoint_le_cone {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) (s : HornFaces.{u} n k) :
    hornFacePoint hn k ≤ hornFaceCone k s := by
  classical
  intro a ha
  have ha' : a = ULift.up k := by
    change a ∈ (hornFacePoint hn k).val.finset at ha
    simpa [hornFacePoint] using ha
  subst a
  exact Finset.mem_insert_self _ _

lemma allowedChains_iff {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)
    (c : NonemptyFiniteChains E) :
    (∃ s : (K : SSet).N, simplexChain (subcomplexN K s).simplex = c) ↔
      (chainSimplex c).simplex ∈ K.obj (op ⦋(chainSimplex c).dim⦌) := by
  constructor
  · rintro ⟨s, hs⟩
    have he : subcomplexN K s = chainSimplex c := by
      apply nerveNondegenerateChains.injective
      change simplexChain _ = simplexChain _
      rw [hs, simplexChain_chainSimplex]
    have hh : (subcomplexN K s).simplex ∈ K.obj (op ⦋(subcomplexN K s).dim⦌) := s.simplex.property
    exact he ▸ hh
  · intro h
    exact ⟨SSet.N.mk ⟨(chainSimplex c).simplex, h⟩
      ((K.mem_nonDegenerate_iff _).mpr (chainSimplex c).nonDegenerate),
      simplexChain_chainSimplex c⟩

lemma orderedSimplexSubcomplex_mem_iff {n d : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋n⦌).Subcomplex)
    (x : (nerve (ULift.{u} (Fin (n+1)))) _⦋d⦌) :
    x ∈ (orderedSimplexSubcomplex K).obj _ ↔
      (SSet.stdSimplex.isoNerve n).inv.app _ x ∈ K.obj _ := by
  constructor
  · rintro ⟨y, rfl⟩
    have he := congrArg (fun f => f.app (op ⦋d⦌) y.val) (SSet.stdSimplex.isoNerve.{u} n).hom_inv_id
    change (SSet.stdSimplex.isoNerve n).inv.app _
      ((SSet.stdSimplex.isoNerve n).hom.app _ y.val) = y.val at he
    change (SSet.stdSimplex.isoNerve n).inv.app _
      ((SSet.stdSimplex.isoNerve n).hom.app _ y.val) ∈ K.obj _
    rw [he]
    exact y.property
  · intro h
    refine ⟨⟨(SSet.stdSimplex.isoNerve n).inv.app _ x, h⟩, ?_⟩
    exact congrArg (fun f => f.app (op ⦋d⦌) x) (SSet.stdSimplex.isoNerve.{u} n).inv_hom_id

lemma hornFaces_allowed_iff {n : ℕ} (k : Fin (n+1))
    (c : NonemptyFiniteChains (ULift.{u} (Fin (n+1)))) :
    (∃ s : (orderedSimplexSubcomplex (SSet.horn n k) : SSet).N,
      simplexChain (subcomplexN _ s).simplex = c) ↔ c ∈ HornFaces n k := by
  rw [allowedChains_iff, orderedSimplexSubcomplex_mem_iff, SSet.mem_horn_iff_notMem_range]
  have hm (a : Fin (n+1)) :
      a ∈ Set.range ((SSet.stdSimplex.isoNerve n).inv.app _ (chainSimplex c).simplex) ↔
        ULift.up a ∈ c.finset := by
    conv_rhs => rw [← simplexChain_chainSimplex c, mem_simplexChain]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply ULift.ext
      exact hi
    · rintro ⟨i, hi⟩
      exact ⟨i, congrArg ULift.down hi⟩
  simp only [HornFaces, Set.mem_ofPred_eq, exists_prop, hm]

noncomputable def hornFacesIso {n : ℕ} (k : Fin (n+1)) :
    AllowedChains (orderedSimplexSubcomplex (SSet.horn.{u} n k)) ≃o HornFaces.{u} n k where
  toFun c := ⟨c.val, (hornFaces_allowed_iff k c.val).mp c.property⟩
  invFun c := ⟨c.val, (hornFaces_allowed_iff k c.val).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionWeak
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Weak. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits Simplicial

noncomputable abbrev exStage (X : SSet.{u}) : ℕ → SSet.{u} :=
  Nat.rec X (fun _ Y => SSet.ex.obj Y)

noncomputable def exSequence (X : SSet.{u}) : ℕ ⥤ SSet.{u} :=
  Functor.ofSequence (X := exStage X) (fun n => exComparison.app (exStage X n))

noncomputable def exInfinity (X : SSet.{u}) : SSet.{u} := colimit (exSequence X)

noncomputable def exInfinityInclusion (X : SSet.{u}) (n : ℕ) :
    exStage X n ⟶ exInfinity X := colimit.ι (exSequence X) n

@[reassoc]
lemma exInfinityInclusion_step (X : SSet.{u}) (n : ℕ) :
    exComparison.app (exStage X n) ≫ exInfinityInclusion X (n+1) =
      exInfinityInclusion X n := by
  have h := colimit.w (exSequence X) (homOfLE (n.le_add_right 1))
  change _ ≫ exInfinityInclusion X (n+1) = exInfinityInclusion X n at h
  erw [Functor.ofSequence_map_homOfLE_succ] at h
  exact h

noncomputable def exInfinityComparison (X : SSet.{u}) : X ⟶ exInfinity X :=
  exInfinityInclusion X 0

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits

noncomputable def exStageMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    ∀ n, exStage X n ⟶ exStage Y n :=
  Nat.rec f (fun _ g => SSet.ex.map g)

@[simp]
lemma exStageMap_id (X : SSet.{u}) (n : ℕ) : exStageMap (𝟙 X) n = 𝟙 (exStage X n) := by
  induction n with
  | zero => rfl
  | succ n ih => change SSet.ex.map (exStageMap (𝟙 X) n) = _; rw [ih]; exact SSet.ex.map_id _

@[simp]
lemma exStageMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    exStageMap (f ≫ g) n = exStageMap f n ≫ exStageMap g n := by
  induction n with
  | zero => rfl
  | succ n ih => change SSet.ex.map (exStageMap (f ≫ g) n) = _; rw [ih, Functor.map_comp]; rfl

noncomputable def exSequenceMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    exSequence X ⟶ exSequence Y := NatTrans.ofSequence (exStageMap f) (by
  intro n
  dsimp only [exSequence]
  erw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
  exact (exComparison.naturality (exStageMap f n)).symm)

noncomputable def exSequenceFunctor : SSet.{u} ⥤ (ℕ ⥤ SSet.{u}) where
  obj := exSequence
  map := exSequenceMap
  map_id X := by apply NatTrans.ext; funext n; exact exStageMap_id X n
  map_comp f g := by apply NatTrans.ext; funext n; exact exStageMap_comp f g n

noncomputable def exInfinityFunctor : SSet.{u} ⥤ SSet.{u} := exSequenceFunctor ⋙ colim

@[reassoc]
lemma exInfinityInclusion_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    exInfinityInclusion X n ≫ exInfinityFunctor.map f =
      exStageMap f n ≫ exInfinityInclusion Y n :=
  ι_colimMap (exSequenceMap f) n

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PartialPrisms
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial Prisms. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OneCat
abbrev Interval := ULift.{u} (Fin 2)
def endpoint (C : Cat.{u,u}) (b : Fin 2) : C ⟶ Cat.of (Interval.{u} × C) :=
  (Prod.sectR (ULift.up b) C).toCatHom
abbrev cylinder : Cat.{u,u} ⥤ Cat.{u,u} := tensorLeft (Cat.of Interval.{u})
def projection (C : Cat.{u,u}) : cylinder.obj C ⟶ C := (CategoryTheory.Prod.snd Interval C).toCatHom
@[reassoc] lemma endpoint_natural {C D : Cat.{u,u}} (f : C ⟶ D) (b : Fin 2) :
    endpoint C b ≫ cylinder.map f = f ≫ endpoint D b := rfl
@[reassoc] lemma projection_natural {C D : Cat.{u,u}} (f : C ⟶ D) :
    cylinder.map f ≫ projection D = projection C ≫ f := rfl
@[simp, reassoc] lemma endpoint_projection (C : Cat.{u,u}) (b : Fin 2) :
    endpoint C b ≫ projection C = 𝟙 C := rfl

end Thomason.OneCat

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SieveAttachments
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sieve Attachments. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OneCat
def liftInterval : Fin 2 →o Interval.{u} where
  toFun := ULift.up
  monotone' _ _ h := h

def cylinderMap {C D : Cat.{u,u}} (H : Cat.of (Interval.{u} × C) ⟶ D) :
    nerve C ⊗ Δ[1] ⟶ nerve D where
  app m := ↾fun x =>
    ((SSet.stdSimplex.objEquiv x.2).toOrderHom.toFunctor ⋙
      liftInterval.toFunctor).prod' x.1 ⋙ H.toFunctor
  naturality m n f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

end Thomason.OneCat

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_HomotopyExtension
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homotopy Extension. -/

noncomputable section
universe u v w z


namespace Thomason.CoherentGluing
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

def toHomotopy {A B : SSet.{u}} {f g : A ⟶ B} (H : A ⊗ Δ[1] ⟶ B)
    (h₀ : SSet.ι₀ ≫ H = f) (h₁ : SSet.ι₁ ≫ H = g) : SSet.Homotopy f g where
  h := H
  h₀ := h₀
  h₁ := h₁
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,hx⟩,θ⟩
    exact False.elim hx

end Thomason.CoherentGluing

end

noncomputable section
universe u v w z


namespace Thomason.HornSubdivision
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

def endpoint (X : SSet.{u}) (j : Fin 2) : X ⟶ X ⊗ Δ[1] :=
  (SimplicialCylinder.zeroFactorIso X).hom ≫ X ◁ SSet.stdSimplex.δ (n := 0) j

@[reassoc] lemma endpoint_natural {A B : SSet.{u}} (f : A ⟶ B) (j : Fin 2) :
    f ≫ endpoint B j = endpoint A j ≫ f ▷ Δ[1] := by
  rfl

lemma endpoint_zero (X : SSet.{u}) : endpoint X 1 = SSet.ι₀ := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro z
    rfl
lemma endpoint_one (X : SSet.{u}) : endpoint X 0 = SSet.ι₁ := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro z
    rfl

lemma cylinder_lift {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i]
    (p : X ⟶ Y) (hp : simplicialFibrations p) (j : Fin 2)
    (l : B ⟶ X) (H : A ⊗ Δ[1] ⟶ X) (K : B ⊗ Δ[1] ⟶ Y)
    (hA : endpoint A j ≫ H = i ≫ l)
    (hB : endpoint B j ≫ K = l ≫ p)
    (hC : H ≫ p = i ▷ Δ[1] ≫ K) :
    ∃ Q : B ⊗ Δ[1] ⟶ X,
      i ▷ Δ[1] ≫ Q = H ∧ endpoint B j ≫ Q = l ∧ Q ≫ p = K := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i
    (SSet.stdSimplex.δ (n := 0) j)
  have hc : i ▷ Δ[0] ≫ (fst B Δ[0] ≫ l) = A ◁ SSet.stdSimplex.δ (n := 0) j ≫ H := by
    apply (cancel_epi (SimplicialCylinder.zeroFactorIso A).hom).mp
    exact hA.symm
  let a : s.pt ⟶ X := s.isPushout.desc (fst B Δ[0] ≫ l) H hc
  have hs : a ≫ p = s.ι ≫ K := by
    apply s.isPushout.hom_ext
    · rw [← Category.assoc, s.isPushout.inl_desc, ← Category.assoc, s.inl_ι]
      apply (cancel_epi (SimplicialCylinder.zeroFactorIso B).hom).mp
      exact hB.symm
    · rw [← Category.assoc, s.isPushout.inr_desc, ← Category.assoc, s.inr_ι]
      exact hC
  have : HasLiftingProperty s.ι p :=
    SSet.anodyneExtensions_pushoutObjObjι s (SimplicialCylinder.delta_one_anodyne j) p hp
  let sq : CommSq a s.ι p K := ⟨hs⟩
  have hi : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
  have hj : s.inl ≫ s.ι = B ◁ SSet.stdSimplex.δ (n := 0) j := s.inl_ι
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← hi, Category.assoc, sq.fac_left]
    exact s.isPushout.inr_desc _ _ _
  · dsimp only [endpoint]
    rw [Category.assoc, ← hj, Category.assoc, sq.fac_left, s.isPushout.inl_desc]
    rfl

lemma anodyne_of_coherent_span {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (g : B ⟶ A) (cA : A ⟶ A) (cB : B ⟶ B)
    (H₀ : SSet.Homotopy (i ≫ g) cA) (K₀ : SSet.Homotopy (g ≫ i) cB)
    (H₁ : SSet.Homotopy (𝟙 A) cA) (K₁ : SSet.Homotopy (𝟙 B) cB)
    (coh₀ : H₀.h ≫ i = i ▷ Δ[1] ≫ K₀.h)
    (coh₁ : H₁.h ≫ i = i ▷ Δ[1] ≫ K₁.h) : SSet.anodyneExtensions i := by
  intro X Y p hp
  constructor
  intro a b s
  obtain ⟨Q,hQA,hQ₀,hQp⟩ := cylinder_lift i p hp 1 (g ≫ a)
    (H₀.h ≫ a) (K₀.h ≫ b)
    (by rw [endpoint_zero, H₀.h₀_assoc]; simp only [Category.assoc])
    (by rw [endpoint_zero, K₀.h₀_assoc]; simpa only [Category.assoc] using congrArg (g ≫ ·) s.w.symm)
    (by rw [Category.assoc, s.w, ← Category.assoc H₀.h i, coh₀]; simp)
  let l := SSet.ι₁ ≫ Q
  have hlA : i ≫ l = cA ≫ a := by
    dsimp only [l]
    rw [← SSet.ι₁_comp_assoc, hQA, H₀.h₁_assoc]
  have hlB : l ≫ p = cB ≫ b := by
    dsimp only [l]
    rw [Category.assoc, hQp, K₀.h₁_assoc]
  obtain ⟨R,hRA,hR₁,hRp⟩ := cylinder_lift i p hp 0 l
    (H₁.h ≫ a) (K₁.h ≫ b)
    (by rw [endpoint_one, H₁.h₁_assoc, hlA])
    (by rw [endpoint_one, K₁.h₁_assoc, hlB])
    (by rw [Category.assoc, s.w, ← Category.assoc H₁.h i, coh₁]; simp)
  refine ⟨⟨{ l := SSet.ι₀ ≫ R, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← SSet.ι₀_comp_assoc, hRA, H₁.h₀_assoc, Category.id_comp]
  · rw [Category.assoc, hRp, K₁.h₀_assoc, Category.id_comp]
end Thomason.HornSubdivision

end

noncomputable section
universe u v w z


namespace Thomason.HornSubdivision
open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory PartialOrder

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def orderCylinder (f g : P →o Q) (h : ∀ x, f x ≤ g x) : OneCat.Interval.{u} × P →o Q where
  toFun x := if x.1.down = 0 then f x.2 else g x.2
  monotone' := by
    rintro ⟨⟨b⟩,x⟩ ⟨⟨c⟩,y⟩ ⟨hbc,hxy⟩
    fin_cases b <;> fin_cases c
    · exact f.monotone hxy
    · exact (h x).trans (g.monotone hxy)
    · exact False.elim (by simp at hbc)
    · exact g.monotone hxy

def orderCylinderCat (f g : P →o Q) (h : ∀ x, f x ≤ g x) :
    OneCat.cylinder.obj (Cat.of P) ⟶ Cat.of Q :=
  ({ obj := orderCylinder f g h
     map := fun a => homOfLE ((orderCylinder f g h).monotone ⟨leOfHom a.1,leOfHom a.2⟩) } :
    OneCat.Interval.{u} × P ⥤ Q).toCatHom

def orderHomotopy (f g : P →o Q) (h : ∀ x, f x ≤ g x) :
    SSet.Homotopy (nerveMap f.toFunctor) (nerveMap g.toFunctor) where
  h := OneCat.cylinderMap (C := Cat.of P) (D := Cat.of Q) (orderCylinderCat f g h)
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,hx⟩,θ⟩
    exact False.elim hx

lemma orderHomotopy_coherent {A B : Type u} [PartialOrder A] [PartialOrder B]
    (i : A →o B) (fA gA : A →o A) (fB gB : B →o B)
    (hA : ∀ x, fA x ≤ gA x) (hB : ∀ x, fB x ≤ gB x)
    (hf : ∀ x, i (fA x) = fB (i x)) (hg : ∀ x, i (gA x) = gB (i x)) :
    (orderHomotopy fA gA hA).h ≫ nerveMap i.toFunctor =
      (nerveMap i.toFunctor ▷ Δ[1]) ≫ (orderHomotopy fB gB hB).h := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  exact CategoryTheory.Functor.ext (fun j => by
    change i (if (SSet.stdSimplex.objEquiv x.2).toOrderHom j = 0
        then fA (x.1.obj j) else gA (x.1.obj j)) =
      (if (SSet.stdSimplex.objEquiv x.2).toOrderHom j = 0
        then fB (i (x.1.obj j)) else gB (i (x.1.obj j)))
    split_ifs <;> [exact hf _; exact hg _])

lemma hornFaceInclusion_anodyne {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    SSet.anodyneExtensions (nerveMap (OrderHom.Subtype.val
      (fun chain : NonemptyFiniteChains (ULift.{u} (Fin (n+1))) =>
        chain ∈ Subdivision.HornFaces.{u} n k)).toFunctor) := by
  classical
  let B := NonemptyFiniteChains (ULift.{u} (Fin (n+1)))
  let A := Subdivision.HornFaces.{u} n k
  let i : A →o B := OrderHom.Subtype.val _
  let a₀ : A := Subdivision.hornFacePoint hn k
  let g : B →o A := OrderHom.const _ a₀
  let cA := Subdivision.hornFaceCone k
  let cB : B →o B := {
    toFun := fun s => ⟨insert (ULift.up k) s.finset, by simp, by
      intro a b
      exact le_total a.val b.val⟩
    monotone' := by
      intro s t h a ha
      rcases Finset.mem_insert.mp ha with ha | ha
      · exact Finset.mem_insert.mpr (Or.inl ha)
      · exact Finset.mem_insert.mpr (Or.inr (h ha)) }
  have hcB (s : B) : s ≤ cB s := fun _ => Finset.mem_insert_of_mem
  have hkB (s : B) : i a₀ ≤ cB s := by
    intro a ha
    have he : a = ULift.up k := by
      change a ∈ ({ULift.up k} : Finset _) at ha
      exact Finset.mem_singleton.mp ha
    subst a
    exact Finset.mem_insert_self _ _
  have : Mono (nerveMap i.toFunctor) := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [CategoryTheory.mono_iff_injective]
    intro x y h
    exact CategoryTheory.Functor.ext (fun j => Subtype.ext (congrArg (fun z => z.obj j) h))
  let H₀ := orderHomotopy (g.comp i) cA (fun s => Subdivision.hornFacePoint_le_cone hn k s)
  let K₀ := orderHomotopy (i.comp g) cB hkB
  let H₁ := orderHomotopy (OrderHom.id) cA (fun s => Subdivision.le_hornFaceCone k s)
  let K₁ := orderHomotopy (OrderHom.id) cB hcB
  apply anodyne_of_coherent_span (nerveMap i.toFunctor) (nerveMap g.toFunctor)
    (nerveMap cA.toFunctor) (nerveMap cB.toFunctor) H₀ K₀ H₁ K₁
  · exact orderHomotopy_coherent i (g.comp i) cA (i.comp g) cB _ _ (fun _ => rfl) (fun _ => rfl)
  · exact orderHomotopy_coherent i OrderHom.id cA OrderHom.id cB _ _ (fun _ => rfl) (fun _ => rfl)
end Thomason.HornSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdividedUnit
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivided Unit. -/

noncomputable section
universe u v w z


namespace Thomason.HornSubdivision
open CategoryTheory Simplicial PartialOrder Subdivision

noncomputable def sdSimplexSubcomplexIso {m : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    SSet.sd.obj (K : SSet.{u}) ≅ nerve (AllowedChains (orderedSimplexSubcomplex K)) :=
  SSet.sd.mapIso (orderedSimplexSubcomplexIso K) ≪≫ sdSubcomplexIso (orderedSimplexSubcomplex K)

noncomputable def sdSimplexIso (m : ℕ) :
    SSet.sd.obj (SSet.stdSimplex.{u}.obj ⦋m⦌) ≅
      nerve (NonemptyFiniteChains (ULift.{u} (Fin (m+1)))) :=
  SSet.sd.mapIso (SSet.stdSimplex.isoNerve.{u} m) ≪≫ sdNerveIso

lemma sdSimplexSubcomplexIso_naturality {m : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    SSet.sd.map K.ι ≫ (sdSimplexIso m).hom =
      (sdSimplexSubcomplexIso K).hom ≫ allowedChainsForget (orderedSimplexSubcomplex K) := by
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  simp only [Functor.mapIso_hom]
  erw [← Category.assoc, ← Functor.map_comp]
  have he : K.ι ≫ (SSet.stdSimplex.isoNerve.{u} m).hom =
      (orderedSimplexSubcomplexIso K).hom ≫ (orderedSimplexSubcomplex K).ι := rfl
  erw [he, Functor.map_comp, Category.assoc, sdSubcomplexMap_naturality, ← Category.assoc]

theorem sd_horn_anodyne {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    SSet.anodyneExtensions (SSet.sd.map (SSet.horn.{u} n k).ι) := by
  let e := PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (AllowedChains (orderedSimplexSubcomplex (SSet.horn n k))))
      (β := PartOrd.of (HornFaces.{u} n k)) (hornFacesIso k))
  have he : e.hom ≫ nerveMap (OrderHom.Subtype.val
      (fun chain : NonemptyFiniteChains (ULift.{u} (Fin (n+1))) =>
        chain ∈ HornFaces.{u} n k)).toFunctor =
      allowedChainsForget (orderedSimplexSubcomplex (SSet.horn n k)) := rfl
  have h := SSet.anodyneExtensions.comp_mem e.hom _ (SSet.anodyneExtensions.of_isIso _) (hornFaceInclusion_anodyne hn k)
  rw [he] at h
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk
    (sdSimplexSubcomplexIso (SSet.horn n k)) (sdSimplexIso n)
    (sdSimplexSubcomplexIso_naturality (SSet.horn n k)).symm)).mpr h

theorem ex_preserves_fibrations {X Y : SSet.{u}} (p : X ⟶ Y) (hp : simplicialFibrations p) :
    simplicialFibrations (SSet.ex.map p) := by
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact (SSet.sdExAdjunction.hasLiftingProperty_iff _ p).mp
    (sd_horn_anodyne (by omega) k p hp)

theorem sd_preserves_anodyne {A B : SSet.{u}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i) :
    SSet.anodyneExtensions (SSet.sd.map i) := by
  intro X Y p hp
  exact (SSet.sdExAdjunction.hasLiftingProperty_iff i p).mpr
    (hi (SSet.ex.map p) (ex_preserves_fibrations p hp))

end Thomason.HornSubdivision

end

noncomputable section
universe u v w z


namespace Thomason.LastVertexProof
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

def Homotopic {A B : SSet.{u}} (f g : A ⟶ B) : Prop :=
  Relation.EqvGen (fun f g : A ⟶ B => Nonempty (SSet.Homotopy f g)) f g

lemma homotopic_of_homotopy {A B : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    Homotopic f g := .rel _ _ ⟨H⟩

lemma homotopic_refl {A B : SSet.{u}} (f : A ⟶ B) : Homotopic f f := .refl _
lemma homotopic_symm {A B : SSet.{u}} {f g : A ⟶ B} (H : Homotopic f g) :
    Homotopic g f := .symm _ _ H
lemma homotopic_trans {A B : SSet.{u}} {f g h : A ⟶ B}
    (H : Homotopic f g) (H' : Homotopic g h) : Homotopic f h := .trans _ _ _ H H'

noncomputable def homotopy_pre {A B C : SSet.{u}} (k : A ⟶ B) {f g : B ⟶ C}
    (H : SSet.Homotopy f g) : SSet.Homotopy (k ≫ f) (k ≫ g) :=
  CoherentGluing.toHomotopy ((k ▷ Δ[1]) ≫ H.h)
    (by rw [SSet.ι₀_comp_assoc, H.h₀])
    (by rw [SSet.ι₁_comp_assoc, H.h₁])

noncomputable def homotopy_post {A B C : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (k : B ⟶ C) : SSet.Homotopy (f ≫ k) (g ≫ k) :=
  CoherentGluing.toHomotopy (H.h ≫ k) (by simp) (by simp)

lemma homotopic_pre {A B C : SSet.{u}} (k : A ⟶ B) {f g : B ⟶ C}
    (H : Homotopic f g) : Homotopic (k ≫ f) (k ≫ g) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (homotopy_pre k H.some)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma homotopic_post {A B C : SSet.{u}} {f g : A ⟶ B}
    (H : Homotopic f g) (k : B ⟶ C) : Homotopic (f ≫ k) (g ≫ k) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (homotopy_post H.some k)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

def intervalEnds : SimplicialCylinder.Ends (Δ[0] : SSet.{u}) ⟶ Δ[1] :=
  SimplicialCylinder.endsMap (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0))
    (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1))

instance intervalEnds_mono : Mono (intervalEnds.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply SSet.stdSimplex.ext
      intro j
      apply Fin.ext
      omega
    | inr b =>
      have h := congrArg (fun z : (Δ[1] : SSet).obj k => SSet.stdSimplex.asOrderHom z 0) hab
      exact (zero_ne_one h).elim
  | inr a =>
    cases b with
    | inl b =>
      have h := congrArg (fun z : (Δ[1] : SSet).obj k => SSet.stdSimplex.asOrderHom z 0) hab
      exact (one_ne_zero h).elim
    | inr b =>
      apply congrArg Sum.inr
      apply SSet.stdSimplex.ext
      intro j
      apply Fin.ext
      omega

def endsTensorMap {A B : SSet.{u}} (f g : A ⟶ B) :
    A ⊗ SimplicialCylinder.Ends Δ[0] ⟶ B where
  app k := ↾fun x => match x.2 with
    | Sum.inl _ => f.app k x.1
    | Sum.inr _ => g.app k x.1
  naturality k l a := by
    ext x
    rcases x with ⟨x, y⟩
    cases y with
    | inl y => exact NatTrans.naturality_apply f a x
    | inr y => exact NatTrans.naturality_apply g a x

lemma homotopy_of_anodyne_eq {A B K : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) [SSet.KanComplex K]
    (f g : B ⟶ K) (h : i ≫ f = i ≫ g) : Nonempty (SSet.Homotopy f g) := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i intervalEnds
  let H : A ⊗ Δ[1] ⟶ K := fst _ _ ≫ i ≫ f
  have hc : i ▷ SimplicialCylinder.Ends Δ[0] ≫ endsTensorMap f g = A ◁ intervalEnds ≫ H := by
    ext k x
    rcases x with ⟨x,y⟩
    cases y with
    | inl y => rfl
    | inr y => exact (congrArg (fun t : A ⟶ K => t.app k x) h).symm
  let a : s.pt ⟶ K := s.isPushout.desc (endsTensorMap f g) H hc
  have : HasLiftingProperty s.ι (terminal.from K) :=
    SSet.anodyneExtensions_pushoutObjObjι' s hi (terminal.from K)
      (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let lsq : CommSq a s.ι (terminal.from K) (terminal.from (B ⊗ Δ[1])) := ⟨by simp⟩
  have he : B ◁ intervalEnds ≫ lsq.lift = endsTensorMap f g := by
    have hj : s.inl ≫ s.ι = B ◁ intervalEnds := s.inl_ι
    rw [← hj, Category.assoc, lsq.fac_left]
    exact s.isPushout.inl_desc _ _ _
  refine ⟨CoherentGluing.toHomotopy lsq.lift ?_ ?_⟩
  · ext k x
    have he' := congrArg (fun t => t.app k (x, Sum.inl (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he
    exact he'
  · ext k x
    have he' := congrArg (fun t => t.app k (x, Sum.inr (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he
    exact he'

lemma extend_anodyne {A B K : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) [SSet.KanComplex K] (f : A ⟶ K) :
    ∃ g : B ⟶ K, i ≫ g = f := by
  have : HasLiftingProperty i (terminal.from K) := hi (terminal.from K)
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let s : CommSq f i (terminal.from K) (terminal.from B) := ⟨by simp⟩
  exact ⟨s.lift, s.fac_left⟩

lemma ex_kan (K : SSet.{u}) [SSet.KanComplex K] : SSet.KanComplex (SSet.ex.obj K) := by
  rw [SSet.KanComplex.iff]
  intro n k f hf
  obtain ⟨g,hg⟩ := extend_anodyne (SSet.sd.map (SSet.horn (n+1) k).ι)
    (HornSubdivision.sd_horn_anodyne (by omega) k)
    ((SSet.sdExAdjunction.homEquiv _ K).symm hf.desc)
  let g' := (SSet.sdExAdjunction.homEquiv _ K) g
  have hg' : (SSet.horn (n+1) k).ι ≫ g' = hf.desc := by
    rw [show g' = (SSet.sdExAdjunction.homEquiv _ K) g from rfl,
      ← SSet.sdExAdjunction.homEquiv_naturality_left, hg]
    exact (SSet.sdExAdjunction.homEquiv _ K).apply_symm_apply _
  refine ⟨g', fun j hj => ?_⟩
  have h := congrArg (fun t => SSet.horn.ι k j hj ≫ t) hg'
  simpa only [← Category.assoc, SSet.horn.ι_ι, SSet.horn.IsCompatible.ι_desc] using h

noncomputable def sdCylinderMap (X : SSet.{u}) :
    SSet.sd.obj (X ⊗ Δ[1]) ⟶ SSet.sd.obj X ⊗ Δ[1] :=
  lift (SSet.sd.map (fst _ _)) (SSet.sd.map (snd _ _) ≫ Subdivision.lastVertex.app Δ[1])

lemma sdCylinderMap_zero (X : SSet.{u}) :
    SSet.sd.map (SSet.ι₀ (X := X)) ≫ sdCylinderMap X = SSet.ι₀ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, sdCylinderMap, lift_fst, ← Functor.map_comp,
      SSet.ι₀_fst, CategoryTheory.Functor.map_id]
  · simp only [Category.assoc, sdCylinderMap, lift_snd]
    rw [← Category.assoc, ← Functor.map_comp, Subdivision.lastVertex.naturality]
    rw [SSet.ι₀_snd, SSet.ι₀_snd]
    rfl

lemma sdCylinderMap_one (X : SSet.{u}) :
    SSet.sd.map (SSet.ι₁ (X := X)) ≫ sdCylinderMap X = SSet.ι₁ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, sdCylinderMap, lift_fst, ← Functor.map_comp,
      SSet.ι₁_fst, CategoryTheory.Functor.map_id]
  · simp only [Category.assoc, sdCylinderMap, lift_snd]
    rw [← Category.assoc, ← Functor.map_comp, Subdivision.lastVertex.naturality]
    rw [SSet.ι₁_snd, SSet.ι₁_snd]
    rfl

noncomputable def mateHomotopy {X K : SSet.{u}} {f g : SSet.sd.obj X ⟶ K}
    (H : SSet.Homotopy f g) :
    SSet.Homotopy ((SSet.sdExAdjunction.homEquiv X K) f)
      ((SSet.sdExAdjunction.homEquiv X K) g) :=
  CoherentGluing.toHomotopy
    ((SSet.sdExAdjunction.homEquiv _ K) (sdCylinderMap X ≫ H.h))
    (by rw [← SSet.sdExAdjunction.homEquiv_naturality_left,
      ← Category.assoc, sdCylinderMap_zero, H.h₀])
    (by rw [← SSet.sdExAdjunction.homEquiv_naturality_left,
      ← Category.assoc, sdCylinderMap_one, H.h₁])

lemma mate_homotopic {X K : SSet.{u}} {f g : SSet.sd.obj X ⟶ K}
    (H : Homotopic f g) :
    Homotopic ((SSet.sdExAdjunction.homEquiv X K) f)
      ((SSet.sdExAdjunction.homEquiv X K) g) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (mateHomotopy H.some)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma unmate_homotopy {X K : SSet.{u}} [SSet.KanComplex K]
    {f g : X ⟶ SSet.ex.obj K} (H : SSet.Homotopy f g) :
    Nonempty (SSet.Homotopy ((SSet.sdExAdjunction.homEquiv X K).symm f)
      ((SSet.sdExAdjunction.homEquiv X K).symm g)) := by
  let h := (SSet.sdExAdjunction.homEquiv (X ⊗ Δ[1]) K).symm H.h
  let f' := (SSet.sdExAdjunction.homEquiv X K).symm f
  let g' := (SSet.sdExAdjunction.homEquiv X K).symm g
  have h₀ : SSet.sd.map (SSet.ι₀ (X := X)) ≫ h = f' := by
    dsimp only [h, f']
    rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm, H.h₀]
  have h₁ : SSet.sd.map (SSet.ι₁ (X := X)) ≫ h = g' := by
    dsimp only [h, g']
    rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm, H.h₁]
  let p := SSet.sd.map (fst X Δ[1])
  have hp₀ : SSet.sd.map (SSet.ι₀ (X := X)) ≫ p = 𝟙 _ := by
    dsimp only [p]
    rw [← Functor.map_comp, SSet.ι₀_fst, CategoryTheory.Functor.map_id]
  have hp₁ : SSet.sd.map (SSet.ι₁ (X := X)) ≫ p = 𝟙 _ := by
    dsimp only [p]
    rw [← Functor.map_comp, SSet.ι₁_fst, CategoryTheory.Functor.map_id]
  obtain ⟨Q⟩ := homotopy_of_anodyne_eq (SSet.sd.map (SSet.ι₀ (X := X)))
    (HornSubdivision.sd_preserves_anodyne _ (SimplicialCylinder.endpoint_anodyne X).1)
    (p ≫ f') h (by rw [← Category.assoc, hp₀, Category.id_comp, h₀])
  have R := homotopy_pre (SSet.sd.map (SSet.ι₁ (X := X))) Q
  rw [← Category.assoc, hp₁, Category.id_comp, h₁] at R
  exact ⟨R⟩

lemma unmate_homotopic {X K : SSet.{u}} [SSet.KanComplex K]
    {f g : X ⟶ SSet.ex.obj K} (H : Homotopic f g) :
    Homotopic ((SSet.sdExAdjunction.homEquiv X K).symm f)
      ((SSet.sdExAdjunction.homEquiv X K).symm g) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (unmate_homotopy H.some).some
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma ex_retract (K : SSet.{u}) [SSet.KanComplex K] :
    ∃ r : SSet.ex.obj K ⟶ K, Subdivision.exComparison.app K ≫ r = 𝟙 K ∧
      Homotopic (r ≫ Subdivision.exComparison.app K) (𝟙 _) := by
  obtain ⟨r,hr⟩ := extend_anodyne (Subdivision.exComparison.app K)
    (Subdivision.exComparison_anodyne K) (𝟙 K)
  let := ex_kan K
  obtain ⟨H⟩ := homotopy_of_anodyne_eq (Subdivision.exComparison.app K)
    (Subdivision.exComparison_anodyne K) (r ≫ Subdivision.exComparison.app K) (𝟙 _)
    (by rw [← Category.assoc, hr]; simp)
  exact ⟨r, hr, homotopic_of_homotopy H⟩

lemma mate_lastVertex {X K : SSet.{u}} (f : X ⟶ K) :
    (SSet.sdExAdjunction.homEquiv X K) (Subdivision.lastVertex.app X ≫ f) =
      f ≫ Subdivision.exComparison.app K := by
  have hn : SSet.sd.map f ≫ Subdivision.lastVertex.app K =
      Subdivision.lastVertex.app X ≫ f := Subdivision.lastVertex.naturality f
  rw [← hn, SSet.sdExAdjunction.homEquiv_naturality_left]
  rfl

lemma precomp_lastVertex_surjective (X K : SSet.{u}) [SSet.KanComplex K]
    (g : SSet.sd.obj X ⟶ K) :
    ∃ f : X ⟶ K, Homotopic (Subdivision.lastVertex.app X ≫ f) g := by
  obtain ⟨r,hr,Hr⟩ := ex_retract K
  let g' := (SSet.sdExAdjunction.homEquiv X K) g
  refine ⟨g' ≫ r, ?_⟩
  have H := homotopic_pre g' Hr
  simp only [Category.comp_id, ← Category.assoc] at H
  rw [← mate_lastVertex (g' ≫ r)] at H
  have Q := unmate_homotopic H
  dsimp only [g'] at Q
  simpa only [Equiv.symm_apply_apply] using Q

lemma precomp_lastVertex_injective (X K : SSet.{u}) [SSet.KanComplex K]
    (f g : X ⟶ K) (H : Homotopic (Subdivision.lastVertex.app X ≫ f)
      (Subdivision.lastVertex.app X ≫ g)) : Homotopic f g := by
  obtain ⟨r,hr,Hr⟩ := ex_retract K
  have H' := mate_homotopic H
  rw [mate_lastVertex, mate_lastVertex] at H'
  have Q := homotopic_post H' r
  simpa only [Category.assoc, hr, Category.comp_id] using Q

end Thomason.LastVertexProof

end

noncomputable section
universe u v w z


namespace Thomason.KanHomotopy
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open HornSubdivision LastVertexProof

def sides {A K : SSet.{u}} (f g : A ⊗ Δ[1] ⟶ K) :
    SimplicialCylinder.Ends A ⊗ Δ[1] ⟶ K where
  app n := ↾fun x => match x.1 with
    | Sum.inl a => f.app n (a,x.2)
    | Sum.inr a => g.app n (a,x.2)
  naturality n m θ := by
    ext x
    rcases x with ⟨x,t⟩
    cases x with
    | inl x => exact congrArg (fun q : (A ⊗ Δ[1]).obj n ⟶ K.obj m => q (x,t)) (f.naturality θ)
    | inr x => exact congrArg (fun q : (A ⊗ Δ[1]).obj n ⟶ K.obj m => q (x,t)) (g.naturality θ)

lemma endpoint_sides {A K : SSet.{u}} (f g : A ⊗ Δ[1] ⟶ K) (j : Fin 2) :
    endpoint (SimplicialCylinder.Ends A) j ≫ sides f g =
      SimplicialCylinder.endsMap (endpoint A j ≫ f) (endpoint A j ≫ g) := by
  ext n x
  cases x <;> rfl

lemma ends_sides_post {A K L : SSet.{u}} (f g : A ⊗ Δ[1] ⟶ K) (p : K ⟶ L) :
    sides f g ≫ p = sides (f ≫ p) (g ≫ p) := by
  ext n x
  rcases x with ⟨x,t⟩
  cases x <;> rfl

lemma ends_pre {A K : SSet.{u}} (b : A ⊗ Δ[1] ⟶ K) :
    SimplicialCylinder.endsInclusion A ≫ b =
      SimplicialCylinder.endsMap (SSet.ι₀ ≫ b) (SSet.ι₁ ≫ b) := by
  ext n x
  cases x <;> rfl

lemma square_top_zero {A K : SSet.{u}}
    (Q : (A ⊗ Δ[1]) ⊗ Δ[1] ⟶ K) (l r : A ⊗ Δ[1] ⟶ K)
    (h : SimplicialCylinder.endsInclusion A ▷ Δ[1] ≫ Q = sides l r) :
    SSet.ι₀ ≫ SSet.ι₁ ≫ Q = SSet.ι₁ ≫ l := by
  ext n x
  exact congrArg (fun f => f.app n (Sum.inl x, SSet.stdSimplex.const _ 1 _)) h

lemma square_top_one {A K : SSet.{u}}
    (Q : (A ⊗ Δ[1]) ⊗ Δ[1] ⟶ K) (l r : A ⊗ Δ[1] ⟶ K)
    (h : SimplicialCylinder.endsInclusion A ▷ Δ[1] ≫ Q = sides l r) :
    SSet.ι₁ ≫ SSet.ι₁ ≫ Q = SSet.ι₁ ≫ r := by
  ext n x
  exact congrArg (fun f => f.app n (Sum.inr x, SSet.stdSimplex.const _ 1 _)) h

lemma fill_rectangle {A K : SSet.{u}} [SSet.KanComplex K]
    {a b c d : A ⟶ K} (bottom : SSet.Homotopy a b)
    (left : SSet.Homotopy a c) (right : SSet.Homotopy b d) :
    Nonempty (SSet.Homotopy c d) := by
  have hp : simplicialFibrations (terminal.from K) := by
    change SSet.modelCategoryQuillen.J.rlp (terminal.from K)
    rw [← SSet.modelCategoryQuillen.fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
    infer_instance
  obtain ⟨Q,hQ,_,_⟩ := cylinder_lift (SimplicialCylinder.endsInclusion A)
    (terminal.from K) hp 1 bottom.h (sides left.h right.h) (terminal.from _)
    (by rw [endpoint_sides, endpoint_zero, left.h₀, right.h₀,
      ends_pre, bottom.h₀, bottom.h₁])
    (by subsingleton) (by subsingleton)
  refine ⟨CoherentGluing.toHomotopy (SSet.ι₁ ≫ Q) ?_ ?_⟩
  · exact (square_top_zero Q left.h right.h hQ).trans left.h₁
  · exact (square_top_one Q left.h right.h hQ).trans right.h₁

def refl {A K : SSet.{u}} (a : A ⟶ K) : SSet.Homotopy a a :=
  CoherentGluing.toHomotopy (fst A Δ[1] ≫ a) (by simp) (by simp)

lemma homotopy_symm {A K : SSet.{u}} [SSet.KanComplex K]
    {a b : A ⟶ K} (H : SSet.Homotopy a b) : Nonempty (SSet.Homotopy b a) :=
  fill_rectangle (refl a) H (refl a)

lemma homotopy_trans {A K : SSet.{u}} [SSet.KanComplex K]
    {a b c : A ⟶ K} (H : SSet.Homotopy a b) (H' : SSet.Homotopy b c) :
    Nonempty (SSet.Homotopy a c) := fill_rectangle H (refl a) H'

lemma homotopy_of_homotopic {A K : SSet.{u}} [SSet.KanComplex K]
    {a b : A ⟶ K} (H : Homotopic a b) : Nonempty (SSet.Homotopy a b) := by
  induction H with
  | rel f g H => exact H
  | refl f => exact ⟨refl f⟩
  | symm f g _ ih => exact homotopy_symm ih.some
  | trans f g h _ _ ih ih' => exact homotopy_trans ih.some ih'.some

def maxSquare (A : SSet.{u}) : (A ⊗ Δ[1]) ⊗ Δ[1] ⟶ A ⊗ Δ[1] where
  app n := ↾fun x => (x.1.1, SSet.stdSimplex.objMk
    (SSet.stdSimplex.asOrderHom x.1.2 ⊔ SSet.stdSimplex.asOrderHom x.2))
  naturality n m θ := by
    ext x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro j
      rfl

@[reassoc] lemma maxSquare_bottom (A : SSet.{u}) : SSet.ι₀ ≫ maxSquare A = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    change max (_ : Fin 2) 0 = _
    exact max_eq_left (Fin.zero_le _)

@[reassoc] lemma maxSquare_top (A : SSet.{u}) :
    SSet.ι₁ ≫ maxSquare A = fst A Δ[1] ≫ SSet.ι₁ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    change max (_ : Fin 2) 1 = 1
    exact max_eq_right (Fin.is_le _)

lemma maxSquare_sides (A : SSet.{u}) :
    SimplicialCylinder.endsInclusion A ▷ Δ[1] ≫ maxSquare A =
      sides (𝟙 _) (fst A Δ[1] ≫ SSet.ι₁) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨x,t⟩
  cases x with
  | inl x =>
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro j
      change max 0 (_ : Fin 2) = _
      exact max_eq_right (Fin.zero_le _)
  | inr x =>
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro j
      change max 1 (_ : Fin 2) = 1
      exact max_eq_left (Fin.is_le _)

lemma verticalize {X Y : SSet.{u}} (p : X ⟶ Y) (hp : simplicialFibrations p)
    (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (H : SSet.Homotopy (p ≫ s) (𝟙 X)) :
    ∃ (Q : SSet.Homotopy (p ≫ s) (𝟙 X)), Q.h ≫ p = fst X Δ[1] ≫ p := by
  let l := H.h ≫ p ≫ s
  let r := fst X Δ[1]
  have hl₀ : SSet.ι₀ ≫ l = p ≫ s := by
    dsimp only [l]
    rw [H.h₀_assoc, Category.assoc, ← Category.assoc s p, hs, Category.id_comp]
  have hl₁ : SSet.ι₁ ≫ l = p ≫ s := by
    dsimp only [l]
    rw [H.h₁_assoc, Category.id_comp]
  have hc : sides l r ≫ p = SimplicialCylinder.endsInclusion X ▷ Δ[1] ≫
      (maxSquare X ≫ H.h ≫ p) := by
    rw [ends_sides_post, ← Category.assoc, maxSquare_sides, Category.assoc,
      ends_sides_post]
    congr 1
    · simp only [Category.assoc, hs, Category.comp_id, Category.id_comp]
    · dsimp only [r]
      simp only [Category.assoc, H.h₁_assoc, Category.id_comp]
  obtain ⟨Q,hQ,_,hQp⟩ := cylinder_lift (SimplicialCylinder.endsInclusion X)
    p hp 1 H.h (sides l r) (maxSquare X ≫ H.h ≫ p)
    (by rw [endpoint_sides, endpoint_zero, hl₀, show SSet.ι₀ ≫ r = 𝟙 X from by
          dsimp only [r]; simp, ends_pre, H.h₀, H.h₁])
    (by rw [endpoint_zero, maxSquare_bottom_assoc]) hc
  have hz : SSet.ι₀ ≫ SSet.ι₁ ≫ Q = p ≫ s :=
    (square_top_zero Q l r hQ).trans hl₁
  have ho : SSet.ι₁ ≫ SSet.ι₁ ≫ Q = 𝟙 X := by
    rw [square_top_one Q l r hQ]
    dsimp only [r]
    simp
  refine ⟨CoherentGluing.toHomotopy (SSet.ι₁ ≫ Q) hz ho, ?_⟩
  change (SSet.ι₁ ≫ Q) ≫ p = _
  rw [Category.assoc, hQp, ← Category.assoc, maxSquare_top, Category.assoc,
    H.h₁_assoc, Category.id_comp]

lemma rlp_of_vertical_retract {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : simplicialFibrations p) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (H : SSet.Homotopy (p ≫ s) (𝟙 X)) (hH : H.h ≫ p = fst X Δ[1] ≫ p) :
    (MorphismProperty.monomorphisms SSet).rlp p := by
  intro A B i hi
  let : Mono i := hi
  constructor
  intro a b sq
  obtain ⟨Q,hQ,hQ₀,hQp⟩ := cylinder_lift i p hp 1 (b ≫ s)
    (a ▷ Δ[1] ≫ H.h) (fst B Δ[1] ≫ b)
    (by rw [endpoint_zero, SSet.ι₀_comp_assoc, H.h₀];
        simpa only [Category.assoc] using congrArg (· ≫ s) sq.w)
    (by rw [endpoint_zero]; simp [hs])
    (by rw [Category.assoc, hH, ← Category.assoc, whiskerRight_fst,
          Category.assoc, sq.w]; rfl)
  refine ⟨⟨{ l := SSet.ι₁ ≫ Q, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← SSet.ι₁_comp_assoc, hQ, SSet.ι₁_comp_assoc, H.h₁]
    simp
  · rw [Category.assoc, hQp]
    simp

def IsHomotopyEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, Homotopic (f ≫ g) (𝟙 X) ∧ Homotopic (g ≫ f) (𝟙 Y)

lemma rlp_of_homotopy_equivalence {X Y : SSet.{u}}
    [SSet.KanComplex X] [SSet.KanComplex Y]
    (p : X ⟶ Y) (hp : simplicialFibrations p) (he : IsHomotopyEquivalence p) :
    (MorphismProperty.monomorphisms SSet).rlp p := by
  obtain ⟨g,hg,hh⟩ := he
  obtain ⟨H⟩ := homotopy_of_homotopic hh
  have : HasLiftingProperty (SSet.ι₀ (X := Y)) p :=
    (SimplicialCylinder.endpoint_anodyne Y).1 p hp
  let sq : CommSq g SSet.ι₀ p H.h := ⟨H.h₀.symm⟩
  let s := SSet.ι₁ ≫ sq.lift
  have hs : s ≫ p = 𝟙 Y := by
    dsimp only [s]
    rw [Category.assoc, sq.fac_right, H.h₁]
  let Q : SSet.Homotopy g s := CoherentGluing.toHomotopy sq.lift sq.fac_left rfl
  have hs' : Homotopic (p ≫ s) (𝟙 X) := homotopic_trans
    (homotopic_symm (homotopic_pre p (homotopic_of_homotopy Q))) hg
  obtain ⟨T,hT⟩ := verticalize p hp s hs (homotopy_of_homotopic hs').some
  exact rlp_of_vertical_retract p hp s hs T hT

end Thomason.KanHomotopy

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CoherentGluing
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coherent Gluing. -/

noncomputable section
universe u v w z


namespace Thomason.KanLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy

lemma heq_of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    IsHomotopyEquivalence f := by
  refine ⟨inv f, ?_, ?_⟩ <;> simp only [IsIso.hom_inv_id, IsIso.inv_hom_id]
  · exact homotopic_refl _
  · exact homotopic_refl _

lemma heq_comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsHomotopyEquivalence f) (hg : IsHomotopyEquivalence g) :
    IsHomotopyEquivalence (f ≫ g) := by
  obtain ⟨f', hff',hf'f⟩ := hf
  obtain ⟨g', hgg',hg'g⟩ := hg
  refine ⟨g' ≫ f', ?_, ?_⟩
  · have h := homotopic_post (homotopic_pre f hgg') f'
    simp only [Category.comp_id, Category.assoc] at h ⊢
    exact homotopic_trans h hff'
  · have h := homotopic_post (homotopic_pre g' hf'f) g
    simp only [Category.comp_id, Category.assoc] at h ⊢
    exact homotopic_trans h hg'g

lemma heq_homotopic {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : Homotopic f g) (hf : IsHomotopyEquivalence f) : IsHomotopyEquivalence g := by
  obtain ⟨k,h₀,h₁⟩ := hf
  exact ⟨k, homotopic_trans (homotopic_symm (homotopic_post h k)) h₀,
    homotopic_trans (homotopic_symm (homotopic_pre k h)) h₁⟩

lemma heq_of_rlp {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : (MorphismProperty.monomorphisms SSet).rlp f) : IsHomotopyEquivalence f := by
  have : HasLiftingProperty (initial.to Y) f := hf _ (by infer_instance)
  let sq : CommSq (initial.to X) (initial.to Y) f (𝟙 Y) := ⟨by simp⟩
  let g := sq.lift
  have hg : g ≫ f = 𝟙 Y := sq.fac_right
  have : HasLiftingProperty (SimplicialCylinder.endsInclusion X) f := hf _ (by infer_instance)
  let s : CommSq (SimplicialCylinder.endsMap (f ≫ g) (𝟙 X))
      (SimplicialCylinder.endsInclusion X) f (fst X Δ[1] ≫ f) := ⟨by
    ext n x
    cases x with
    | inl x => exact congrArg (fun q : Y ⟶ Y => (f ≫ q).app n x) hg
    | inr x => rfl⟩
  have h₀ : SSet.ι₀ ≫ s.lift = f ≫ g := by
    ext n x
    exact congrArg (fun q => q.app n (Sum.inl x)) s.fac_left
  have h₁ : SSet.ι₁ ≫ s.lift = 𝟙 X := by
    ext n x
    exact congrArg (fun q => q.app n (Sum.inr x)) s.fac_left
  refine ⟨g, homotopic_of_homotopy (CoherentGluing.toHomotopy s.lift h₀ h₁), ?_⟩
  rw [hg]
  exact homotopic_refl _

def Local {A B : SSet.{u}} (f : A ⟶ B) : Prop :=
  ∀ (K : SSet.{u}), SSet.KanComplex K → IsHomotopyEquivalence ((pre f).app K)

lemma local_iso {A B : SSet.{u}} (f : A ⟶ B) [IsIso f] : Local f := by
  intro K hK
  change IsHomotopyEquivalence ((internalHom.map f.op).app K)
  exact heq_of_isIso _

lemma local_comp {A B C : SSet.{u}} {f : A ⟶ B} {g : B ⟶ C}
    (hf : Local f) (hg : Local g) : Local (f ≫ g) := by
  intro K hK
  simpa only [pre_map, NatTrans.comp_app] using heq_comp (hg K hK) (hf K hK)

def uncurryHomotopy {A T K : SSet.{u}} {f g : T ⟶ (ihom A).obj K}
    (H : SSet.Homotopy f g) : SSet.Homotopy (uncurry f) (uncurry g) :=
  CoherentGluing.toHomotopy ((α_ A T Δ[1]).hom ≫ uncurry H.h)
    (by rw [← Category.assoc]
        change A ◁ SSet.ι₀ ≫ uncurry H.h = _
        rw [← uncurry_natural_left, H.h₀])
    (by rw [← Category.assoc]
        change A ◁ SSet.ι₁ ≫ uncurry H.h = _
        rw [← uncurry_natural_left, H.h₁])

def curryHomotopy {A T K : SSet.{u}} {f g : A ⊗ T ⟶ K}
    (H : SSet.Homotopy f g) : SSet.Homotopy (curry f) (curry g) :=
  CoherentGluing.toHomotopy (curry ((α_ A T Δ[1]).inv ≫ H.h))
    (by apply uncurry_injective
        rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc]
        change SSet.ι₀ ≫ H.h = f
        exact H.h₀)
    (by apply uncurry_injective
        rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc]
        change SSet.ι₁ ≫ H.h = g
        exact H.h₁)

lemma homotopic_uncurry {A T K : SSet.{u}} {f g : T ⟶ (ihom A).obj K}
    (H : Homotopic f g) : Homotopic (uncurry f) (uncurry g) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (uncurryHomotopy H.some)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma homotopic_curry {A T K : SSet.{u}} {f g : A ⊗ T ⟶ K}
    (H : Homotopic f g) : Homotopic (curry f) (curry g) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (curryHomotopy H.some)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

end Thomason.KanLocal

end

noncomputable section
universe u v w z


namespace Thomason.KanLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy HornSubdivision
open SSet.modelCategoryQuillen

lemma heq_of_precomp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : IsHomotopyEquivalence f) (hfg : IsHomotopyEquivalence (f ≫ g)) :
    IsHomotopyEquivalence g := by
  obtain ⟨f',h₀,h₁⟩ := hf
  have hf' : IsHomotopyEquivalence f' := ⟨f,h₁,h₀⟩
  have H := homotopic_post h₁ g
  simp only [Category.assoc, Category.id_comp] at H
  exact heq_homotopic H (heq_comp hf' hfg)

lemma heq_of_postcomp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hg : IsHomotopyEquivalence g) (hfg : IsHomotopyEquivalence (f ≫ g)) :
    IsHomotopyEquivalence f := by
  obtain ⟨g',h₀,h₁⟩ := hg
  have hg' : IsHomotopyEquivalence g' := ⟨g,h₁,h₀⟩
  have H := homotopic_pre f h₀
  simp only [Category.comp_id, ← Category.assoc] at H
  exact heq_homotopic H (heq_comp hfg hg')

end Thomason.KanLocal

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_KanTowers
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kan Towers. -/

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.AttachmentComparison

def upward {P : Type u} [PartialOrder P] (A : Set P) : Set P :=
  {p | ∃ a ∈ A, a ≤ p}

end Thomason.AttachmentComparison

end

noncomputable section
universe u v w z


namespace Thomason.KanPath
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy KanLocal
open SSet.modelCategoryQuillen

abbrev Paths (B : SSet.{u}) := (ihom (Δ[1] : SSet.{u})).obj B

def curryR {A B : SSet.{u}} (h : A ⊗ Δ[1] ⟶ B) : A ⟶ Paths B :=
  curry ((β_ Δ[1] A).hom ≫ h)
def uncurryR {A B : SSet.{u}} (g : A ⟶ Paths B) : A ⊗ Δ[1] ⟶ B :=
  (β_ A Δ[1]).hom ≫ uncurry g

@[simp] lemma uncurryR_curryR {A B : SSet.{u}} (h : A ⊗ Δ[1] ⟶ B) :
    uncurryR (curryR h) = h := by
  dsimp only [uncurryR, curryR]
  rw [uncurry_curry, ← Category.assoc]
  have hh : (β_ A Δ[1]).hom ≫ (β_ Δ[1] A).hom = 𝟙 _ := by ext n x <;> rfl
  rw [hh, Category.id_comp]

@[simp] lemma curryR_uncurryR {A B : SSet.{u}} (g : A ⟶ Paths B) :
    curryR (uncurryR g) = g := by
  dsimp only [uncurryR, curryR]
  rw [← Category.assoc]
  have hh : (β_ Δ[1] A).hom ≫ (β_ A Δ[1]).hom = 𝟙 _ := by ext n x <;> rfl
  rw [hh, Category.id_comp, curry_uncurry]

lemma uncurryR_injective {A B : SSet.{u}} : Function.Injective (@uncurryR A B) := by
  intro g h H
  simpa using congrArg curryR H

@[reassoc] lemma uncurryR_pre {A C B : SSet.{u}} (a : A ⟶ C) (g : C ⟶ Paths B) :
    uncurryR (a ≫ g) = a ▷ Δ[1] ≫ uncurryR g := by
  dsimp only [uncurryR]
  rw [uncurry_natural_left, ← Category.assoc, ← Category.assoc]
  congr 1

@[reassoc] lemma uncurryR_post {A B C : SSet.{u}} (g : A ⟶ Paths B) (f : B ⟶ C) :
    uncurryR (g ≫ (ihom Δ[1]).map f) = uncurryR g ≫ f := by
  dsimp only [uncurryR]
  rw [uncurry_natural_right, Category.assoc]

def ev (B : SSet.{u}) : Paths B ⊗ Δ[1] ⟶ B := uncurryR (𝟙 (Paths B))
def eval₀ (B : SSet.{u}) : Paths B ⟶ B := SSet.ι₀ ≫ ev B
def eval₁ (B : SSet.{u}) : Paths B ⟶ B := SSet.ι₁ ≫ ev B
def const (B : SSet.{u}) : B ⟶ Paths B := curryR (fst B Δ[1])

lemma uncurryR_eq {A B : SSet.{u}} (g : A ⟶ Paths B) :
    uncurryR g = g ▷ Δ[1] ≫ ev B := by
  simpa only [Category.comp_id, ev] using uncurryR_pre g (𝟙 (Paths B))

@[reassoc] lemma comp_eval₀ {A B : SSet.{u}} (g : A ⟶ Paths B) :
    g ≫ eval₀ B = SSet.ι₀ ≫ uncurryR g := by
  rw [uncurryR_eq, eval₀, SSet.ι₀_comp_assoc]
@[reassoc] lemma comp_eval₁ {A B : SSet.{u}} (g : A ⟶ Paths B) :
    g ≫ eval₁ B = SSet.ι₁ ≫ uncurryR g := by
  rw [uncurryR_eq, eval₁, SSet.ι₁_comp_assoc]

@[reassoc (attr := simp)] lemma const_eval₀ (B : SSet.{u}) : const B ≫ eval₀ B = 𝟙 B := by
  rw [comp_eval₀, const, uncurryR_curryR]
  simp
@[reassoc (attr := simp)] lemma const_eval₁ (B : SSet.{u}) : const B ≫ eval₁ B = 𝟙 B := by
  rw [comp_eval₁, const, uncurryR_curryR]
  simp

@[reassoc] lemma eval₀_naturality {B C : SSet.{u}} (f : B ⟶ C) :
    (ihom Δ[1]).map f ≫ eval₀ C = eval₀ B ≫ f := by
  have H := uncurryR_post (𝟙 (Paths B)) f
  simp only [Category.id_comp] at H
  rw [comp_eval₀, H]
  rfl
@[reassoc] lemma eval₁_naturality {B C : SSet.{u}} (f : B ⟶ C) :
    (ihom Δ[1]).map f ≫ eval₁ C = eval₁ B ≫ f := by
  have H := uncurryR_post (𝟙 (Paths B)) f
  simp only [Category.id_comp] at H
  rw [comp_eval₁, H]
  rfl

def minSquare (A : SSet.{u}) : (A ⊗ Δ[1]) ⊗ Δ[1] ⟶ A ⊗ Δ[1] where
  app n := ↾fun x => (x.1.1, SSet.stdSimplex.objMk
    (SSet.stdSimplex.asOrderHom x.1.2 ⊓ SSet.stdSimplex.asOrderHom x.2))
  naturality n m θ := by
    ext x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro j
      rfl

lemma minSquare_left (A : SSet.{u}) : SSet.ι₀ ▷ Δ[1] ≫ minSquare A = fst A Δ[1] ≫ SSet.ι₀ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    change min 0 (_ : Fin 2) = 0
    exact min_eq_left (Fin.zero_le _)
lemma minSquare_right (A : SSet.{u}) : SSet.ι₁ ▷ Δ[1] ≫ minSquare A = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    change min 1 (_ : Fin 2) = _
    exact min_eq_right (Fin.le_last _)
lemma minSquare_bottom (A : SSet.{u}) : SSet.ι₀ ≫ minSquare A = fst A Δ[1] ≫ SSet.ι₀ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    change min (_ : Fin 2) 0 = 0
    exact min_eq_right (Fin.zero_le _)

def contraction (B : SSet.{u}) : SSet.Homotopy (eval₀ B ≫ const B) (𝟙 (Paths B)) :=
  CoherentGluing.toHomotopy (curryR (minSquare (Paths B) ≫ ev B))
    (by
      apply uncurryR_injective
      rw [uncurryR_pre, uncurryR_curryR, ← Category.assoc, minSquare_left,
        Category.assoc, uncurryR_pre, const, uncurryR_curryR, whiskerRight_fst]
      rfl)
    (by
      apply uncurryR_injective
      rw [uncurryR_pre, uncurryR_curryR, ← Category.assoc, minSquare_right, Category.id_comp]
      rfl)

@[reassoc] lemma contraction_eval₀ (B : SSet.{u}) :
    (contraction B).h ≫ eval₀ B = fst _ _ ≫ eval₀ B := by
  rw [comp_eval₀]
  change SSet.ι₀ ≫ uncurryR (curryR (minSquare (Paths B) ≫ ev B)) = _
  rw [uncurryR_curryR, ← Category.assoc, minSquare_bottom, Category.assoc]
  rfl

lemma cylinder_lift_ends {D E X Y : SSet.{u}} (i : D ⟶ E)
    (hi : SSet.anodyneExtensions i) (p : X ⟶ Y) (hp : simplicialFibrations p)
    (x₀ x₁ : E ⟶ X) (H : D ⊗ Δ[1] ⟶ X) (G : E ⊗ Δ[1] ⟶ Y)
    (h₀ : i ≫ x₀ = SSet.ι₀ ≫ H) (h₁ : i ≫ x₁ = SSet.ι₁ ≫ H)
    (g₀ : x₀ ≫ p = SSet.ι₀ ≫ G) (g₁ : x₁ ≫ p = SSet.ι₁ ≫ G)
    (hG : H ≫ p = i ▷ Δ[1] ≫ G) :
    ∃ Q : E ⊗ Δ[1] ⟶ X, i ▷ Δ[1] ≫ Q = H ∧
      SSet.ι₀ ≫ Q = x₀ ∧ SSet.ι₁ ≫ Q = x₁ ∧ Q ≫ p = G := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i intervalEnds
  have hc : i ▷ SimplicialCylinder.Ends Δ[0] ≫ endsTensorMap x₀ x₁ =
      D ◁ intervalEnds ≫ H := by
    ext n x
    rcases x with ⟨x,y⟩
    cases y with
    | inl y => exact congrArg (fun t : D ⟶ X => t.app n x) h₀
    | inr y => exact congrArg (fun t : D ⟶ X => t.app n x) h₁
  let t : s.pt ⟶ X := s.isPushout.desc (endsTensorMap x₀ x₁) H hc
  have hinl : s.inl ≫ s.ι = E ◁ intervalEnds := s.inl_ι
  have hinr : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
  have ht : t ≫ p = s.ι ≫ G := by
    apply s.isPushout.hom_ext
    · simp only [t, ← Category.assoc, s.isPushout.inl_desc, hinl]
      ext n x
      rcases x with ⟨x,y⟩
      cases y with
      | inl y => exact congrArg (fun t : E ⟶ Y => t.app n x) g₀
      | inr y => exact congrArg (fun t : E ⟶ Y => t.app n x) g₁
    · simpa only [t, ← Category.assoc, s.isPushout.inr_desc, hinr] using hG
  have : HasLiftingProperty s.ι p :=
    SSet.anodyneExtensions_pushoutObjObjι' s hi p hp
  let sq : CommSq t s.ι p G := ⟨ht⟩
  have he : E ◁ intervalEnds ≫ sq.lift = endsTensorMap x₀ x₁ := by
    rw [← hinl, Category.assoc, sq.fac_left]
    exact s.isPushout.inl_desc _ _ _
  refine ⟨sq.lift, ?_, ?_, ?_, sq.fac_right⟩
  · rw [← hinr, Category.assoc, sq.fac_left]
    exact s.isPushout.inr_desc _ _ _
  · ext n x
    exact congrArg (fun t => t.app n (x, Sum.inl (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he
  · ext n x
    exact congrArg (fun t => t.app n (x, Sum.inr (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he

abbrev MappingPath {A B : SSet.{u}} (f : A ⟶ B) := pullback f (eval₀ B)
def left {A B : SSet.{u}} (f : A ⟶ B) : A ⟶ MappingPath f :=
  pullback.lift (𝟙 A) (f ≫ const B) (by simp)
def right {A B : SSet.{u}} (f : A ⟶ B) : MappingPath f ⟶ B :=
  pullback.snd f (eval₀ B) ≫ eval₁ B

@[reassoc (attr := simp)] lemma fac {A B : SSet.{u}} (f : A ⟶ B) : left f ≫ right f = f := by
  simp [left, right, pullback.lift_snd_assoc]

lemma left_heq {A B : SSet.{u}} (f : A ⟶ B) : IsHomotopyEquivalence (left f) := by
  let a := pullback.fst f (eval₀ B)
  let p := pullback.snd f (eval₀ B)
  have hp : a ≫ f = p ≫ eval₀ B := pullback.condition
  let H : MappingPath f ⊗ Δ[1] ⟶ MappingPath f := pullback.lift (fst _ _ ≫ a)
    (p ▷ Δ[1] ≫ (contraction B).h)
    (by rw [Category.assoc, Category.assoc, contraction_eval₀,
      whiskerRight_fst_assoc, ← hp])
  refine ⟨a, ?_, ?_⟩
  · have hl : left f ≫ a = 𝟙 A := by simp only [left, a, pullback.lift_fst]
    rw [hl]
    exact homotopic_refl _
  · apply homotopic_of_homotopy
    refine CoherentGluing.toHomotopy H ?_ ?_
    · apply pullback.hom_ext
      · simp [H, a, left, pullback.lift_fst]
      · simp only [H, Category.assoc, pullback.lift_snd]
        rw [SSet.ι₀_comp_assoc, (contraction B).h₀]
        simp only [left, pullback.lift_snd]
        rw [← Category.assoc, ← hp]
        rfl
    · apply pullback.hom_ext
      · simp [H, a, pullback.lift_fst]
      · simp only [H, Category.assoc, pullback.lift_snd, Category.id_comp]
        rw [SSet.ι₁_comp_assoc, (contraction B).h₁, Category.comp_id]

def map {A₁ A₀ B₁ B₀ : SSet.{u}} {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀}
    (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀) (h : a ≫ f₀ = f₁ ≫ b) :
    MappingPath f₁ ⟶ MappingPath f₀ :=
  pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _ ≫ (ihom Δ[1]).map b) (by
    simp only [Category.assoc, eval₀_naturality, h]
    rw [← Category.assoc, pullback.condition, Category.assoc])

@[reassoc (attr := simp)] lemma map_fst {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (h : a ≫ f₀ = f₁ ≫ b) :
    map a b h ≫ pullback.fst f₀ (eval₀ B₀) = pullback.fst f₁ (eval₀ B₁) ≫ a := by
  simp only [map, pullback.lift_fst]
@[reassoc (attr := simp)] lemma map_snd {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (h : a ≫ f₀ = f₁ ≫ b) :
    map a b h ≫ pullback.snd f₀ (eval₀ B₀) =
      pullback.snd f₁ (eval₀ B₁) ≫ (ihom Δ[1]).map b := by
  simp only [map, pullback.lift_snd]
@[reassoc (attr := simp)] lemma map_right {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (h : a ≫ f₀ = f₁ ≫ b) :
    map a b h ≫ right f₀ = right f₁ ≫ b := by
  simp only [right, map_snd_assoc, Category.assoc, eval₁_naturality]

lemma right_lifting {A B D E : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (i : D ⟶ E) (hi : SSet.anodyneExtensions i)
    (x : D ⟶ MappingPath f) (y : E ⟶ B) (h : x ≫ right f = i ≫ y) :
    ∃ l : E ⟶ MappingPath f, i ≫ l = x ∧ l ≫ right f = y := by
  obtain ⟨a,ha⟩ := extend_anodyne i hi (x ≫ pullback.fst f (eval₀ B))
  have hp : simplicialFibrations (terminal.from B) := by
    change J.rlp _
    rw [← fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
    infer_instance
  obtain ⟨Q,hQ,h₀,h₁,_⟩ := cylinder_lift_ends i hi (terminal.from B) hp
    (a ≫ f) y (uncurryR (x ≫ pullback.snd f (eval₀ B))) (terminal.from _)
    (by
      rw [← Category.assoc, ha, Category.assoc, pullback.condition, ← Category.assoc,
        comp_eval₀])
    (by rw [← comp_eval₁]; exact h.symm)
    (by subsingleton) (by subsingleton) (by subsingleton)
  let l : E ⟶ MappingPath f := pullback.lift a (curryR Q)
    (by rw [comp_eval₀, uncurryR_curryR, h₀])
  refine ⟨l, ?_, ?_⟩
  · apply pullback.hom_ext
    · simpa only [l, Category.assoc, pullback.lift_fst] using ha
    · simp only [Category.assoc, l, pullback.lift_snd]
      apply uncurryR_injective
      rw [uncurryR_pre, uncurryR_curryR, hQ]
  · change l ≫ pullback.snd _ _ ≫ eval₁ B = y
    rw [← Category.assoc, pullback.lift_snd, comp_eval₁, uncurryR_curryR, h₁]

lemma right_fibration {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) : simplicialFibrations (right f) := by
  change J.rlp _
  intro D E i hi
  constructor
  intro x y sq
  obtain ⟨l,hl,hr⟩ := right_lifting f i (MorphismProperty.le_llp_rlp J i hi) x y sq.w
  exact ⟨⟨l,hl,hr⟩⟩

lemma relative_lifting {A₁ A₀ B₁ B₀ D E : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) (ha : simplicialFibrations a) (hb : simplicialFibrations b)
    (i : D ⟶ E) (hi : SSet.anodyneExtensions i)
    (x : D ⟶ MappingPath f₁) (y : E ⟶ MappingPath f₀) (z : E ⟶ B₁)
    (hm : x ≫ map a b w = i ≫ y) (hr : x ≫ right f₁ = i ≫ z)
    (hyz : y ≫ right f₀ = z ≫ b) :
    ∃ l : E ⟶ MappingPath f₁, i ≫ l = x ∧ l ≫ map a b w = y ∧ l ≫ right f₁ = z := by
  have : HasLiftingProperty i a := hi _ ha
  let sq : CommSq (x ≫ pullback.fst f₁ (eval₀ B₁)) i a
      (y ≫ pullback.fst f₀ (eval₀ B₀)) := ⟨by
    simpa only [Category.assoc, map_fst] using
      congrArg (fun t => t ≫ pullback.fst f₀ (eval₀ B₀)) hm⟩
  obtain ⟨Q,hQ,h₀,h₁,hbQ⟩ := cylinder_lift_ends i hi b hb
    (sq.lift ≫ f₁) z (uncurryR (x ≫ pullback.snd f₁ (eval₀ B₁)))
    (uncurryR (y ≫ pullback.snd f₀ (eval₀ B₀)))
    (by rw [← Category.assoc, sq.fac_left, Category.assoc, pullback.condition,
      ← Category.assoc, comp_eval₀])
    (by rw [← comp_eval₁]; exact hr.symm)
    (by
      rw [Category.assoc, ← w, ← Category.assoc, sq.fac_right, Category.assoc,
        pullback.condition, ← Category.assoc, comp_eval₀])
    (by rw [← comp_eval₁]; exact hyz.symm)
    (by
      have hm' : (x ≫ pullback.snd f₁ (eval₀ B₁)) ≫ (ihom Δ[1]).map b =
          i ≫ (y ≫ pullback.snd f₀ (eval₀ B₀)) := by
        simpa only [Category.assoc, map_snd] using
          congrArg (fun t => t ≫ pullback.snd f₀ (eval₀ B₀)) hm
      rw [← uncurryR_post, hm', uncurryR_pre])
  let l : E ⟶ MappingPath f₁ := pullback.lift sq.lift (curryR Q)
    (by rw [comp_eval₀, uncurryR_curryR, h₀])
  refine ⟨l, ?_, ?_, ?_⟩
  · apply pullback.hom_ext
    · simpa only [l, Category.assoc, pullback.lift_fst] using sq.fac_left
    · simp only [l, Category.assoc, pullback.lift_snd]
      apply uncurryR_injective
      rw [uncurryR_pre, uncurryR_curryR, hQ]
  · apply pullback.hom_ext
    · simp only [Category.assoc, map_fst, l, pullback.lift_fst_assoc, sq.fac_right]
    · simp only [Category.assoc, map_snd, l, pullback.lift_snd_assoc]
      apply uncurryR_injective
      rw [uncurryR_post, uncurryR_curryR, hbQ]
  · change l ≫ pullback.snd _ _ ≫ eval₁ B₁ = z
    rw [← Category.assoc, pullback.lift_snd, comp_eval₁, uncurryR_curryR, h₁]

abbrev Matching {A₀ B₁ B₀ : SSet.{u}} (f₀ : A₀ ⟶ B₀) (b : B₁ ⟶ B₀) :=
  pullback (right f₀) b

def relative {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) : MappingPath f₁ ⟶ Matching f₀ b :=
  pullback.lift (map a b w) (right f₁) (map_right a b w)

lemma relative_fibration {A₁ A₀ B₁ B₀ : SSet.{u}}
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) (ha : simplicialFibrations a) (hb : simplicialFibrations b) :
    simplicialFibrations (relative a b w) := by
  change J.rlp _
  intro D E i hi
  constructor
  intro x t sq
  obtain ⟨l,hl,hm,hr⟩ := relative_lifting a b w ha hb i
    (MorphismProperty.le_llp_rlp J i hi) x
    (t ≫ pullback.fst (right f₀) b) (t ≫ pullback.snd (right f₀) b)
    (by simpa only [Category.assoc, relative, pullback.lift_fst] using
      congrArg (fun q => q ≫ pullback.fst (right f₀) b) sq.w)
    (by simpa only [Category.assoc, relative, pullback.lift_snd] using
      congrArg (fun q => q ≫ pullback.snd (right f₀) b) sq.w)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  refine ⟨⟨l,hl,?_⟩⟩
  apply pullback.hom_ext
  · simpa only [Category.assoc, relative, pullback.lift_fst] using hm
  · simpa only [Category.assoc, relative, pullback.lift_snd] using hr

instance mappingPath_kan {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) : SSet.KanComplex (MappingPath f) := by
  let : HomotopicalAlgebra.Fibration (right f) := by
    rw [HomotopicalAlgebra.fibration_iff, fibrations_eq]
    exact right_fibration f
  exact HomotopicalAlgebra.isFibrant_of_fibration (right f)

lemma right_heq {A B : SSet.{u}} (f : A ⟶ B) (hf : IsHomotopyEquivalence f) :
    IsHomotopyEquivalence (right f) :=
  heq_of_precomp (left f) (right f) (left_heq f) (by simpa using hf)

lemma right_rlp {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (hf : IsHomotopyEquivalence f) :
    (MorphismProperty.monomorphisms SSet).rlp (right f) :=
  rlp_of_homotopy_equivalence (right f) (right_fibration f) (right_heq f hf)

lemma relative_rlp {A₁ A₀ B₁ B₀ : SSet.{u}}
    [SSet.KanComplex A₁] [SSet.KanComplex A₀] [SSet.KanComplex B₁] [SSet.KanComplex B₀]
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) (ha : simplicialFibrations a) (hb : simplicialFibrations b)
    (hf₁ : IsHomotopyEquivalence f₁) (hf₀ : IsHomotopyEquivalence f₀) :
    (MorphismProperty.monomorphisms SSet).rlp (relative a b w) := by
  have hp : (MorphismProperty.monomorphisms SSet).rlp (pullback.snd (right f₀) b) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (right f₀) b) (right_rlp f₀ hf₀)
  have hp' : simplicialFibrations (pullback.snd (right f₀) b) := by
    change J.rlp _
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback (right f₀) b)
      (right_fibration f₀)
  let : HomotopicalAlgebra.Fibration (pullback.snd (right f₀) b) := by
    rw [HomotopicalAlgebra.fibration_iff, fibrations_eq]
    exact hp'
  let : SSet.KanComplex (Matching f₀ b) :=
    HomotopicalAlgebra.isFibrant_of_fibration (pullback.snd (right f₀) b)
  have hq : IsHomotopyEquivalence (relative a b w) :=
    heq_of_postcomp _ (pullback.snd (right f₀) b) (heq_of_rlp _ hp)
      (by simpa only [relative, pullback.lift_snd] using right_heq f₁ hf₁)
  exact rlp_of_homotopy_equivalence _ (relative_fibration a b w ha hb) hq

end Thomason.KanPath

end

noncomputable section
universe u v w z


namespace Thomason.KanTower
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy KanLocal KanPath
open SSet.modelCategoryQuillen

abbrev edge (n : ℕ) : op (n + 1) ⟶ op n := (homOfLE (Nat.le_succ n)).op

def cone (F : ℕᵒᵖ ⥤ SSet.{u}) {Z : SSet.{u}} (p : ∀ n, Z ⟶ F.obj (op n))
    (hp : ∀ n, p (n+1) ≫ F.map (edge n) = p n) : Cone F := by
  have H (m n : ℕ) (h : m ≤ n) : p n ≫ F.map (homOfLE h).op = p m := by
    induction n, h using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have e : (homOfLE (Nat.le.step hn)).op = edge n ≫ (homOfLE hn).op := Subsingleton.elim _ _
      rw [e, F.map_comp, ← Category.assoc, hp, ih]
  refine ⟨Z, ⟨fun n => p n.unop, ?_⟩⟩
  intro n m f
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
  exact (H m.unop n.unop (leOfHom f.unop)).symm

@[simp] lemma cone_π (F : ℕᵒᵖ ⥤ SSet.{u}) {Z : SSet.{u}} (p : ∀ n, Z ⟶ F.obj (op n))
    (hp : ∀ n, p (n+1) ≫ F.map (edge n) = p n) (n : ℕ) :
    (cone F p hp).π.app (op n) = p n := rfl

section
variable (F G : ℕᵒᵖ ⥤ SSet.{u}) (f : F ⟶ G)

abbrev limMap : limit F ⟶ limit G := lim.map f

def stage (n : ℕ) : MappingPath (limMap F G f) ⟶ MappingPath (f.app (op n)) :=
  KanPath.map (limit.π F (op n)) (limit.π G (op n)) (by simp)

def transition (n : ℕ) : MappingPath (f.app (op (n+1))) ⟶ MappingPath (f.app (op n)) :=
  KanPath.map (F.map (edge n)) (G.map (edge n)) (f.naturality (edge n))

@[reassoc (attr := simp)] lemma stage_fst (n : ℕ) :
    stage F G f n ≫ pullback.fst _ _ = pullback.fst _ _ ≫ limit.π F (op n) := by
  simp [stage]
@[reassoc (attr := simp)] lemma stage_snd (n : ℕ) :
    stage F G f n ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (ihom Δ[1]).map (limit.π G (op n)) := by
  simp [stage]
@[reassoc (attr := simp)] lemma stage_right (n : ℕ) :
    stage F G f n ≫ right (f.app (op n)) = right (limMap F G f) ≫ limit.π G (op n) := by
  simp [stage]

@[reassoc (attr := simp)] lemma transition_fst (n : ℕ) :
    transition F G f n ≫ pullback.fst _ _ = pullback.fst _ _ ≫ F.map (edge n) := by
  simp [transition]
@[reassoc (attr := simp)] lemma transition_snd (n : ℕ) :
    transition F G f n ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (ihom Δ[1]).map (G.map (edge n)) := by
  simp [transition]

@[reassoc] lemma stage_transition (n : ℕ) :
    stage F G f (n+1) ≫ transition F G f n = stage F G f n := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, transition_snd, stage_snd_assoc, stage_snd,
      ← Functor.map_comp, limit.w]

end
end Thomason.KanTower

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetalColimits
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Posetal Colimits. -/

noncomputable section
universe u v w z


namespace Thomason.SubdividedUnit
open CategoryTheory Limits Simplicial PartialOrder
open Subdivision AttachmentComparison

abbrev D := SSet.sd.{u} ⋙ SSet.sd

end Thomason.SubdividedUnit

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetalReduction
attribute [-instance] _root_.OAI.Thomason.GeometricRecognition.Mesh.finiteChains _root_.OAI.Thomason.GeometricRecognition.PolyPoint.finiteBoundedFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Posetal Reduction. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.KanLocal
open LastVertexProof

def transpose {A B K : SSet.{u}} (f : A ⟶ (ihom B).obj K) : B ⟶ (ihom A).obj K :=
  curry ((β_ A B).hom ≫ uncurry f)

lemma transpose_transpose {A B K : SSet.{u}} (f : A ⟶ (ihom B).obj K) :
    transpose (transpose f) = f := by
  dsimp only [transpose]
  rw [uncurry_curry, ← Category.assoc]
  have h := SymmetricCategory.symmetry B A
  rw [h,Category.id_comp,curry_uncurry]

lemma transpose_homotopic {A B K : SSet.{u}} {f g : A ⟶ (ihom B).obj K}
    (H : Homotopic f g) : Homotopic (transpose f) (transpose g) :=
  homotopic_curry (homotopic_pre _ (homotopic_uncurry H))

lemma transpose_pre {A B C K : SSet.{u}} (f : A ⟶ (ihom B).obj K) (i : C ⟶ A) :
    transpose (i ≫ f) = transpose f ≫ (pre i).app K := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [transpose,uncurry_curry,uncurry_natural_left]
  rw [← Category.assoc,← BraidedCategory.braiding_naturality_left,Category.assoc]

lemma transpose_post {A B C K : SSet.{u}} (f : A ⟶ (ihom B).obj K) (i : C ⟶ B) :
    transpose (f ≫ (pre i).app K) = i ≫ transpose f := by
  have he := transpose_pre (transpose f) i
  have hh := congrArg (@transpose A C K) he
  simpa only [transpose_transpose] using hh.symm

lemma local_of_homotopy_classes {A B : SSet.{u}} (f : A ⟶ B)
    (hs : ∀ (K : SSet.{u}) [SSet.KanComplex K] (a : A ⟶ K),
      ∃ b : B ⟶ K, Homotopic (f ≫ b) a)
    (hi : ∀ (K : SSet.{u}) [SSet.KanComplex K] (a b : B ⟶ K),
      Homotopic (f ≫ a) (f ≫ b) → Homotopic a b) : Local f := by
  intro K hK
  let U := (ihom B).obj K
  let V := (ihom A).obj K
  let m : U ⟶ V := (pre f).app K
  obtain ⟨b,hb⟩ := hs ((ihom V).obj K) (transpose (𝟙 V))
  let g : V ⟶ U := transpose b
  have hg : Homotopic (g ≫ m) (𝟙 V) := by
    have h := transpose_homotopic hb
    simpa only [transpose_pre,transpose_transpose] using h
  have hmg : Homotopic (f ≫ transpose (m ≫ g)) (f ≫ transpose (𝟙 U)) := by
    have h := transpose_homotopic (homotopic_pre m hg)
    simpa only [← transpose_post, Category.assoc,Category.comp_id,Category.id_comp] using h
  have hgm := transpose_homotopic (hi ((ihom U).obj K) _ _ hmg)
  refine ⟨g, ?_, hg⟩
  simpa only [transpose_transpose] using hgm

lemma lastVertex_local (X : SSet.{u}) : Local (Subdivision.lastVertex.app X) :=
  local_of_homotopy_classes _ (fun K _ => precomp_lastVertex_surjective X K)
    (fun K _ => precomp_lastVertex_injective X K)

end Thomason.KanLocal

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplicialApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplicial Approximation. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.PolyPoint
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
local instance polyMapsDecEqQ : DecidableEq Q := Classical.decEq Q

local instance polyMapsDecEqP_rced991_1 : DecidableEq P := Classical.decEq P
def vertex (p : P) : PolyPoint P where
  weights := Finsupp.single p 1
  nonneg q := by simp [Finsupp.single_apply]; positivity
  total := by simp
  chain := by simp

@[simp] lemma vertex_weights (p q : P) : (vertex p).weights q = if p = q then 1 else 0 := by
  simp [vertex, Finsupp.single_apply]

@[simp] lemma vertex_support (p : P) : (vertex p).weights.support = {p} := by
  simp [vertex]

@[simp] lemma barycenter_support (s : NonemptyFiniteChains P) :
    (barycenter s).weights.support = s.finset := by
  ext p
  rw [Finsupp.mem_support_iff, barycenter_apply]
  split_ifs with hp
  · simp only [hp, iff_true]
    exact inv_ne_zero (by exact_mod_cast Finset.card_ne_zero.mpr s.nonempty)
  · simp [hp]

def PreservesChains (f : P → Q) : Prop :=
  ∀ s : NonemptyFiniteChains P, IsChain (· ≤ ·) ((s.finset.image f : Finset Q) : Set Q)

lemma preservesChains_monotone (f : P →o Q) : PreservesChains f := by
  intro s a ha b hb hab
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hb
  exact (s.comparable ⟨p,hp⟩ ⟨q,hq⟩).imp
    (fun h => f.monotone (show p ≤ q from h))
    (fun h => f.monotone (show q ≤ p from h))

def map (f : P → Q) (hf : PreservesChains f) (x : PolyPoint P) : PolyPoint Q where
  weights := x.weights.mapDomain f
  nonneg q := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    apply Finset.sum_nonneg
    intro p hp
    simp only [Finsupp.single_apply]
    split_ifs <;> first | exact x.nonneg p | exact le_rfl
  total := by
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact x.total
  chain := by
    exact IsChain.mono Finsupp.mapDomain_support
      (hf ⟨x.weights.support, (supportIndex x).nonempty,
        fun p q => x.chain.total p.property q.property⟩)

lemma map_support (f : P → Q) (hf : PreservesChains f) (x : PolyPoint P) :
    (map f hf x).weights.support ⊆ x.weights.support.image f := Finsupp.mapDomain_support

lemma map_apply (f : P → Q) (hf : PreservesChains f) (x : PolyPoint P) (q : Q) :
    (map f hf x).weights q = x.weights.sum (fun p r => if f p = q then r else 0) := by
  simp only [map, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]

lemma continuous_map (f : P → Q) (hf : PreservesChains f) : Continuous (map f hf) := by
  rw [continuous_coinduced_dom]
  apply continuous_sigma
  intro s
  apply continuous_of_finite_carrier
    (fun x : Face s.carrier => map f hf x.val) (s.carrier.image f)
  · intro x q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (map_support f hf x.val hq)
    exact Finset.mem_image.mpr ⟨p,x.property hp,rfl⟩
  · intro q
    have he (x : Face s.carrier) : (map f hf x.val).weights q =
        ∑ p ∈ s.carrier, if f p = q then x.val.weights p else 0 := by
      rw [map_apply]
      exact Finsupp.sum_of_support_subset _ x.property _ (by simp)
    apply Continuous.congr _ (fun x => (he x).symm)
    apply continuous_finsetSum
    intro p hp
    by_cases h : f p = q
    · simpa only [h, ite_true, Function.comp_def] using
        ((continuous_apply p).comp continuous_induced_dom :
          Continuous (fun x : Face s.carrier => x.val.weights p))
    · simp only [h, ite_false]
      exact continuous_const

@[simp] lemma map_vertex (f : P → Q) (hf : PreservesChains f) (p : P) :
    map f hf (vertex p) = vertex (f p) := by
  apply PolyPoint.ext
  simp [map,vertex]

def segment (x y : PolyPoint P)
    (h : IsChain (· ≤ ·) ((x.weights.support ∪ y.weights.support : Finset P) : Set P))
    (t : unitInterval) : PolyPoint P where
  weights := (1 - t.val) • x.weights + t.val • y.weights
  nonneg p := by
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (x.nonneg p))
      (mul_nonneg t.property.1 (y.nonneg p))
  total := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_smul_index (fun _ => rfl), Finsupp.sum_smul_index (fun _ => rfl)]
    have hx : ∑ p ∈ x.weights.support, x.weights p = 1 := x.total
    have hy : ∑ p ∈ y.weights.support, y.weights p = 1 := y.total
    change (∑ p ∈ x.weights.support, (1 - t.val) * x.weights p) +
      (∑ p ∈ y.weights.support, t.val * y.weights p) = 1
    rw [← Finset.mul_sum, ← Finset.mul_sum, hx, hy]
    ring
  chain := IsChain.mono (by
    intro p hp
    rcases Finset.mem_union.mp (Finsupp.support_add hp) with hp | hp
    · exact Finset.mem_union_left _ (Finsupp.support_smul hp)
    · exact Finset.mem_union_right _ (Finsupp.support_smul hp)) h

@[simp] lemma segment_zero (x y : PolyPoint P) (h) : segment x y h 0 = x := by
  apply PolyPoint.ext
  simp [segment]

@[simp] lemma segment_one (x y : PolyPoint P) (h) : segment x y h 1 = y := by
  apply PolyPoint.ext
  simp [segment]

lemma exists_greatest (s : NonemptyFiniteChains P) :
    ∃ p ∈ s.finset, ∀ q ∈ s.finset, q ≤ p := by
  obtain ⟨p,hp,hm⟩ := s.finset.exists_maximal s.nonempty
  refine ⟨p,hp,fun q hq => ?_⟩
  rcases s.comparable ⟨q,hq⟩ ⟨p,hp⟩ with h | h
  · exact h
  · exact hm hq h

def greatest (s : NonemptyFiniteChains P) : P := (exists_greatest s).choose

lemma greatest_mem (s : NonemptyFiniteChains P) : greatest s ∈ s.finset :=
  (exists_greatest s).choose_spec.1

lemma le_greatest (s : NonemptyFiniteChains P) (p : P) (hp : p ∈ s.finset) :
    p ≤ greatest s := (exists_greatest s).choose_spec.2 p hp

lemma greatest_mono {s t : NonemptyFiniteChains P} (h : s ≤ t) :
    greatest s ≤ greatest t := le_greatest t _ (h (greatest_mem s))

end Thomason.GeometricRecognition.PolyPoint

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Approximation
open PolyPoint Mesh
variable {P : Type u} [PartialOrder P]

local instance approximationDecEqP_rced991_1 : DecidableEq P := Classical.decEq P
def affineMap {A : Type*} [PartialOrder A] {Q : Type*} [PartialOrder Q]
    (a : A →o Q) : C(PolyPoint A, PolyPoint Q) :=
  ⟨PolyPoint.map a (preservesChains_monotone a), continuous_map _ _⟩

end Approximation
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Contiguity
open PolyPoint Mesh Approximation
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

local instance instDecidableEq_solutions_rced991_1 : DecidableEq Q := Classical.decEq Q
def last (P : PartOrd.{u}) : (n : ℕ) → level P n →o P
  | 0 => OrderHom.id
  | n+1 => (last P n).comp ⟨greatest,fun _ _ h => greatest_mono h⟩

end Contiguity
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RelativeContiguity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Contiguity. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.PolyPoint
variable {P : Type u} [PartialOrder P]

def restrict (B : Set P) (x : PolyPoint P) (hx : ∀ p ∈ x.weights.support, p ∈ B) :
    PolyPoint B where
  weights := x.weights.subtypeDomain (· ∈ B)
  nonneg p := x.nonneg p.val
  total := (Finsupp.sum_subtypeDomain_index hx).trans x.total
  chain := by
    intro a ha b hb hab
    have ha' : a.val ∈ x.weights.support := by
      simpa only [Finset.mem_coe,Finsupp.mem_support_iff,Finsupp.subtypeDomain_apply] using ha
    have hb' : b.val ∈ x.weights.support := by
      simpa only [Finset.mem_coe,Finsupp.mem_support_iff,Finsupp.subtypeDomain_apply] using hb
    exact x.chain.total ha' hb'

def inclusion (B : Set P) : B →o P := ⟨Subtype.val,fun _ _ h => h⟩

lemma map_subtype_restrict (B : Set P) (x : PolyPoint P) (hx) :
    map (inclusion B) (preservesChains_monotone (inclusion B)) (restrict B x hx) = x := by
  classical
  apply PolyPoint.ext
  change (x.weights.subtypeDomain (· ∈ B)).mapDomain Subtype.val = x.weights
  calc
    _ = (x.weights.subtypeDomain (· ∈ B)).embDomain (Function.Embedding.subtype (· ∈ B)) :=
      (Finsupp.embDomain_eq_mapDomain (Function.Embedding.subtype (· ∈ B)) _).symm
    _ = (x.weights.subtypeDomain (· ∈ B)).extendDomain :=
      (Finsupp.extendDomain_eq_embDomain_subtype _).symm
    _ = x.weights := Finsupp.extendDomain_subtypeDomain _ hx

lemma map_injective {Q : Type*} [PartialOrder Q] (f : P →o Q)
    (hf : Function.Injective f) : Function.Injective (map f (preservesChains_monotone f)) := by
  intro x y he
  exact PolyPoint.ext (Finsupp.mapDomain_injective hf (congrArg PolyPoint.weights he))

lemma map_subtype_support (B : Set P) (x : PolyPoint B) :
    ∀ p ∈ (map (inclusion B) (preservesChains_monotone (inclusion B)) x).weights.support, p ∈ B := by
  classical
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp (map_support _ _ x hp)
  exact q.property

end Thomason.GeometricRecognition.PolyPoint

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision

lemma pre_fibration {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (K : SSet.{u}) [SSet.KanComplex K] : simplicialFibrations ((pre i).app K) := by
  rw [show simplicialFibrations = SSet.modelCategoryQuillen.J.rlp from rfl,
    ← SSet.modelCategoryQuillen.fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
  infer_instance

lemma path_const_natural {A B : SSet.{u}} (f : A ⟶ B) :
    const A ≫ (ihom Δ[1]).map f = f ≫ const B := by
  apply uncurryR_injective
  rw [uncurryR_post]
  simp only [uncurryR_pre,const,uncurryR_curryR,whiskerRight_fst]

lemma endsMap_comp {A B C : SSet.{u}} (f g : A ⟶ B) (h : B ⟶ C) :
    SimplicialCylinder.endsMap f g ≫ h = SimplicialCylinder.endsMap (f ≫ h) (g ≫ h) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  cases x <;> rfl

lemma endsInclusion_comp {A B : SSet.{u}} (h : A ⊗ Δ[1] ⟶ B) :
    SimplicialCylinder.endsInclusion A ≫ h =
      SimplicialCylinder.endsMap (SSet.ι₀ ≫ h) (SSet.ι₁ ≫ h) := endsMap_comp _ _ _

lemma kan_square_relative_injective {A₁ A₀ B₁ B₀ D : SSet.{u}}
    [SSet.KanComplex A₁] [SSet.KanComplex A₀] [SSet.KanComplex B₁] [SSet.KanComplex B₀]
    {f₁ : A₁ ⟶ B₁} {f₀ : A₀ ⟶ B₀} (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀)
    (w : a ≫ f₀ = f₁ ≫ b) (ha : simplicialFibrations a) (hb : simplicialFibrations b)
    (hf₁ : IsHomotopyEquivalence f₁) (hf₀ : IsHomotopyEquivalence f₀)
    (x y : D ⟶ A₁) (z : D ⟶ A₀) (hx : x ≫ a = z) (hy : y ≫ a = z)
    (H : SSet.Homotopy (x ≫ f₁) (y ≫ f₁))
    (hH : H.h ≫ b = fst D Δ[1] ≫ z ≫ f₀) :
    ∃ G : SSet.Homotopy x y, G.h ≫ a = fst D Δ[1] ≫ z := by
  let t : D ⊗ Δ[1] ⟶ Matching f₀ b := pullback.lift
    (fst D Δ[1] ≫ z ≫ left f₀) H.h (by simpa only [Category.assoc,KanPath.fac] using hH.symm)
  let : HasLiftingProperty (SimplicialCylinder.endsInclusion D) (relative a b w) :=
    relative_rlp a b w ha hb hf₁ hf₀ _ (by infer_instance)
  have hl (v : D ⟶ A₁) : (v ≫ left f₁) ≫ map a b w = v ≫ a ≫ left f₀ := by
    apply pullback.hom_ext
    · simp only [Category.assoc,map_fst,left,pullback.lift_fst_assoc,pullback.lift_fst,
        Category.id_comp,Category.comp_id]
    · simp only [Category.assoc,map_snd,left,pullback.lift_snd_assoc,pullback.lift_snd,
        path_const_natural]
      rw [← Category.assoc f₁ b,← w]
      simp only [Category.assoc]
  let sq : CommSq (SimplicialCylinder.endsMap (x ≫ left f₁) (y ≫ left f₁))
      (SimplicialCylinder.endsInclusion D) (relative a b w) t := ⟨by
    apply pullback.hom_ext
    · simp only [relative,t,Category.assoc,pullback.lift_fst,endsMap_comp,endsInclusion_comp,
        SSet.ι₀_fst_assoc,SSet.ι₁_fst_assoc]
      congr 1
      · simpa only [Category.assoc,← hx] using hl x
      · simpa only [Category.assoc,← hy] using hl y
    · simp only [relative,t,Category.assoc,pullback.lift_snd,endsMap_comp,endsInclusion_comp,
        Category.assoc,KanPath.fac,H.h₀,H.h₁]⟩
  have h₀' : SSet.ι₀ ≫ sq.lift = x ≫ left f₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro d
    exact congrArg (fun h => h.app n (Sum.inl d)) sq.fac_left
  have h₁' : SSet.ι₁ ≫ sq.lift = y ≫ left f₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro d
    exact congrArg (fun h => h.app n (Sum.inr d)) sq.fac_left
  let g := sq.lift ≫ pullback.fst f₁ (eval₀ B₁)
  have h₀ : SSet.ι₀ ≫ g = x := by
    dsimp only [g]
    rw [← Category.assoc,h₀']
    simp only [Category.assoc,left,pullback.lift_fst,Category.comp_id]
  have h₁ : SSet.ι₁ ≫ g = y := by
    dsimp only [g]
    rw [← Category.assoc,h₁']
    simp only [Category.assoc,left,pullback.lift_fst,Category.comp_id]
  refine ⟨CoherentGluing.toHomotopy g h₀ h₁, ?_⟩
  have hh := congrArg (fun h => h ≫ pullback.fst (right f₀) b ≫
    pullback.fst f₀ (eval₀ B₀)) sq.fac_right
  change g ≫ a = _
  simpa only [relative,t,g,Category.assoc,pullback.lift_fst_assoc,pullback.lift_fst,
    map_fst,left,Category.comp_id] using hh
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

local instance relativeContiguityFaceDecidableEq_rced991_1 : DecidableEq Q := Classical.decEq Q
def constantOrder (A : Type u) [PartialOrder A] (q : Q) : A →o Q := ⟨fun _ => q,fun _ _ _ => le_rfl⟩

def BasedHomotopy {A X Y : SSet.{u}} (i : A ⟶ X) (c : A ⟶ Y) (f g : X ⟶ Y) : Prop :=
  ∃ H : SSet.Homotopy f g, (i ▷ Δ[1]) ≫ H.h = fst _ _ ≫ c

end Thomason.GeometricRecognition.Contiguity

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Subdivision Contiguity

lemma uncurry_homotopy_restriction {A B D K : SSet.{u}} (i : B ⟶ A)
    {f g : D ⟶ (ihom A).obj K} (H : SSet.Homotopy f g) (c : D ⟶ (ihom B).obj K)
    (hh : H.h ≫ (pre i).app K = fst D Δ[1] ≫ c) :
    (i ▷ D) ▷ Δ[1] ≫ (uncurryHomotopy H).h = fst (B ⊗ D) Δ[1] ≫ uncurry c := by
  change (i ▷ D) ▷ Δ[1] ≫ (α_ A D Δ[1]).hom ≫ uncurry H.h = _
  rw [associator_naturality_left_assoc,← uncurry_pre_app,hh,uncurry_natural_left]
  rw [← Category.assoc]
  have hp : (α_ B D Δ[1]).hom ≫ B ◁ fst D Δ[1] = fst (B ⊗ D) Δ[1] := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [hp]

lemma curry_homotopy_restriction {A B D K : SSet.{u}} (i : B ⟶ A)
    {f g : A ⊗ D ⟶ K} (H : SSet.Homotopy f g) (c : B ⊗ D ⟶ K)
    (hh : (i ▷ D) ▷ Δ[1] ≫ H.h = fst (B ⊗ D) Δ[1] ≫ c) :
    (curryHomotopy H).h ≫ (pre i).app K = fst D Δ[1] ≫ curry c := by
  apply uncurry_injective
  change uncurry (curry ((α_ A D Δ[1]).inv ≫ H.h) ≫ (pre i).app K) = _
  rw [uncurry_pre_app,uncurry_curry,uncurry_natural_left,uncurry_curry]
  have hn : i ▷ (D ⊗ Δ[1]) ≫ (α_ A D Δ[1]).inv =
      (α_ B D Δ[1]).inv ≫ i ▷ D ▷ Δ[1] := by
    simp
  rw [← Category.assoc,hn,Category.assoc,hh,← Category.assoc]
  congr 1

lemma pair_local_injective {A B A' B' D K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (j : B' ⟶ A') [Mono j]
    (f : A' ⟶ A) (g : B' ⟶ B) (w : j ≫ f = g ≫ i)
    (hf : Local f) (hg : Local g) (c : B ⊗ D ⟶ K) (a b : A ⊗ D ⟶ K)
    (ha : i ▷ D ≫ a = c) (hb : i ▷ D ≫ b = c)
    (H : SSet.Homotopy (f ▷ D ≫ a) (f ▷ D ≫ b))
    (hH : j ▷ D ▷ Δ[1] ≫ H.h = fst (B' ⊗ D) Δ[1] ≫ g ▷ D ≫ c) :
    ∃ G : SSet.Homotopy a b, i ▷ D ▷ Δ[1] ≫ G.h = fst (B ⊗ D) Δ[1] ≫ c := by
  have hs : (pre i).app K ≫ (pre g).app K = (pre f).app K ≫ (pre j).app K := by
    rw [← NatTrans.comp_app,← pre_map,← NatTrans.comp_app,← pre_map,w]
  have hc (v : A ⊗ D ⟶ K) (hv : i ▷ D ≫ v = c) :
      curry v ≫ (pre i).app K = curry c := by
    apply uncurry_injective
    simpa only [uncurry_pre_app,uncurry_curry] using hv
  let H' : SSet.Homotopy (curry a ≫ (pre f).app K) (curry b ≫ (pre f).app K) :=
    CoherentGluing.toHomotopy (curryHomotopy H).h
      (by have hh := (curryHomotopy H).h₀
          simpa only [curry_pre_app] using hh)
      (by have hh := (curryHomotopy H).h₁
          simpa only [curry_pre_app] using hh)
  have hH' : H'.h ≫ (pre j).app K = fst D Δ[1] ≫ curry c ≫ (pre g).app K := by
    change (curryHomotopy H).h ≫ (pre j).app K = _
    simpa only [curry_pre_app,Category.assoc] using
      curry_homotopy_restriction j H (g ▷ D ≫ c) hH
  obtain ⟨G,hG⟩ := kan_square_relative_injective ((pre i).app K) ((pre j).app K)
    hs (pre_fibration i K) (pre_fibration j K) (hf K inferInstance) (hg K inferInstance)
    (curry a) (curry b) (curry c) (hc a ha) (hc b hb) H' hH'
  let G' : SSet.Homotopy a b := CoherentGluing.toHomotopy (uncurryHomotopy G).h
    (by simpa only [uncurry_curry] using (uncurryHomotopy G).h₀)
    (by simpa only [uncurry_curry] using (uncurryHomotopy G).h₁)
  refine ⟨G',?_⟩
  change i ▷ D ▷ Δ[1] ≫ (uncurryHomotopy G).h = _
  simpa only [uncurry_curry] using uncurry_homotopy_restriction i G (curry c) hG
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RelativeRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Representation. -/

noncomputable section
universe u v w z
open CategoryTheory PartialOrder Simplicial MonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open PolyPoint Mesh Approximation Contiguity LastVertexProof KanLocal

lemma nerveOrderMap_mono {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) : Mono (nerveMap f.toFunctor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro x y h
  exact CategoryTheory.Functor.ext (fun i => hf (congrArg (fun z => z.obj i) h))

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath Contiguity HornSubdivision

lemma fill_rectangle_over {D E F : SSet.{u}} (p : E ⟶ F) (hp : simplicialFibrations p)
    {a b c d : D ⟶ E} (z : D ⟶ F) (bottom : SSet.Homotopy a b)
    (left : SSet.Homotopy a c) (right : SSet.Homotopy b d)
    (hbottom : bottom.h ≫ p = fst D Δ[1] ≫ z)
    (hleft : left.h ≫ p = fst D Δ[1] ≫ z)
    (hright : right.h ≫ p = fst D Δ[1] ≫ z) :
    ∃ G : SSet.Homotopy c d, G.h ≫ p = fst D Δ[1] ≫ z := by
  obtain ⟨Q,hQ,h₀,hpQ⟩ := cylinder_lift (SimplicialCylinder.endsInclusion D) p hp 1
    bottom.h (sides left.h right.h) (fst (D ⊗ Δ[1]) Δ[1] ≫ fst D Δ[1] ≫ z)
    (by rw [endpoint_sides,endpoint_zero,left.h₀,right.h₀,ends_pre,bottom.h₀,bottom.h₁])
    (by rw [endpoint_zero,SSet.ι₀_fst_assoc,hbottom])
    (by rw [ends_sides_post,hleft,hright]
        ext n x
        rcases x with ⟨x,t⟩
        cases x <;> rfl)
  refine ⟨CoherentGluing.toHomotopy (SSet.ι₁ ≫ Q)
    ((square_top_zero Q left.h right.h hQ).trans left.h₁)
    ((square_top_one Q left.h right.h hQ).trans right.h₁),?_⟩
  change (SSet.ι₁ ≫ Q) ≫ p = _
  rw [Category.assoc,hpQ,SSet.ι₁_fst_assoc]

lemma fill_rectangle_relative_tensor {A B D K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] {a b c d : A ⊗ D ⟶ K} (z : B ⊗ D ⟶ K)
    (bottom : SSet.Homotopy a b) (left : SSet.Homotopy a c) (right : SSet.Homotopy b d)
    (hbottom : i ▷ D ▷ Δ[1] ≫ bottom.h = fst (B ⊗ D) Δ[1] ≫ z)
    (hleft : i ▷ D ▷ Δ[1] ≫ left.h = fst (B ⊗ D) Δ[1] ≫ z)
    (hright : i ▷ D ▷ Δ[1] ≫ right.h = fst (B ⊗ D) Δ[1] ≫ z) :
    ∃ G : SSet.Homotopy c d, i ▷ D ▷ Δ[1] ≫ G.h = fst (B ⊗ D) Δ[1] ≫ z := by
  obtain ⟨G,hG⟩ := fill_rectangle_over ((pre i).app K) (pre_fibration i K)
    (curry z) (curryHomotopy bottom) (curryHomotopy left) (curryHomotopy right)
    (curry_homotopy_restriction i bottom z hbottom)
    (curry_homotopy_restriction i left z hleft)
    (curry_homotopy_restriction i right z hright)
  let H := uncurryHomotopy G
  let H' : SSet.Homotopy c d := CoherentGluing.toHomotopy H.h
    (by simpa only [uncurry_curry] using H.h₀)
    (by simpa only [uncurry_curry] using H.h₁)
  refine ⟨H',?_⟩
  change i ▷ D ▷ Δ[1] ≫ (uncurryHomotopy G).h = _
  simpa only [uncurry_curry] using uncurry_homotopy_restriction i G (curry z) hG

lemma fill_rectangle_relative {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] {a b c d : A ⟶ K} (z : B ⟶ K)
    (bottom : SSet.Homotopy a b) (left : SSet.Homotopy a c) (right : SSet.Homotopy b d)
    (hbottom : i ▷ Δ[1] ≫ bottom.h = fst B Δ[1] ≫ z)
    (hleft : i ▷ Δ[1] ≫ left.h = fst B Δ[1] ≫ z)
    (hright : i ▷ Δ[1] ≫ right.h = fst B Δ[1] ≫ z) :
    ∃ G : SSet.Homotopy c d, i ▷ Δ[1] ≫ G.h = fst B Δ[1] ≫ z := by
  have hh {f g : A ⟶ K} (H : SSet.Homotopy f g)
      (hH : i ▷ Δ[1] ≫ H.h = fst B Δ[1] ≫ z) :
      i ▷ (𝟙_ SSet) ▷ Δ[1] ≫ (homotopy_pre (ρ_ A).hom H).h =
        fst (B ⊗ (𝟙_ SSet)) Δ[1] ≫ (ρ_ B).hom ≫ z := by
    change i ▷ (𝟙_ SSet) ▷ Δ[1] ≫ (ρ_ A).hom ▷ Δ[1] ≫ H.h = _
    rw [← comp_whiskerRight_assoc,rightUnitor_naturality,comp_whiskerRight_assoc,
      hH,whiskerRight_fst_assoc]
  obtain ⟨G,hG⟩ := fill_rectangle_relative_tensor i ((ρ_ B).hom ≫ z)
    (homotopy_pre (ρ_ A).hom bottom) (homotopy_pre (ρ_ A).hom left)
    (homotopy_pre (ρ_ A).hom right) (hh bottom hbottom) (hh left hleft) (hh right hright)
  let G' : SSet.Homotopy c d := CoherentGluing.toHomotopy
    ((ρ_ A).inv ▷ Δ[1] ≫ G.h)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,Category.assoc,Iso.inv_hom_id_assoc]
      using (homotopy_pre (ρ_ A).inv G).h₀)
    (by simpa only [homotopy_pre,CoherentGluing.toHomotopy,Category.assoc,Iso.inv_hom_id_assoc]
      using (homotopy_pre (ρ_ A).inv G).h₁)
  refine ⟨G',?_⟩
  change i ▷ Δ[1] ≫ (ρ_ A).inv ▷ Δ[1] ≫ G.h = _
  rw [← comp_whiskerRight_assoc,rightUnitor_inv_naturality,comp_whiskerRight_assoc,
    hG,whiskerRight_fst_assoc]
  simp only [Iso.inv_hom_id_assoc]

lemma based_homotopy_symm {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (z : B ⟶ K) {a b : A ⟶ K}
    (H : BasedHomotopy i z a b) : BasedHomotopy i z b a := by
  obtain ⟨H,hH⟩ := H
  have ha : i ≫ a = z := by
    have hh := congrArg (fun q => SSet.ι₀ ≫ q) hH
    simpa only [SSet.ι₀_comp_assoc,H.h₀,SSet.ι₀_fst_assoc] using hh
  exact fill_rectangle_relative i z (refl a) H (refl a)
    (by change i ▷ Δ[1] ≫ fst A Δ[1] ≫ a = _; rw [whiskerRight_fst_assoc,ha]) hH
    (by change i ▷ Δ[1] ≫ fst A Δ[1] ≫ a = _; rw [whiskerRight_fst_assoc,ha])

lemma based_homotopy_trans {A B K : SSet.{u}} [SSet.KanComplex K]
    (i : B ⟶ A) [Mono i] (z : B ⟶ K) {a b c : A ⟶ K}
    (H : BasedHomotopy i z a b) (H' : BasedHomotopy i z b c) : BasedHomotopy i z a c := by
  obtain ⟨H,hH⟩ := H
  obtain ⟨H',hH'⟩ := H'
  have ha : i ≫ a = z := by
    have hh := congrArg (fun q => SSet.ι₀ ≫ q) hH
    simpa only [SSet.ι₀_comp_assoc,H.h₀,SSet.ι₀_fst_assoc] using hh
  exact fill_rectangle_relative i z H (refl a) H' hH
    (by change i ▷ Δ[1] ≫ fst A Δ[1] ≫ a = _; rw [whiskerRight_fst_assoc,ha]) hH'
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh

lemma based_homotopy_refl {A B K : SSet.{u}} (i : B ⟶ A) (z : B ⟶ K)
    (a : A ⟶ K) (ha : i ≫ a = z) : BasedHomotopy i z a a := by
  refine ⟨refl a,?_⟩
  change i ▷ Δ[1] ≫ fst A Δ[1] ≫ a = _
  rw [whiskerRight_fst_assoc,ha]

lemma based_homotopy_post {A B K L : SSet.{u}} (i : B ⟶ A) (z : B ⟶ K)
    {a b : A ⟶ K} (H : BasedHomotopy i z a b) (f : K ⟶ L) :
    BasedHomotopy i (z ≫ f) (a ≫ f) (b ≫ f) := by
  obtain ⟨H,hH⟩ := H
  refine ⟨homotopy_post H f,?_⟩
  change i ▷ Δ[1] ≫ H.h ≫ f = _
  rw [← Category.assoc,hH,Category.assoc]

structure PairRefinement (P B : PartOrd.{u}) (i : B →o P) where
  R : PartOrd.{u}
  S : PartOrd.{u}
  finiteR : Finite R
  finiteS : Finite S
  j : S →o R
  injective : Function.Injective j
  l : R →o P
  k : S →o B
  square : l.comp j = i.comp k
  local_l : Local (nerveMap l.toFunctor)
  local_k : Local (nerveMap k.toFunctor)
  home : PolyPoint R ≃ₜ PolyPoint P
  homeB : PolyPoint S ≃ₜ PolyPoint B
  natural : ∀ x, home (map j (preservesChains_monotone j) x) =
    map i (preservesChains_monotone i) (homeB x)

attribute [instance] PairRefinement.finiteR PairRefinement.finiteS

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh

@[reassoc]
lemma exSequence_zero_inclusion (X : SSet.{u}) (n : ℕ) :
    (exSequence X).map (homOfLE (Nat.zero_le n)) ≫ exInfinityInclusion X n =
      exInfinityComparison X := colimit.w _ _

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CubicalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubical Geometry. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition.Cubical
open PolyPoint
variable {I : Type u} [Fintype I] [LinearOrder I]
local instance cubeDecEqFaces : DecidableEq (Finset I) := Classical.decEq _
local instance cubeFintypeChains : Fintype (NonemptyFiniteChains I) := Fintype.ofFinite _

def chain (s : Finset I) (hs : s.Nonempty) : NonemptyFiniteChains I :=
  ⟨s,hs,fun p q => le_total p.val q.val⟩

def allFacesEquiv : Option (NonemptyFiniteChains I) ≃ Finset I where
  toFun s := s.elim ∅ NonemptyFiniteChains.finset
  invFun s := if hs : s.Nonempty then some (chain s hs) else none
  left_inv s := by
    cases s with
    | none => simp
    | some s =>
      change (if hs : s.finset.Nonempty then some (chain s.finset hs) else none) = some s
      rw [dite_eq_left s.nonempty]
      exact congrArg some (NonemptyFiniteChains.ext rfl)
  right_inv s := by
    dsimp
    split_ifs with hs
    · rfl
    · exact (Finset.not_nonempty_iff_eq_empty.mp hs).symm

lemma sum_faces (f : Finset I → ℝ) :
    ∑ s, f s = f ∅ + ∑ s : NonemptyFiniteChains I, f s.finset := by
  rw [← allFacesEquiv.sum_comp]
  exact Fintype.sum_option _

def compress (w : Finset I →₀ ℝ) : NonemptyFiniteChains I →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm (fun s => w s.finset * (s.finset.card : ℝ))

@[simp] lemma compress_apply (w : Finset I →₀ ℝ) (s : NonemptyFiniteChains I) :
    compress w s = w s.finset * (s.finset.card : ℝ) := rfl

omit [Fintype I] in
lemma card_pos (s : NonemptyFiniteChains I) : 0 < (s.finset.card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr s.nonempty

lemma compress_mem_support (w : Finset I →₀ ℝ) (s : NonemptyFiniteChains I) :
    s ∈ (compress w).support ↔ s.finset ∈ w.support := by
  simp only [Finsupp.mem_support_iff,compress_apply]
  exact mul_ne_zero_iff.trans (and_iff_left (ne_of_gt (card_pos s)))

def coordinate (w : Finset I →₀ ℝ) (i : I) : ℝ :=
  ∑ s : Finset I, if i ∈ s then w s else 0

lemma compress_evaluate (w : Finset I →₀ ℝ) (i : I) :
    barycentricLinear (compress w) i = coordinate w i := by
  rw [barycentricLinear_apply, (compress w).sum_fintype (fun s r => r * (barycenter s).weights i) (by simp)]
  rw [coordinate,sum_faces]
  simp only [Finset.notMem_empty,ite_false,zero_add]
  apply Finset.sum_congr rfl
  intro s hs
  rw [compress_apply,barycenter_apply]
  split_ifs with hi
  · exact mul_inv_cancel_right₀ (ne_of_gt (card_pos s)) _
  · simp

lemma compress_nonneg (w : Finset I →₀ ℝ) (hn : ∀ s, 0 ≤ w s) :
    ∀ s, 0 ≤ compress w s := fun s => mul_nonneg (hn _) (le_of_lt (card_pos s))

lemma compress_chain (w : Finset I →₀ ℝ)
    (hc : IsChain (· ≤ ·) (w.support : Set (Finset I))) :
    IsChain (· ≤ ·) ((compress w).support : Set (NonemptyFiniteChains I)) := by
  intro s hs t ht hst
  exact hc.total ((compress_mem_support w s).mp hs) ((compress_mem_support w t).mp ht)

omit [LinearOrder I] in
lemma sum_weights (x : PolyPoint (Finset I)) : ∑ s, x.weights s = 1 := by
  exact (x.weights.sum_fintype (fun _ r => r) (fun _ => rfl)).symm.trans x.total

lemma coordinate_nonneg (w : Finset I →₀ ℝ) (hn : ∀ s, 0 ≤ w s) (i : I) :
    0 ≤ coordinate w i := by
  apply Finset.sum_nonneg
  intro s hs
  split_ifs <;> first | exact hn s | exact le_rfl

lemma coordinate_le_sum (w : Finset I →₀ ℝ) (hn : ∀ s, 0 ≤ w s) (i : I) :
    coordinate w i ≤ ∑ s, w s := by
  apply Finset.sum_le_sum
  intro s hs
  split_ifs <;> first | exact le_rfl | exact hn s

def evaluate (x : PolyPoint (Finset I)) : I → unitInterval := fun i =>
  ⟨coordinate x.weights i,coordinate_nonneg _ x.nonneg i,
    (coordinate_le_sum _ x.nonneg i).trans (sum_weights x).le⟩

lemma continuous_evaluate : Continuous (@evaluate I _ _) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  apply continuous_finsetSum
  intro s hs
  by_cases hi : i ∈ s
  · simpa only [hi,ite_true] using (continuous_weights (P := Finset I) s)
  · simp only [hi,ite_false]
    exact continuous_const

lemma evaluate_injective : Function.Injective (@evaluate I _ _) := by
  intro x y he
  have hg : compress x.weights = compress y.weights := by
    apply barycentricLinear_injective_nonneg_flag _ _
      (compress_nonneg _ x.nonneg) (compress_nonneg _ y.nonneg)
      (compress_chain _ x.chain) (compress_chain _ y.chain)
    ext i
    rw [compress_evaluate,compress_evaluate]
    exact congrArg Subtype.val (congrFun he i)
  have hn (s : NonemptyFiniteChains I) : x.weights s.finset = y.weights s.finset := by
    have h := DFunLike.congr_fun hg s
    exact mul_right_cancel₀ (ne_of_gt (card_pos s)) h
  apply PolyPoint.ext
  ext s
  by_cases hs : s.Nonempty
  · exact hn (chain s hs)
  · have hxe := sum_weights x
    have hye := sum_weights y
    rw [sum_faces] at hxe hye
    have heq := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun a _ => hn a)
    rw [heq] at hxe
    have hs0 := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    linarith

def uncompress (g : NonemptyFiniteChains I →₀ ℝ) : Finset I →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm (fun s =>
    if hs : s.Nonempty then g (chain s hs) / (s.card : ℝ) else 0)

@[simp] lemma uncompress_empty (g : NonemptyFiniteChains I →₀ ℝ) :
    uncompress g ∅ = 0 := by simp [uncompress]

lemma uncompress_nonempty (g : NonemptyFiniteChains I →₀ ℝ)
    (s : Finset I) (hs : s.Nonempty) :
    uncompress g s = g (chain s hs) / (s.card : ℝ) := by
  simp only [uncompress,Finsupp.coe_equivFunOnFinite_symm,dite_eq_left hs]

lemma compress_uncompress (g : NonemptyFiniteChains I →₀ ℝ) :
    compress (uncompress g) = g := by
  ext s
  rw [compress_apply,uncompress_nonempty _ _ s.nonempty]
  have he : chain s.finset s.nonempty = s := NonemptyFiniteChains.ext rfl
  rw [he]
  exact div_mul_cancel₀ _ (ne_of_gt (card_pos s))

lemma uncompress_nonneg (g : NonemptyFiniteChains I →₀ ℝ) (hn : ∀ s, 0 ≤ g s) :
    ∀ s, 0 ≤ uncompress g s := by
  intro s
  by_cases hs : s.Nonempty
  · rw [uncompress_nonempty _ _ hs]
    exact div_nonneg (hn _) (Nat.cast_nonneg _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs,uncompress_empty]

lemma uncompress_support_nonempty (g : NonemptyFiniteChains I →₀ ℝ)
    {s : Finset I} (hs : s ∈ (uncompress g).support) : s.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty.mp h,Finsupp.mem_support_iff,uncompress_empty] at hs
  exact hs rfl

lemma uncompress_chain (g : NonemptyFiniteChains I →₀ ℝ)
    (hc : IsChain (· ≤ ·) (g.support : Set (NonemptyFiniteChains I))) :
    IsChain (· ≤ ·) ((uncompress g).support : Set (Finset I)) := by
  intro s hs t ht hst
  let a := chain s (uncompress_support_nonempty g hs)
  let b := chain t (uncompress_support_nonempty g ht)
  have ha : a ∈ g.support := by
    rw [← compress_uncompress g,compress_mem_support]
    exact hs
  have hb : b ∈ g.support := by
    rw [← compress_uncompress g,compress_mem_support]
    exact ht
  exact hc.total ha hb

lemma sum_le_one_of_coordinates (w : Finset I →₀ ℝ)
    (hc : IsChain (· ≤ ·) (w.support : Set (Finset I)))
    (he : w ∅ = 0) (hb : ∀ i, coordinate w i ≤ 1) : ∑ s, w s ≤ 1 := by
  by_cases hw : w = 0
  · subst w
    simp
  have hne := Finsupp.support_nonempty_iff.mpr hw
  obtain ⟨s,hs,hmin⟩ := Finset.exists_min_image w.support Finset.card hne
  have hsne : s.Nonempty := by
    by_contra h
    have hs0 := Finset.not_nonempty_iff_eq_empty.mp h
    exact (Finsupp.mem_support_iff.mp hs) (hs0 ▸ he)
  obtain ⟨i,hi⟩ := hsne
  have hmem (t : Finset I) (ht : t ∈ w.support) : i ∈ t := by
    rcases hc.total hs ht with hst | hts
    · exact hst hi
    · exact (Finset.eq_of_subset_of_card_le hts (hmin t ht)) ▸ hi
  have hcoord : coordinate w i = ∑ s, w s := by
    apply Finset.sum_congr rfl
    intro t ht
    by_cases htw : t ∈ w.support
    · simp only [hmem t htw,ite_true]
    · rw [Finsupp.notMem_support_iff.mp htw]
      split_ifs <;> rfl
  rw [← hcoord]
  exact hb i

lemma coordinate_add (a b : Finset I →₀ ℝ) (i : I) :
    coordinate (a+b) i = coordinate a i + coordinate b i := by
  simp only [coordinate,Finsupp.add_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs <;> simp

lemma coordinate_empty (r : ℝ) (i : I) :
    coordinate (Finsupp.single ∅ r) i = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi,Finsupp.single_eq_of_ne]
    intro h
    subst s
    exact Finset.notMem_empty i hi
  · rw [ite_eq_right hi]

lemma evaluate_surjective : Function.Surjective (@evaluate I _ _) := by
  intro x
  let f : I →₀ ℝ := Finsupp.equivFunOnFinite.symm (fun i => (x i).val)
  have hn : ∀ i, 0 ≤ f i := fun i => (x i).property.1
  have hc : IsChain (· ≤ ·) (f.support : Set I) :=
    fun i hi j hj hij => le_total i j
  obtain ⟨g,hgn,hgc,hgs,hgf⟩ := exists_barycentric_decomposition f hn hc
  let w := uncompress g
  have heval (i : I) : coordinate w i = (x i).val := by
    rw [← compress_evaluate,compress_uncompress,hgf]
    rfl
  have htotal : (∑ s, w s) ≤ 1 := sum_le_one_of_coordinates w
    (uncompress_chain g hgc) (uncompress_empty g) (fun i => by rw [heval]; exact (x i).property.2)
  let w' := w + Finsupp.single ∅ (1 - ∑ s, w s)
  have hmem (s : Finset I) (hs : s ∈ w'.support) : s ∈ w.support ∨ s = ∅ := by
    rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
    · exact Or.inl h
    · right
      by_contra hne
      exact (Finsupp.mem_support_iff.mp h) (Finsupp.single_eq_of_ne hne)
  let z : PolyPoint (Finset I) := {
    weights := w'
    nonneg s := by
      dsimp [w']
      rw [Finsupp.single_apply]
      apply add_nonneg (uncompress_nonneg g hgn s)
      split_ifs
      · exact sub_nonneg.mpr htotal
      · exact le_rfl
    total := by
      change (w + Finsupp.single ∅ (1 - ∑ s, w s)).sum (fun _ r => r) = 1
      rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl),
        Finsupp.sum_single_index (by rfl), w.sum_fintype (fun _ r => r) (fun _ => rfl)]
      ring
    chain := by
      intro s hs t ht hst
      rcases hmem s hs with hs | rfl
      · rcases hmem t ht with ht | rfl
        · exact (uncompress_chain g hgc).total hs ht
        · exact Or.inr (Finset.empty_subset s)
      · exact Or.inl (Finset.empty_subset t) }
  refine ⟨z,?_⟩
  funext i
  apply Subtype.ext
  change coordinate w' i = (x i).val
  rw [coordinate_add,coordinate_empty,add_zero,heval]

def cubeHomeomorph : PolyPoint (Finset I) ≃ₜ (I → unitInterval) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective evaluate ⟨evaluate_injective,evaluate_surjective⟩) continuous_evaluate

end Thomason.GeometricRecognition.Cubical

end

noncomputable section
universe u v w z
open PartialOrder
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition.Cubical
open PolyPoint
variable {I : Type u} [Fintype I] [LinearOrder I]
local instance instDecidableEqFinset_solutions : DecidableEq (Finset I) := Classical.decEq _

lemma coordinate_eq_zero_iff (x : PolyPoint (Finset I)) (i : I) :
    coordinate x.weights i = 0 ↔ ∀ s ∈ x.weights.support, i ∉ s := by
  rw [coordinate,Finset.sum_eq_zero_iff_of_nonneg (fun s _ => by
    split_ifs <;> first | exact x.nonneg s | exact le_rfl)]
  constructor
  · intro h s hs hi
    have hz := h s (Finset.mem_univ s)
    simp only [hi,ite_true] at hz
    exact (Finsupp.mem_support_iff.mp hs) hz
  · intro h s hs
    split_ifs with hi
    · by_contra hn
      exact h s (Finsupp.mem_support_iff.mpr hn) hi
    · rfl

lemma coordinate_eq_one_iff (x : PolyPoint (Finset I)) (i : I) :
    coordinate x.weights i = 1 ↔ ∀ s ∈ x.weights.support, i ∈ s := by
  have he : (∑ s : Finset I, if i ∉ s then x.weights s else 0) =
      1 - coordinate x.weights i := by
    rw [← sum_weights x,coordinate,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs <;> simp_all
  conv_lhs => rw [eq_comm,← sub_eq_zero,← he]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun s _ => by
    split_ifs <;> first | exact x.nonneg s | exact le_rfl)]
  constructor
  · intro h s hs
    by_contra hi
    have hz := h s (Finset.mem_univ s)
    simp only [hi] at hz
    exact (Finsupp.mem_support_iff.mp hs) hz
  · intro h s hs
    by_cases hi : i ∈ s
    · simp [hi]
    · have hz : x.weights s = 0 := by
        by_contra hn
        exact hi (h s (Finsupp.mem_support_iff.mpr hn))
      simp [hi,hz]

def boundaryFaces (I : Type u) [Fintype I] : Set (NonemptyFiniteChains (Finset I)) :=
  {s | ∃ i : I, (∀ v ∈ s.finset, i ∉ v) ∨ (∀ v ∈ s.finset, i ∈ v)}

omit [Fintype I] [LinearOrder I] in
lemma subdivide_support (x : PolyPoint (NonemptyFiniteChains (Finset I))) :
    (subdivide x).weights.support = x.weights.support.biUnion NonemptyFiniteChains.finset :=
  barycentricLinear_support_eq x.weights x.nonneg

lemma cube_boundary_iff (x : PolyPoint (Finset I)) :
    evaluate x ∈ Cube.boundary I ↔
      ∃ i : I, (∀ v ∈ x.weights.support, i ∉ v) ∨ (∀ v ∈ x.weights.support, i ∈ v) := by
  change (∃ i, evaluate x i = 0 ∨ evaluate x i = 1) ↔ _
  apply exists_congr
  intro i
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl ((coordinate_eq_zero_iff x i).mp (congrArg Subtype.val h))
    · exact Or.inr ((coordinate_eq_one_iff x i).mp (congrArg Subtype.val h))
  · intro h
    rcases h with h | h
    · exact Or.inl (Subtype.ext ((coordinate_eq_zero_iff x i).mpr h))
    · exact Or.inr (Subtype.ext ((coordinate_eq_one_iff x i).mpr h))

lemma subdivided_cube_boundary_iff (x : PolyPoint (NonemptyFiniteChains (Finset I))) :
    evaluate (subdivide x) ∈ Cube.boundary I ↔
      ∀ s ∈ x.weights.support, s ∈ boundaryFaces I := by
  rw [cube_boundary_iff,subdivide_support]
  constructor
  · rintro ⟨i,hi⟩ s hs
    exact ⟨i,hi.imp (fun hi v hv => hi v (Finset.mem_biUnion.mpr ⟨s,hs,hv⟩))
      (fun hi v hv => hi v (Finset.mem_biUnion.mpr ⟨s,hs,hv⟩))⟩
  · intro h
    let c : NonemptyFiniteChains (NonemptyFiniteChains (Finset I)) :=
      ⟨x.weights.support,(supportIndex x).nonempty,fun a b => x.chain.total a.property b.property⟩
    let t := greatest c
    obtain ⟨i,hi⟩ := h t (greatest_mem c)
    refine ⟨i,hi.imp ?_ ?_⟩
    · intro hi v hv
      obtain ⟨s,hs,hv⟩ := Finset.mem_biUnion.mp hv
      exact hi v ((le_greatest c s hs) hv)
    · intro hi v hv
      obtain ⟨s,hs,hv⟩ := Finset.mem_biUnion.mp hv
      exact hi v ((le_greatest c s hs) hv)
end Thomason.GeometricRecognition.Cubical

end

noncomputable section
universe u v w z
open PartialOrder
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition.Cubical
open PolyPoint
variable {I : Type u} [Fintype I] [LinearOrder I]

def pairCubeHomeomorph : PolyPoint (NonemptyFiniteChains (Finset I)) ≃ₜ (I → unitInterval) :=
  subdivisionHomeomorph.trans cubeHomeomorph

def boundaryEvaluate (x : PolyPoint (boundaryFaces I)) : Cube.boundary I :=
  ⟨evaluate (subdivide (map (inclusion (boundaryFaces I))
    (preservesChains_monotone (inclusion (boundaryFaces I))) x)),
    (subdivided_cube_boundary_iff _).mpr (map_subtype_support (boundaryFaces I) x)⟩

lemma boundaryEvaluate_injective : Function.Injective (@boundaryEvaluate I _ _) := by
  intro x y h
  apply map_injective (inclusion (boundaryFaces I)) Subtype.val_injective
  apply pairCubeHomeomorph.injective
  exact congrArg Subtype.val h

lemma boundaryEvaluate_surjective : Function.Surjective (@boundaryEvaluate I _ _) := by
  intro y
  let x := (pairCubeHomeomorph (I := I)).symm y.val
  have hx : ∀ s ∈ x.weights.support, s ∈ boundaryFaces I := by
    apply (subdivided_cube_boundary_iff x).mp
    change pairCubeHomeomorph x ∈ Cube.boundary I
    rw [show pairCubeHomeomorph x = y.val from pairCubeHomeomorph.apply_symm_apply y.val]
    exact y.property
  refine ⟨restrict (boundaryFaces I) x hx,?_⟩
  apply Subtype.ext
  change pairCubeHomeomorph (map (inclusion (boundaryFaces I))
    (preservesChains_monotone (inclusion (boundaryFaces I))) (restrict _ x hx)) = y.val
  rw [map_subtype_restrict]
  exact pairCubeHomeomorph.apply_symm_apply y.val

lemma continuous_boundaryEvaluate : Continuous (@boundaryEvaluate I _ _) := by
  apply Continuous.subtype_mk
  exact continuous_evaluate.comp (continuous_subdivide.comp (continuous_map _ _))

def boundaryHomeomorph : PolyPoint (boundaryFaces I) ≃ₜ Cube.boundary I :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective boundaryEvaluate
      ⟨boundaryEvaluate_injective,boundaryEvaluate_surjective⟩) continuous_boundaryEvaluate

end Thomason.GeometricRecognition.Cubical

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CubicalRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubical Recognition. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

def top_homotopy_rel_pre {A : Type u} {B : Type v} {X : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    {a b : C(A,X)} {S : Set A} (H : a.HomotopyRel b S)
    (f : C(B,A)) (T : Set B) (hf : ∀ x ∈ T, f x ∈ S) :
    (a.comp f).HomotopyRel (b.comp f) T where
  toHomotopy := H.toHomotopy.compContinuousMap f
  prop' := fun t x hx => H.prop t (f x) (hf x hx)

structure CubicalPair (P B : PartOrd.{u}) (i : B →o P) (n : ℕ) where
  home : PolyPoint P ≃ₜ (Fin (n+1) → unitInterval)
  boundary : ∀ a, a ∈ Set.range (map i (preservesChains_monotone i)) ↔
    home a ∈ Cube.boundary (Fin (n+1))

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Boxes. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation HornSubdivision

def boxBoundary (I : Type u) : (nerve (Finset I)).Subcomplex where
  obj k := {s | ∃ i : I, (∀ j, i ∉ s.obj j) ∨ (∀ j, i ∈ s.obj j)}
  map θ := by
    rintro s ⟨i,hi⟩
    exact ⟨i,hi.imp (fun h j => h _) (fun h j => h _)⟩

lemma mem_boxBoundary {I : Type u} [Fintype I] (k : ℕ)
    (s : (nerve (Finset I)) _⦋k⦌) :
    s ∈ (boxBoundary I).obj _ ↔ simplexChain s ∈ Cubical.boundaryFaces I := by
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨i,hi.imp ?_ ?_⟩
    · intro h v hv
      obtain ⟨j,rfl⟩ := (mem_simplexChain s v).mp hv
      exact h j
    · intro h v hv
      obtain ⟨j,rfl⟩ := (mem_simplexChain s v).mp hv
      exact h j
  · rintro ⟨i,hi⟩
    exact ⟨i,hi.imp (fun h j => h _ ((mem_simplexChain s _).mpr ⟨j,rfl⟩))
      (fun h j => h _ ((mem_simplexChain s _).mpr ⟨j,rfl⟩))⟩

lemma allowed_boxBoundary {I : Type u} [Fintype I] (c : NonemptyFiniteChains (Finset I)) :
    (∃ s : (boxBoundary I : SSet).N,
      simplexChain (subcomplexN (boxBoundary I) s).simplex = c) ↔ c ∈ Cubical.boundaryFaces I := by
  constructor
  · rintro ⟨s,rfl⟩
    exact (mem_boxBoundary s.dim s.simplex.val).mp s.simplex.property
  · intro hc
    let t := chainSimplex c
    have ht : t.simplex ∈ (boxBoundary I).obj _ := by
      rw [mem_boxBoundary,simplexChain_chainSimplex]
      exact hc
    let s : (boxBoundary I : SSet).N :=
      SSet.N.mk ⟨t.simplex,ht⟩ (((boxBoundary I).mem_nonDegenerate_iff _).mpr t.nonDegenerate)
    exact ⟨s,simplexChain_chainSimplex c⟩

def boxBoundaryFaceIso (I : Type u) [Fintype I] :
    AllowedChains (boxBoundary I) ≃o Cubical.boundaryFaces I where
  toFun c := ⟨c.val,(allowed_boxBoundary c.val).mp c.property⟩
  invFun c := ⟨c.val,(allowed_boxBoundary c.val).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def sdBoxBoundaryIso (I : Type u) [Fintype I] :
    SSet.sd.obj (boxBoundary I : SSet) ≅ nerve (Cubical.boundaryFaces I) :=
  sdSubcomplexIso (boxBoundary I) ≪≫ PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (AllowedChains (boxBoundary I)))
      (β := PartOrd.of (Cubical.boundaryFaces I)) (boxBoundaryFaceIso I))

lemma sd_box_boundary_square (I : Type u) [Fintype I] :
    SSet.sd.map (boxBoundary I).ι ≫ (sdNerveIso (E := Finset I)).hom =
      (sdBoxBoundaryIso I).hom ≫ nerveMap (inclusion (Cubical.boundaryFaces I)).toFunctor :=
  sdSubcomplexMap_naturality (boxBoundary I)

def boxPairProjection (I : Type u) : nerve (NonemptyFiniteChains (Finset I)) ⟶ nerve (Finset I) :=
  (sdNerveIso (E := Finset I)).inv ≫ lastVertex.app _
def boxBoundaryProjection (I : Type u) [Fintype I] :
    nerve (Cubical.boundaryFaces I) ⟶ (boxBoundary I : SSet) :=
  (sdBoxBoundaryIso I).inv ≫ lastVertex.app _

lemma box_pair_square (I : Type u) [Fintype I] :
    nerveMap (inclusion (Cubical.boundaryFaces I)).toFunctor ≫ boxPairProjection I =
      boxBoundaryProjection I ≫ (boxBoundary I).ι := by
  apply (cancel_epi (sdBoxBoundaryIso I).hom).mp
  simp only [boxPairProjection,boxBoundaryProjection,← Category.assoc]
  rw [← sd_box_boundary_square]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  exact lastVertex.naturality (boxBoundary I).ι

lemma boxPairProjection_local (I : Type u) : Local (boxPairProjection I) :=
  local_comp (local_iso _) (lastVertex_local _)
lemma boxBoundaryProjection_local (I : Type u) [Fintype I] : Local (boxBoundaryProjection I) :=
  local_comp (local_iso _) (lastVertex_local _)

instance boxBoundaryInclusion_mono (I : Type u) [Fintype I] :
    Mono (nerveMap (inclusion (Cubical.boundaryFaces I)).toFunctor) :=
  nerveOrderMap_mono _ Subtype.val_injective

def finiteBoxPair (I : Type u) [Fintype I] [LinearOrder I] (n : ℕ) (e : I ≃ Fin (n+1)) :
    CubicalPair (PartOrd.of (NonemptyFiniteChains (Finset I)))
      (PartOrd.of (Cubical.boundaryFaces I)) (inclusion (Cubical.boundaryFaces I)) n where
  home := Cubical.pairCubeHomeomorph.trans
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) e)
  boundary := by
    intro a
    have he : (Cubical.pairCubeHomeomorph (I := I)) a ∈ Cube.boundary I ↔
        (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) e)
          (Cubical.pairCubeHomeomorph a) ∈ Cube.boundary (Fin (n+1)) := by
      constructor
      · rintro ⟨j,hj⟩
        exact ⟨e j,by simpa using hj⟩
      · rintro ⟨j,hj⟩
        obtain ⟨i,rfl⟩ := e.surjective j
        exact ⟨i,by simpa only [Homeomorph.piCongrLeft_apply_apply] using hj⟩
    change _ ↔ (Homeomorph.piCongrLeft (Y := fun _ : Fin (n+1) => unitInterval) e)
      (Cubical.pairCubeHomeomorph a) ∈ Cube.boundary (Fin (n+1))
    rw [← he]
    constructor
    · rintro ⟨b,rfl⟩
      exact (Cubical.boundaryHomeomorph b).property
    · intro ha
      obtain ⟨b,hb⟩ := Cubical.boundaryHomeomorph.surjective ⟨_,ha⟩
      exact ⟨b,Cubical.pairCubeHomeomorph.injective (congrArg Subtype.val hb)⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation HornSubdivision

def bit (I : Type u) : Finset (Option I) →o Fin 2 := by
  classical
  refine ⟨fun s => if none ∈ s then 1 else 0,?_⟩
  intro s t h
  dsimp only
  split_ifs with hs ht ht <;> try omega
  exact False.elim (ht (h hs))

def pack (I : Type u) (s : Finset I) (t : Fin 2) : Finset (Option I) :=
  if t = 0 then s.map Function.Embedding.some else Finset.insertNone s

lemma some_mem_pack {I : Type u} (s : Finset I) (t : Fin 2) (i : I) :
    some i ∈ pack I s t ↔ i ∈ s := by
  classical
  simp only [pack]
  split_ifs <;> simp

lemma none_mem_pack {I : Type u} (s : Finset I) (t : Fin 2) :
    none ∈ pack I s t ↔ t = 1 := by
  classical
  fin_cases t <;> simp [pack]

def packOrder (I : Type u) : Finset I × Fin 2 →o Finset (Option I) where
  toFun st := pack I st.1 st.2
  monotone' := by
    intro s t h i hi
    cases i with
    | none =>
      rw [none_mem_pack] at hi ⊢
      have hh := h.2
      rw [hi] at hh
      omega
    | some i =>
      rw [some_mem_pack] at hi ⊢
      exact h.1 hi

lemma eraseNone_pack {I : Type u} (s : Finset I) (t : Fin 2) :
    Finset.eraseNone (pack I s t) = s := by
  ext i
  simp only [Finset.mem_eraseNone,some_mem_pack]

lemma bit_pack {I : Type u} (s : Finset I) (t : Fin 2) :
    bit I (pack I s t) = t := by
  classical
  change (if none ∈ pack I s t then (1 : Fin 2) else 0) = t
  fin_cases t <;> simp [none_mem_pack]

lemma pack_eraseNone_bit {I : Type u} (s : Finset (Option I)) :
    pack I (Finset.eraseNone s) (bit I s) = s := by
  classical
  ext i
  cases i with
  | none =>
    rw [none_mem_pack]
    change (if none ∈ s then (1 : Fin 2) else 0) = 1 ↔ none ∈ s
    simp
  | some i => simp only [some_mem_pack,Finset.mem_eraseNone]

def simplexOrder {P : Type u} [PartialOrder P] {n : ℕ}
    (s : (nerve P) _⦋n⦌) : Fin (n+1) →o P :=
  ⟨s.obj, fun _ _ h => leOfHom (s.map (homOfLE h))⟩

def boxToPrism (I : Type u) : nerve (Finset (Option I)) ⟶ nerve (Finset I) ⊗ Δ[1] where
  app n := TypeCat.ofHom fun s =>
    ⟨s ⋙ Finset.eraseNone.toFunctor, SSet.stdSimplex.objMk ((bit I).comp (simplexOrder s))⟩
  naturality n m θ := by
    ext s
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro j
      rfl

def prismToBox (I : Type u) : nerve (Finset I) ⊗ Δ[1] ⟶ nerve (Finset (Option I)) where
  app n := TypeCat.ofHom fun s =>
    ((packOrder I).comp ((simplexOrder s.1).prod (SSet.stdSimplex.asOrderHom s.2))).toFunctor
  naturality n m θ := by
    ext s j
    rfl

def boxPrismIso (I : Type u) : nerve (Finset (Option I)) ≅ nerve (Finset I) ⊗ Δ[1] where
  hom := boxToPrism I
  inv := prismToBox I
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    exact CategoryTheory.Functor.ext (h_obj := fun j => pack_eraseNone_bit (s.obj j))
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext
    · exact CategoryTheory.Functor.ext (h_obj := fun j =>
        eraseNone_pack (s.1.obj j) (SSet.stdSimplex.asOrderHom s.2 j))
    · apply SSet.stdSimplex.ext
      intro j
      exact bit_pack (s.1.obj j) (SSet.stdSimplex.asOrderHom s.2 j)

lemma prismToBox_side_mem (I : Type u) (n : ℕ)
    (s : (boxBoundary I : SSet) _⦋n⦌) (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    (prismToBox I).app _ (s.val,t) ∈ (boxBoundary (Option I)).obj _ := by
  obtain ⟨i,hi⟩ := s.property
  refine ⟨some i,hi.imp ?_ ?_⟩
  · intro h j
    change some i ∉ pack I (s.val.obj j) (SSet.stdSimplex.asOrderHom t j)
    simpa only [some_mem_pack] using h j
  · intro h j
    change some i ∈ pack I (s.val.obj j) (SSet.stdSimplex.asOrderHom t j)
    simpa only [some_mem_pack] using h j

lemma prismToBox_end_mem (I : Type u) (n : ℕ)
    (s : (nerve (Finset I)) _⦋n⦌) (t : Fin 2) :
    (prismToBox I).app _ (s,SSet.stdSimplex.const _ t _) ∈ (boxBoundary (Option I)).obj _ := by
  refine ⟨none,?_⟩
  fin_cases t
  · left
    intro j
    change none ∉ pack I (s.obj j) 0
    simp only [none_mem_pack]
    decide
  · right
    intro j
    change none ∈ pack I (s.obj j) 1
    exact (none_mem_pack _ _).mpr rfl

def prismBoxSide (I : Type u) : (boxBoundary I : SSet) ⊗ Δ[1] ⟶ (boxBoundary (Option I) : SSet) where
  app n := TypeCat.ofHom fun st => ⟨(prismToBox I).app n (st.1.val,st.2),
    prismToBox_side_mem I _ st.1 st.2⟩
  naturality _ _ _ := by ext; rfl

def prismBoxEnd (I : Type u) (t : Fin 2) : nerve (Finset I) ⟶ (boxBoundary (Option I) : SSet) where
  app n := TypeCat.ofHom fun s => ⟨(prismToBox I).app n (s,SSet.stdSimplex.const _ t _),
    prismToBox_end_mem I _ s t⟩
  naturality _ _ _ := by ext; rfl

lemma prismBoxSide_comp (I : Type u) :
    prismBoxSide I ≫ (boxBoundary (Option I)).ι =
      (boxBoundary I).ι ▷ Δ[1] ≫ prismToBox I := rfl
lemma prismBoxEnd_zero_comp (I : Type u) :
    prismBoxEnd I 0 ≫ (boxBoundary (Option I)).ι = SSet.ι₀ ≫ prismToBox I := rfl
lemma prismBoxEnd_one_comp (I : Type u) :
    prismBoxEnd I 1 ≫ (boxBoundary (Option I)).ι = SSet.ι₁ ≫ prismToBox I := rfl

lemma boxPrism_boundary_const (I : Type u) {K : SSet.{u}} (x : K _⦋0⦌)
    (F : nerve (Finset I) ⊗ Δ[1] ⟶ K)
    (hi : (boxBoundary I).ι ▷ Δ[1] ≫ F = SSet.const x)
    (h₀ : SSet.ι₀ ≫ F = SSet.const x) (h₁ : SSet.ι₁ ≫ F = SSet.const x) :
    (boxBoundary (Option I)).ι ≫ boxToPrism I ≫ F = SSet.const x := by
  classical
  ext n s
  obtain ⟨i,hi'⟩ := s.property
  let q := (boxToPrism I).app _ s.val
  change F.app _ q = _
  cases i with
  | some i =>
    have hq : q.1 ∈ (boxBoundary I).obj _ := by
      refine ⟨i,hi'.imp ?_ ?_⟩
      · intro h j
        change i ∉ Finset.eraseNone (s.val.obj j)
        simpa only [Finset.mem_eraseNone] using h j
      · intro h j
        change i ∈ Finset.eraseNone (s.val.obj j)
        simpa only [Finset.mem_eraseNone] using h j
    exact congrArg (fun f => f.app _ (⟨q.1,hq⟩,q.2)) hi
  | none =>
    rcases hi' with h | h
    · have he : q = SSet.ι₀.app _ q.1 := by
        apply Prod.ext
        · rfl
        apply SSet.stdSimplex.ext
        intro j
        change (if none ∈ s.val.obj j then (1 : Fin 2) else 0) = 0
        exact ite_eq_right (h j)
      rw [he]
      exact congrArg (fun f => f.app _ q.1) h₀
    · have he : q = SSet.ι₁.app _ q.1 := by
        apply Prod.ext
        · rfl
        apply SSet.stdSimplex.ext
        intro j
        change (if none ∈ s.val.obj j then (1 : Fin 2) else 0) = 1
        exact ite_eq_left (h j)
      rw [he]
      exact congrArg (fun f => f.app _ q.1) h₁
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiberRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiber Recognition. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

lemma correct_nullhomotopy_to_fiber {A B K L : SSet.{u}}
    (i : B ⟶ A) [Mono i] (p : K ⟶ L) (hp : simplicialFibrations p)
    (x : K _⦋0⦌) {a : A ⟶ K}
    (H : SSet.Homotopy a (SSet.const x))
    (J : SSet.Homotopy (SSet.const (X := A) x) (SSet.const x))
    (hH : i ▷ Δ[1] ≫ H.h = SSet.const x)
    (hJ : i ▷ Δ[1] ≫ J.h = SSet.const x)
    (G : SSet.Homotopy (H.h ≫ p) (J.h ≫ p))
    (gi : i ▷ Δ[1] ▷ Δ[1] ≫ G.h = SSet.const (p.app _ x))
    (g₀ : (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ▷ Δ[1] ≫ G.h = SSet.const (p.app _ x))
    (g₁ : (SSet.ι₁ : A ⟶ A ⊗ Δ[1]) ▷ Δ[1] ≫ G.h = SSet.const (p.app _ x)) :
    ∃ F : SSet.Homotopy a (SSet.const x),
      i ▷ Δ[1] ≫ F.h = SSet.const x ∧ F.h ≫ p = SSet.const (p.app _ x) := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i
    (SSet.stdSimplex.δ (n := 0) (0 : Fin 2))
  have hs : SSet.anodyneExtensions s.ι :=
    SSet.anodyneExtensions_pushoutObjObjι s (SimplicialCylinder.delta_one_anodyne 0)
  have htop {b : A ⟶ K} (T : SSet.Homotopy b (SSet.const x))
      (hT : i ▷ Δ[1] ≫ T.h = SSet.const x) : s.ι ≫ T.h = SSet.const x := by
    apply s.isPushout.hom_ext
    · rw [← Category.assoc,s.inl_ι,SSet.comp_const]
      apply (cancel_epi (SimplicialCylinder.zeroFactorIso A).hom).mp
      change endpoint A 0 ≫ T.h = _
      rw [endpoint_one,T.h₁,SSet.comp_const]
    · rw [← Category.assoc,s.inr_ι]
      change i ▷ Δ[1] ≫ T.h = _
      rw [hT,SSet.comp_const]
  have hside : s.ι ▷ Δ[1] ≫ G.h = SSet.const (p.app _ x) := by
    apply (s.isPushout.map (tensorRight (Δ[1] : SSet.{u}))).hom_ext
    · change s.inl ▷ Δ[1] ≫ s.ι ▷ Δ[1] ≫ G.h = _
      rw [← comp_whiskerRight_assoc,s.inl_ι]
      apply (cancel_epi ((SimplicialCylinder.zeroFactorIso A).hom ▷ Δ[1])).mp
      rw [← comp_whiskerRight_assoc]
      change (endpoint A 0) ▷ Δ[1] ≫ G.h = _
      rw [endpoint_one,g₁,SSet.comp_const,SSet.comp_const]
    · change s.inr ▷ Δ[1] ≫ s.ι ▷ Δ[1] ≫ G.h = _
      rw [← comp_whiskerRight_assoc,s.inr_ι]
      change i ▷ Δ[1] ▷ Δ[1] ≫ G.h = _
      rw [gi,SSet.comp_const]
  obtain ⟨Q,hQ,hQ₀,hQ₁,hQp⟩ := cylinder_lift_ends s.ι hs p hp H.h J.h (SSet.const x) G.h
    (by rw [htop H hH,SSet.comp_const])
    (by rw [htop J hJ,SSet.comp_const]) G.h₀.symm G.h₁.symm
    (by rw [SSet.const_comp,hside])
  let F : SSet.Homotopy a (SSet.const x) := CoherentGluing.toHomotopy
    ((SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ▷ Δ[1] ≫ Q)
    (by rw [SSet.ι₀_comp_assoc,hQ₀,H.h₀])
    (by rw [SSet.ι₁_comp_assoc,hQ₁,J.h₀])
  have hQi : i ▷ Δ[1] ▷ Δ[1] ≫ Q = SSet.const x := by
    have hi : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
    rw [← hi,comp_whiskerRight_assoc,hQ,SSet.comp_const]
  refine ⟨F,?_,?_⟩
  · change i ▷ Δ[1] ≫ (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ▷ Δ[1] ≫ Q = _
    rw [← comp_whiskerRight_assoc,← SSet.ι₀_comp,comp_whiskerRight_assoc,hQi,SSet.comp_const]
  · change ((SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ▷ Δ[1] ≫ Q) ≫ p = _
    rw [Category.assoc,hQp,g₀]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open SSet.modelCategoryQuillen
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

def strictFiber {K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌) : K.Subcomplex where
  obj n := {s | p.app n s = L.map (n.unop.const _ 0).op y}
  map {n m} θ s hs := by
    change p.app m (K.map θ s) = _
    rw [← CategoryTheory.comp_apply,p.naturality,CategoryTheory.comp_apply,hs,
      ← CategoryTheory.comp_apply,← L.map_comp]
    rfl

lemma strictFiber_ι_comp {K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌) :
    (strictFiber p y).ι ≫ p = SSet.const y := by
  ext n s
  exact s.property

def strictFiberLift {A K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌)
    (a : A ⟶ K) (ha : a ≫ p = SSet.const y) : A ⟶ (strictFiber p y : SSet) where
  app n := TypeCat.ofHom fun s => ⟨a.app n s,by
    change p.app n (a.app n s) = _
    exact congrArg (fun f : A ⟶ L => f.app n s) ha⟩
  naturality n m θ := by
    ext s
    apply Subtype.ext
    exact congrArg (fun f => f s) (a.naturality θ)

lemma strictFiberLift_ι {A K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌)
    (a : A ⟶ K) (ha : a ≫ p = SSet.const y) :
    strictFiberLift p y a ha ≫ (strictFiber p y).ι = a := rfl

lemma strictFiber_kan {K L : SSet.{u}} (p : K ⟶ L) (hp : simplicialFibrations p)
    (y : L _⦋0⦌) : SSet.KanComplex (strictFiber p y : SSet) := by
  apply (HomotopicalAlgebra.isFibrant_iff _).mpr
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B i hi
  constructor
  intro a b sq
  have := hp i hi
  let q : CommSq (a ≫ (strictFiber p y).ι) i p (SSet.const y) :=
    ⟨by rw [Category.assoc,strictFiber_ι_comp,SSet.comp_const,SSet.comp_const]⟩
  refine ⟨⟨{
    l := strictFiberLift p y q.lift q.fac_right
    fac_left := ?_
    fac_right := Subsingleton.elim _ _ }⟩⟩
  apply (cancel_mono (strictFiber p y).ι).mp
  rw [Category.assoc,strictFiberLift_ι,q.fac_left]

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity PolyPoint

lemma strictFiber_vertex_iff {K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌)
    (x : K _⦋0⦌) : x ∈ (strictFiber p y).obj (op ⦋0⦌) ↔ p.app _ x = y := by
  have e : (⦋0⦌.const ⦋0⦌ 0) = 𝟙 _ := by
    ext i
    simp
  change (p.app _ x = L.map _ y) ↔ _
  rw [e]
  change (p.app _ x = L.map (𝟙 _) y) ↔ _
  rw [L.map_id]
  rfl

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

def simplexConeOrder {n m : ℕ} (s : Fin (m+1) →o Fin (n+1))
    (t : Fin (m+1) →o Fin 2) : Fin (m+1) →o Fin (n+1) where
  toFun j := if t j = 0 then 0 else s j
  monotone' := by
    intro i j h
    have ht := t.monotone h
    dsimp only
    split_ifs with hi hj hj
    · exact le_rfl
    · exact Fin.zero_le _
    · exact False.elim (hi (le_antisymm (hj ▸ ht) (Fin.zero_le _)))
    · exact s.monotone h

def simplexCone (n : ℕ) : (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[n] where
  app m := TypeCat.ofHom fun s => SSet.stdSimplex.objMk
    (simplexConeOrder (SSet.stdSimplex.asOrderHom s.1) (SSet.stdSimplex.asOrderHom s.2))
  naturality m k θ := by
    ext s
    rfl

lemma simplexCone_zero (n : ℕ) :
    SSet.ι₀ ≫ simplexCone.{u} n = SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) := by
  ext m s
  apply SSet.stdSimplex.ext
  intro j
  rfl
lemma simplexCone_one (n : ℕ) : SSet.ι₁ ≫ simplexCone.{u} n = 𝟙 _ := by
  ext m s
  apply SSet.stdSimplex.ext
  intro j
  rfl

theorem fibration_rlp_of_fibers {K L : SSet.{u}} (p : K ⟶ L)
    (hp : simplicialFibrations p)
    (hf : ∀ y : L _⦋0⦌, SSet.modelCategoryQuillen.I.rlp
      (terminal.from (strictFiber p y : SSet))) : SSet.modelCategoryQuillen.I.rlp p := by
  rintro _ _ _ ⟨n⟩
  constructor
  intro a b sq
  let i := (SSet.boundary n).ι
  let C := simplexCone.{u} n ≫ b
  let y := b.app _ (SSet.stdSimplex.obj₀Equiv.symm 0)
  have hc₀ : SSet.ι₀ ≫ C = SSet.const y := by
    rw [← Category.assoc,simplexCone_zero,SSet.const_comp]
  have hc₁ : SSet.ι₁ ≫ C = b := by rw [← Category.assoc,simplexCone_one,Category.id_comp]
  have : HasLiftingProperty (SSet.ι₁ (X := (SSet.boundary n : SSet))) p :=
    (SimplicialCylinder.endpoint_anodyne (SSet.boundary n : SSet)).2 p hp
  let q : CommSq a SSet.ι₁ p (i ▷ Δ[1] ≫ C) :=
    ⟨by rw [SSet.ι₁_comp_assoc,hc₁]; exact sq.w⟩
  let a₀ := SSet.ι₀ ≫ q.lift
  have ha₀ : a₀ ≫ p = SSet.const y := by
    dsimp only [a₀]
    rw [Category.assoc,q.fac_right,SSet.ι₀_comp_assoc,hc₀,SSet.comp_const]
  let af := strictFiberLift p y a₀ ha₀
  have := hf y _ ⟨n⟩
  let r : CommSq af i (terminal.from (strictFiber p y : SSet)) (terminal.from _) :=
    ⟨Subsingleton.elim _ _⟩
  let l := r.lift ≫ (strictFiber p y).ι
  have hl : i ≫ l = a₀ := by rw [← Category.assoc,r.fac_left,strictFiberLift_ι]
  have hlp : l ≫ p = SSet.const y := by rw [Category.assoc,strictFiber_ι_comp,SSet.comp_const]
  obtain ⟨Q,hQ,hQ₀,hQp⟩ := cylinder_lift i p hp 1 l q.lift C
    (by rw [endpoint_zero,hl])
    (by rw [endpoint_zero,hc₀,hlp]) q.fac_right
  refine ⟨⟨{l := SSet.ι₁ ≫ Q, fac_left := ?_,fac_right := ?_}⟩⟩
  · rw [← SSet.ι₁_comp_assoc,hQ,q.fac_left]
  · rw [Category.assoc,hQp,hc₁]
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_KanQuillen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kan Quillen. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite

namespace Thomason.GeometricRecognition

lemma strictFiber_isPullback {K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌) :
    IsPullback (strictFiber p y).ι (terminal.from (strictFiber p y : SSet)) p
      (SSet.const (X := ⊤_ SSet.{u}) y) := by
  have hw : (strictFiber p y).ι ≫ p = terminal.from (strictFiber p y : SSet) ≫ SSet.const y := by
    rw [strictFiber_ι_comp,SSet.comp_const]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
  refine PullbackCone.IsLimit.mk hw
    (fun s => strictFiberLift p y s.fst (by rw [s.condition,SSet.comp_const]))
    (fun s => strictFiberLift_ι _ _ _ _) (fun _ => Subsingleton.elim _ _) ?_
  intro s m hm _
  apply (cancel_mono (strictFiber p y).ι).mp
  rw [strictFiberLift_ι,hm]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite

namespace Thomason.GeometricRecognition
open HornSubdivision Subdivision

lemma sequential_colimit_lifting {A B : SSet.{u}} [A.Finite] [B.Finite]
    (i : A ⟶ B) {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y)
    (hp : ∀ n, HasLiftingProperty i (p.app n)) :
    HasLiftingProperty i (colim.map p) := by
  let : PreservesFilteredColimitsOfSize.{0,0} (coyoneda.obj (op A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let : PreservesFilteredColimitsOfSize.{0,0} (coyoneda.obj (op B)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  constructor
  intro a b sq
  obtain ⟨n,an,han⟩ := exists_hom_of_preservesColimit_coyoneda (colimit.isColimit X) a
  obtain ⟨m,bm,hbm⟩ := exists_hom_of_preservesColimit_coyoneda (colimit.isColimit Y) b
  change an ≫ colimit.ι X n = a at han
  change bm ≫ colimit.ι Y m = b at hbm
  have he : (an ≫ p.app n) ≫ colimit.ι Y n = (i ≫ bm) ≫ colimit.ι Y m := by
    rw [Category.assoc,← ι_colimMap,← Category.assoc,han,Category.assoc,hbm]
    exact sq.w
  obtain ⟨k,u,v,huv⟩ := exists_eq_of_preservesColimit_coyoneda (colimit.isColimit Y)
    (an ≫ p.app n) (i ≫ bm) he
  let := hp k
  let q : CommSq (an ≫ X.map u) i (p.app k) (bm ≫ Y.map v) :=
    ⟨by rw [Category.assoc,p.naturality,← Category.assoc]; exact huv⟩
  refine ⟨⟨{l := q.lift ≫ colimit.ι X k,fac_left := ?_,fac_right := ?_}⟩⟩
  · rw [← Category.assoc,q.fac_left,Category.assoc,colimit.w,han]
  · change (q.lift ≫ colimit.ι X k) ≫ colimMap p = b
    rw [Category.assoc,ι_colimMap,← Category.assoc,q.fac_right,Category.assoc,colimit.w,hbm]

lemma exStageMap_fibration {X Y : SSet.{u}} (p : X ⟶ Y) (hp : simplicialFibrations p)
    (n : ℕ) : simplicialFibrations (exStageMap p n) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact ex_preserves_fibrations _ ih

theorem exInfinity_fibration {X Y : SSet.{u}} (p : X ⟶ Y) (hp : simplicialFibrations p) :
    simplicialFibrations (exInfinityFunctor.map p) := by
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J,MorphismProperty.iSup_iff] at hi
  obtain ⟨n,⟨k⟩⟩ := hi
  apply sequential_colimit_lifting (SSet.horn (n+1) k).ι (exSequenceMap p)
  intro m
  exact exStageMap_fibration p hp m _ (by simp only [SSet.modelCategoryQuillen.J,MorphismProperty.iSup_iff]; exact ⟨n,⟨k⟩⟩)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z


namespace Thomason.DependentPosets
open CategoryTheory Limits Opposite
attribute [-instance] CategoryTheory.Sigma.sigma
variable {I : Type u} (P : I → Type u) [∀ i, PartialOrder (P i)]

def incl (i : I) : P i →o (Σ i, P i) where
  toFun := Sigma.mk i
  monotone' _ _ h := Sigma.LE.fiber _ _ _ h

def componentIso (i : I) : {x : Σ i, P i // x.1 = i} ≃o P i where
  toFun x := x.property ▸ x.val.2
  invFun x := ⟨⟨i,x⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,x⟩,h⟩; cases h; rfl
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨⟨j,x⟩,hx⟩ ⟨⟨k,y⟩,hy⟩
    cases hx; cases hy
    exact Sigma.mk_le_mk_iff.symm

lemma label_const {n : SimplexCategoryᵒᵖ} (s : (nerve (Σ i, P i)).obj n)
    (j : Fin (n.unop.len+1)) : (s.obj j).1 = (s.obj 0).1 :=
  ((Sigma.le_def.mp (leOfHom (s.map (homOfLE (Fin.zero_le j))))).choose).symm

def restricted {n : SimplexCategoryᵒᵖ} (s : (nerve (Σ i, P i)).obj n) :
    Fin (n.unop.len+1) ⥤ {x : Σ i, P i // x.1 = (s.obj 0).1} where
  obj j := ⟨s.obj j, label_const P s j⟩
  map f := homOfLE (leOfHom (s.map f))

def branch {n : SimplexCategoryᵒᵖ} (s : (nerve (Σ i, P i)).obj n) :
    (nerve (P (s.obj 0).1)).obj n :=
  restricted P s ⋙ (componentIso P (s.obj 0).1).toOrderEmbedding.toOrderHom.toFunctor

lemma incl_branch {n : SimplexCategoryᵒᵖ} (s : (nerve (Σ i, P i)).obj n) :
    (nerveMap (incl P (s.obj 0).1).toFunctor).app n (branch P s) = s := by
  apply nerve.ext_of_isThin
  funext j
  change Sigma.mk (s.obj 0).1 ((label_const P s j) ▸ (s.obj j).2) = s.obj j
  exact Sigma.ext (label_const P s j).symm (eqRec_heq _ _)

def isColimit : IsColimit (Cofan.mk (nerve (Σ i, P i))
    (fun i => nerveMap (incl P i).toFunctor)) := by
  apply evaluationJointlyReflectsColimits
  intro n
  apply (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj n)
    (fun i => nerve (P i)) (fun i => nerveMap (incl P i).toFunctor)).symm.toFun
  apply Classical.choice
  apply (Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mpr
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij : i = j := congrArg (fun s => (s.obj 0).1) h
    subst j
    have hxy : x = y := by
      apply nerve.ext_of_isThin
      funext k
      have hk := congrArg (fun s => s.obj k) h
      exact Sigma.mk.inj_iff.mp hk |>.2 |> eq_of_heq
    subst y
    rfl
  · intro s
    exact ⟨⟨(s.obj 0).1,branch P s⟩,incl_branch P s⟩

def iso : (∐ fun i => nerve (P i)) ≅ nerve (Σ i, P i) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (isColimit P)

@[reassoc] lemma iso_hom_ι (i : I) :
    Sigma.ι (fun i => nerve (P i)) i ≫ (iso P).hom = nerveMap (incl P i).toFunctor :=
  (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom (isColimit P) (Discrete.mk i)

variable {P}
def old (A : ∀ i, Set (P i)) : Set (Σ i, P i) := {x | x.2 ∈ A x.1}
lemma old_lower (A : ∀ i, Set (P i)) (hA : ∀ i, IsLowerSet (A i)) :
    IsLowerSet (old A) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h hy
  cases h with
  | fiber i x y h => exact hA i h hy

def oldIso (A : ∀ i, Set (P i)) : (Σ i, A i) ≃o old A where
  toFun x := ⟨⟨x.1,x.2.val⟩,x.2.property⟩
  invFun x := ⟨x.val.1,⟨x.val.2,x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨i,x⟩ ⟨j,y⟩
    constructor
    · intro h
      change Sigma.LE ⟨i,x.val⟩ ⟨j,y.val⟩ at h
      obtain ⟨e,he⟩ := Sigma.le_def.mp h
      cases e
      exact Sigma.LE.fiber _ _ _ he
    · intro h
      cases h
      exact Sigma.LE.fiber _ _ _ (by assumption)

def oldNerveIso (A : ∀ i, Set (P i)) :
    (∐ fun i => nerve (A i)) ≅ nerve (old A) :=
  iso (fun i => A i) ≪≫ PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (Σ i, A i)) (β := PartOrd.of (old A)) (oldIso A))

@[reassoc] lemma oldNerveIso_ι (A : ∀ i, Set (P i)) (i : I) :
    Sigma.ι (fun i => nerve (A i)) i ≫ (oldNerveIso A).hom =
      nerveMap ((oldIso A).toOrderEmbedding.toOrderHom.comp (incl (fun i => A i) i)).toFunctor := by
  change Sigma.ι (fun i => nerve (A i)) i ≫
    ((iso (fun i => A i)).hom ≫
      nerveMap (oldIso A).toOrderEmbedding.toOrderHom.toFunctor) = _
  rw [iso_hom_ι_assoc]
  rfl

lemma old_naturality (A : ∀ i, Set (P i)) :
    Limits.Sigma.map (fun i => nerveMap (OrderEmbedding.subtype (A i)).toOrderHom.toFunctor) ≫
      (iso P).hom =
    (oldNerveIso A).hom ≫ nerveMap (OrderEmbedding.subtype (old A)).toOrderHom.toFunctor := by
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_map_assoc, iso_hom_ι]
  rw [← Category.assoc]
  erw [oldNerveIso_ι A i]
  rfl

open AttachmentComparison
lemma mem_upward_old (A : ∀ i, Set (P i)) (i : I) (x : P i) :
    (⟨i,x⟩ : Σ i, P i) ∈ upward (old A) ↔ x ∈ upward (A i) := by
  constructor
  · rintro ⟨⟨j,a⟩,ha,hax⟩
    obtain ⟨e,h⟩ := Sigma.le_def.mp hax
    cases e
    exact ⟨a,ha,h⟩
  · rintro ⟨a,ha,hax⟩
    exact ⟨⟨i,a⟩,ha,Sigma.LE.fiber _ _ _ hax⟩

def oldUp (A : ∀ i, Set (P i)) (z : upward (old A)) : upward (A z.val.1) :=
  ⟨z.val.2, (mem_upward_old A _ _).mp z.property⟩

def oldRetraction (A : ∀ i, Set (P i)) (r : ∀ i, upward (A i) →o A i) :
    upward (old A) →o old A where
  toFun z := ⟨⟨z.val.1,(r _ (oldUp A z)).val⟩,(r _ (oldUp A z)).property⟩
  monotone' := by
    rintro ⟨⟨i,x⟩,hx⟩ ⟨⟨j,y⟩,hy⟩ h
    obtain ⟨e,he⟩ := Sigma.le_def.mp h
    cases e
    exact Sigma.LE.fiber _ _ _ ((r i).monotone he)

lemma oldRetraction_retract (A : ∀ i, Set (P i)) (r : ∀ i, upward (A i) →o A i)
    (hr : ∀ i (a : A i), r i ⟨a.val,a.val,a.property,le_rfl⟩ = a) (a : old A) :
    oldRetraction A r ⟨a.val,a.val,a.property,le_rfl⟩ = a := by
  rcases a with ⟨⟨i,a⟩,ha⟩
  apply Subtype.ext
  change Sigma.mk i (r i _).val = Sigma.mk i a
  exact congrArg (fun x : A i => Sigma.mk i x.val) (hr i ⟨a,ha⟩)

lemma oldRetraction_adjunction (A : ∀ i, Set (P i)) (r : ∀ i, upward (A i) →o A i)
    (hadj : ∀ i (a : A i) (z : upward (A i)), a.val ≤ z.val ↔ a ≤ r i z)
    (a : old A) (z : upward (old A)) :
    a.val ≤ z.val ↔ a ≤ oldRetraction A r z := by
  rcases a with ⟨⟨i,a⟩,ha⟩
  rcases z with ⟨⟨j,z⟩,hz⟩
  constructor
  · intro h
    obtain ⟨e,he⟩ := Sigma.le_def.mp h
    cases e
    exact Sigma.LE.fiber _ _ _ ((hadj i ⟨a,ha⟩ _).mp he)
  · intro h
    obtain ⟨e,he⟩ := Sigma.le_def.mp h
    cases e
    exact Sigma.LE.fiber _ _ _ ((hadj i ⟨a,ha⟩ _).mpr he)
end Thomason.DependentPosets

end

noncomputable section
universe u v w z


namespace Thomason.TransferAcyclicity
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

structure PosetAttachment where
  B : Type u
  order : PartialOrder B
  A : Set B
  lower : IsLowerSet A
  retraction : upward A →o A
  retract : ∀ a : A, retraction ⟨a.val,a.val,a.property,le_rfl⟩ = a
  adjunction : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ retraction z
  anodyne : SSet.anodyneExtensions
    (nerveMap (OrderEmbedding.toOrderHom (X := A) (Y := B)
      (OrderEmbedding.subtype A)).toFunctor)
attribute [instance] PosetAttachment.order

variable {I : Type u} (d : I → PosetAttachment.{u})

def sumData : PosetAttachment.{u} where
  B := Σ i, (d i).B
  order := inferInstance
  A := DependentPosets.old (fun i => (d i).A)
  lower := DependentPosets.old_lower _ (fun i => (d i).lower)
  retraction := DependentPosets.oldRetraction _ (fun i => (d i).retraction)
  retract := DependentPosets.oldRetraction_retract _ _ (fun i => (d i).retract)
  adjunction := DependentPosets.oldRetraction_adjunction _ _ (fun i => (d i).adjunction)
  anodyne := by
    let h := SSet.anodyneExtensions.colimMap
      (Discrete.natTrans (F := Discrete.functor (fun i => nerve (d i).A))
        (G := Discrete.functor (fun i => nerve (d i).B))
        (fun i => nerveMap (OrderEmbedding.toOrderHom (X := (d i.as).A)
          (Y := (d i.as).B) (OrderEmbedding.subtype (d i.as).A)).toFunctor))
      (fun i => (d i.as).anodyne)
    exact (SSet.anodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk
      (DependentPosets.oldNerveIso (fun i => (d i).A))
      (DependentPosets.iso (fun i => (d i).B))
      (DependentPosets.old_naturality (fun i => (d i).A)).symm)).mp h

end Thomason.TransferAcyclicity

end

noncomputable section
universe u v w z


namespace Thomason.TransferAcyclicity
open CategoryTheory Limits Simplicial
open AttachmentComparison SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

end Thomason.TransferAcyclicity

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_DimensionOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension One. -/

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

structure PosetAttachment where
  B : Type u
  order : PartialOrder B
  A : Set B
  lower : IsLowerSet A
  retraction : upward A →o A
  retract : ∀ a : A, retraction ⟨a.val,a.val,a.property,le_rfl⟩ = a
  adjunction : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ retraction z
attribute [instance] PosetAttachment.order

end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial
open AttachmentComparison SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

end Thomason.BoundaryProperness

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ModelTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model Transfer. -/

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer
open CategoryTheory Limits MorphismProperty Simplicial
open AttachmentComparison (upward )

variable {C : Type v} [Category.{u} C]

abbrev posetObj (G : SSet.{u} ⥤ C) (P : Type u) [PartialOrder P] := G.obj (nerve P)
abbrev inc (G : SSet.{u} ⥤ C) {P : Type u} [PartialOrder P] (A : Set P) :
    posetObj G A ⟶ posetObj G P :=
  G.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor)
abbrev L (G : SSet.{u} ⥤ C) := SSet.sd ⋙ SSet.sd ⋙ G
abbrev R (N : C ⥤ SSet.{u}) := N ⋙ SSet.ex ⋙ SSet.ex
abbrev transferredAdjunction {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} (adj : G ⊣ N) :
    L G ⊣ R N :=
  (SSet.sdExAdjunction.comp SSet.sdExAdjunction).comp adj
abbrev W (N : C ⥤ SSet.{u}) := simplicialWeakEquivalences.inverseImage (R N)
abbrev Fib (N : C ⥤ SSet.{u}) := simplicialFibrations.inverseImage (R N)
abbrev Cof (N : C ⥤ SSet.{u}) := (Fib N ⊓ W N).llp

structure PosetComparison (G : SSet.{u} ⥤ C) (N : C ⥤ SSet.{u}) (adj : G ⊣ N) : Prop where
  unit_weak : ∀ (P : Type u) [PartialOrder P],
    simplicialWeakEquivalences (adj.unit.app (nerve P))
  attachment_mono : ∀ {B : Type u} [PartialOrder B] (A : Set B) (_hA : IsLowerSet A)
    {X Y : C} (a : posetObj G A ⟶ X) (j : X ⟶ Y) (v : posetObj G B ⟶ Y),
    IsPushout a (inc G A) j v → Mono (N.map j)
  comparison : ∀ {B : Type u} [PartialOrder B] (A : Set B) (_hA : IsLowerSet A)
    (r : upward A →o A)
    (_hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {X Y : C} (a : posetObj G A ⟶ X) (j : X ⟶ Y) (v : posetObj G B ⟶ Y),
    IsPushout a (inc G A) j v →
    ∀ {P : SSet.{u}} {lX : N.obj X ⟶ P} {lB : N.obj (posetObj G B) ⟶ P},
    IsPushout (N.map a) (N.map (inc G A)) lX lB →
    ∀ F : P ⟶ N.obj Y, lX ≫ F = N.map j → lB ≫ F = N.map v →
      simplicialWeakEquivalences F

variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable (h : PosetComparison G N adj)
include h

lemma inc_mono {B : Type u} [PartialOrder B] (A : Set B) (hA : IsLowerSet A) :
    Mono (N.map (inc G A)) :=
  h.attachment_mono A hA (𝟙 _) (inc G A) (𝟙 _) IsPushout.of_id_fst

open PartialOrder KanLocal
open SubdividedUnit (D )

end Thomason.AbstractTransfer

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Horns
open CategoryTheory Limits Simplicial PartialOrder KanLocal
open AttachmentComparison (upward)
open AbstractTransfer
open TransferAcyclicity (PosetAttachment sumData)
attribute [-instance] CategoryTheory.Sigma.sigma

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G]

abbrev arrow (G : SSet.{u} ⥤ C) (d : PosetAttachment.{u}) := Arrow.mk (inc G d.A)

def Admissible (G : SSet.{u} ⥤ C) : MorphismProperty (C) :=
  fun _ _ f => ∃ d : PosetAttachment.{u}, Nonempty (arrow G d ≅ Arrow.mk f)

section Coproducts
variable {I : Type u} (d : I → PosetAttachment.{u})

def posetCoprodIso (P : I → Type u) [∀ i, PartialOrder (P i)] :
    (∐ fun i => posetObj G (P i)) ≅ posetObj G (Σ i, P i) :=
  (PreservesCoproduct.iso G (fun i => nerve (P i))).symm ≪≫
    G.mapIso (DependentPosets.iso P)

def oldCoprodIso : (∐ fun i => posetObj G (d i).A) ≅ posetObj G (sumData d).A :=
  (PreservesCoproduct.iso G (fun i => nerve (d i).A)).symm ≪≫
    G.mapIso (DependentPosets.oldNerveIso (fun i => (d i).A))

@[reassoc] lemma posetCoprodIso_ι (P : I → Type u) [∀ i, PartialOrder (P i)] (i : I) :
    Sigma.ι (fun i => posetObj G (P i)) i ≫ (posetCoprodIso (G := G) P).hom =
      G.map (nerveMap (DependentPosets.incl P i).toFunctor) := by
  simp only [posetCoprodIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison, ← Functor.map_comp,
    DependentPosets.iso_hom_ι]

@[reassoc] lemma oldCoprodIso_ι (i : I) :
    Sigma.ι (fun i => posetObj G (d i).A) i ≫ (oldCoprodIso (G := G) d).hom =
      G.map (nerveMap
        ((DependentPosets.oldIso (fun i => (d i).A)).toOrderEmbedding.toOrderHom.comp
          (DependentPosets.incl (fun i => (d i).A) i)).toFunctor) := by
  change Sigma.ι (fun i => G.obj (nerve (d i).A)) i ≫
    ((PreservesCoproduct.iso G (fun i => nerve (d i).A)).inv ≫
      G.map (DependentPosets.oldNerveIso (fun i => (d i).A)).hom) = G.map _
  rw [← Category.assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison, ← Functor.map_comp,
    DependentPosets.oldNerveIso_ι]

end Coproducts

end Thomason.AbstractTransfer.Horns

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open KanLocal SubdividedUnit Horns
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G] [PreservesFilteredColimitsOfSize.{u,u} N]
variable (h : PosetComparison G N adj)
include h

variable [IsLocallyPresentable.{u} C]
variable [IsCardinalForSmallObjectArgument (hornImages (L G)) Cardinal.aleph0.{u}]

omit h [PreservesColimitsOfSize.{u,u} G] [PreservesFilteredColimitsOfSize.{u,u} N]
  [IsCardinalForSmallObjectArgument (hornImages (L G)) Cardinal.aleph0.{u}] in
include adj in
lemma first_wfs_aux : IsWeakFactorizationSystem (Fib N).llp (Fib N) := by
  have hwfs := hornImages_weakFactorization (L G)
  rwa [hornImages_rlp (transferredAdjunction adj)] at hwfs

end Thomason.AbstractTransfer

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ProperTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Proper Transfer. -/

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Boundaries
open CategoryTheory Limits Simplicial PartialOrder KanLocal
open AttachmentComparison (upward)
open AbstractTransfer
open BoundaryProperness (PosetAttachment )
attribute [-instance] CategoryTheory.Sigma.sigma

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G]

abbrev arrow (G : SSet.{u} ⥤ C) (d : PosetAttachment.{u}) := Arrow.mk (inc G d.A)

def Admissible (G : SSet.{u} ⥤ C) : MorphismProperty (C) :=
  fun _ _ f => ∃ d : PosetAttachment.{u}, Nonempty (arrow G d ≅ Arrow.mk f)

end Thomason.AbstractTransfer.Boundaries

end

end OAI
end


