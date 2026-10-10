-- Prove2me | Definitions.Def_TFZDTopologyA
-- name    : TFZDTopologyA
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T01:02:40.294256+00:00
-- url     : https://prove2.me/theorems/ec65bfcf-99ba-453f-bd05-41758ae234f4
-- title:
--   OpenAI's torsion-free zero-divisor construction — simplicial and CW topology (part A)
-- statement:
--   General topology used in Section 5 of OpenAI's *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026, [github.com/openai/math](https://github.com/openai/math)) to build the finite two-dimensional classifying space. The code is OpenAI's Lean modules `SimplexTopology`, `Simplicial`, `Cellular`, `PartialLift`, `Milnor` and `HomotopyFunctor` from `lean/OAI/Algebra/GroupRing` (Apache License 2.0), concatenated with identifier-level edits for this platform's Lean and Mathlib. Its names are in the namespaces `OAI.GroupRingTopology` and `OAI.GroupRingTopology.*`.
--
--   It contains:
--   - the standard simplex as a compact subset of $\mathbb R^V$, and closed disks;
--   - geometric realizations of abstract simplicial complexes, with their cell structure;
--   - cellular maps, and lifting of maps defined on part of a cell complex;
--   - a Milnor-style construction and the homotopy functor that compares homotopy classes of maps between these spaces.
--
--   The bundle is mostly infrastructure: it holds definitions together with the lemmas proved about them, which later parts use. Nothing in it is specific to group rings.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, Section 5 (simplicial and CW models, cellular approximation, Milnor-type homotopy functor); Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), SimplexTopology, Simplicial, Cellular, PartialLift, Milnor, HomotopyFunctor

import Mathlib
universe u v w

section
namespace OAI

noncomputable section

namespace GroupRingTopology

def simplexSet (Scalar : Type*) (Vertex : Type*) [Semiring Scalar] [PartialOrder Scalar]
    [Fintype Vertex] : Set (Vertex → Scalar) :=
  {coordinates | (∀ vertex, 0 ≤ coordinates vertex) ∧ ∑ vertex, coordinates vertex = 1}

instance (Vertex : Type*) [Fintype Vertex] : CompactSpace (simplexSet ℝ Vertex) := by
  apply isCompact_iff_compactSpace.mp
  have hsub : simplexSet ℝ Vertex ⊆ Set.Icc 0 1 := fun x hx =>
    ⟨fun v => hx.1 v, fun v => by
      have := Finset.single_le_sum (fun w _ => hx.1 w) (Finset.mem_univ v)
      simpa [hx.2] using this⟩
  refine (isCompact_Icc (a := (0 : Vertex → ℝ)) (b := 1)).of_isClosed_subset ?_ hsub
  have h : simplexSet ℝ Vertex = (⋂ v, {x : Vertex → ℝ | 0 ≤ x v}) ∩ {x | ∑ v, x v = 1} := by
    ext x; simp [simplexSet]
  rw [h]
  exact (isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)).inter
    (isClosed_eq (continuous_finset_sum _ fun v _ => continuous_apply v) continuous_const)

end GroupRingTopology

open Set Metric Topology BigOperators
namespace GroupRingTopology.SimplexDisk

def Truncated (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}
def Positive (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
def sumCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i
@[simp] lemma sumCLM_apply (n : ℕ) (x : Fin n → ℝ) : sumCLM n x = ∑ i, x i := by
  simp [sumCLM]

lemma truncated_closed (n : ℕ) : IsClosed (Truncated n) := by
  have h : Truncated n = (⋂ i, {x | (0:ℝ) ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x; simp [Truncated]
  rw [h]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma positive_open (n : ℕ) : IsOpen (Positive n) := by
  have h : Positive n = (⋂ i, {x | (0:ℝ) < x i}) ∩ {x | ∑ i, x i < 1} := by
    ext x; simp [Positive]
  rw [h]
  exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma interior_truncated (n : ℕ) : interior (Truncated n) = Positive n := by
  apply Subset.antisymm
  · intro x hx
    have hc : ∀ i, 0 < x i := by
      intro i
      have hh := interior_mono (show Truncated n ⊆ (Function.eval i) ⁻¹' Ici (0:ℝ) from fun _ h => h.1 i) hx
      rw [← (isOpenMap_eval i).preimage_interior_eq_interior_preimage (continuous_apply i),interior_Ici] at hh
      exact hh
    refine ⟨hc,?_⟩
    cases n with
    | zero => simp
    | succ n =>
      have hs : Function.Surjective (sumCLM (n+1)) := by
        intro r
        refine ⟨Pi.single 0 r,?_⟩
        simp
      have hh := interior_mono (show Truncated (n+1) ⊆ (sumCLM (n+1)) ⁻¹' Iic (1:ℝ) from fun _ h => by simpa using h.2) hx
      rw [← ((sumCLM (n+1)).isOpenMap hs).preimage_interior_eq_interior_preimage (sumCLM (n+1)).continuous,interior_Iic] at hh
      simpa only [mem_preimage,mem_Iio,sumCLM_apply] using hh
  · apply (positive_open n).subset_interior_iff.mpr
    exact fun _ h => ⟨fun i => (h.1 i).le,h.2.le⟩

lemma truncated_convex (n : ℕ) : Convex ℝ (Truncated n) := by
  have h : Truncated n = (⋂ i, ((LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) ⁻¹' Ici 0)) ∩
      (sumCLM n) ⁻¹' Iic 1 := by ext x; simp [Truncated]
  rw [h]
  exact (convex_iInter fun i => (convex_Ici (0:ℝ)).linear_preimage (LinearMap.proj i)).inter
    ((convex_Iic (1:ℝ)).linear_preimage (sumCLM n).toLinearMap)

lemma truncated_bounded (n : ℕ) : Bornology.IsBounded (Truncated n) := by
  apply (isBounded_Icc (a := (0 : Fin n → ℝ)) (b := 1)).subset
  intro x hx
  refine ⟨hx.1,fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

lemma positive_nonempty (n : ℕ) : (Positive n).Nonempty := by
  refine ⟨fun _ => 1 / (n+1 : ℝ),fun _ => by positivity,?_⟩
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn : (0:ℝ) < n+1 := by positivity
  rw [mul_one_div,div_lt_one hn]
  linarith

noncomputable def ambient (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  Classical.choose (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))

lemma ambient_positive (n : ℕ) : ambient n '' Positive n = ball 0 1 := by
  simpa only [ambient,interior_truncated] using
    (Classical.choose_spec (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))).1
lemma ambient_truncated (n : ℕ) : ambient n '' Truncated n = closedBall 0 1 := by
  simpa only [ambient,(truncated_closed n).closure_eq] using
    (Classical.choose_spec (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (truncated_convex n) (by rw [interior_truncated]; exact positive_nonempty n) (truncated_bounded n))).2.1

noncomputable def truncatedDisk (n : ℕ) : Truncated n ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  ((ambient n).image (Truncated n)).trans (Homeomorph.setCongr (ambient_truncated n))

noncomputable def simplexTruncated (n : ℕ) : simplexSet ℝ (Fin (n+1)) ≃ₜ Truncated n where
  toFun x := ⟨fun i => x.1 i.succ,fun i => x.2.1 _,by
    have h := x.2.2
    rw [Fin.sum_univ_succ] at h
    linarith [x.2.1 0]⟩
  invFun x := ⟨Fin.cons (1 - ∑ i, x.1 i) x.1,by
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr x.2.2
      · exact x.2.1 j
    · simp [Fin.sum_univ_succ]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    have h := x.2.2
    rw [Fin.sum_univ_succ] at h
    change 1 - ∑ i : Fin n, x.1 i.succ = x.1 0
    linarith
  right_inv x := by rfl
  continuous_toFun := (continuous_pi fun i => (continuous_apply i.succ).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_subtype_val)
    · exact (continuous_apply j).comp continuous_subtype_val

noncomputable def simplexDisk (n : ℕ) : simplexSet ℝ (Fin (n+1)) ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (simplexTruncated n).trans (truncatedDisk n)

lemma simplexTruncated_positive (n : ℕ) (x : simplexSet ℝ (Fin (n+1))) :
    (simplexTruncated n x).1 ∈ Positive n ↔ ∀ i, 0 < x.1 i := by
  have h := x.2.2
  rw [Fin.sum_univ_succ] at h
  constructor
  · rintro ⟨hc,hs⟩ i
    refine Fin.cases ?_ (fun j => hc j) i
    change ∑ i : Fin n, x.1 i.succ < 1 at hs
    linarith
  · intro hc
    refine ⟨fun j => hc _,?_⟩
    change ∑ i : Fin n, x.1 i.succ < 1
    linarith [hc 0]

lemma simplexDisk_open (n : ℕ) (x : simplexSet ℝ (Fin (n+1))) :
    (simplexDisk n x).1 ∈ ball 0 1 ↔ ∀ i, 0 < x.1 i := by
  rw [← simplexTruncated_positive]
  change ambient n (simplexTruncated n x).1 ∈ ball 0 1 ↔ _
  rw [← ambient_positive]
  exact (ambient n).injective.mem_set_image

lemma simplexDisk_boundary (n : ℕ) (x : simplexSet ℝ (Fin (n+1))) :
    (simplexDisk n x).1 ∈ sphere 0 1 ↔ ∃ i, x.1 i = 0 := by
  have h := (simplexDisk n x).2
  rw [mem_sphere,mem_closedBall] at *
  have ho := simplexDisk_open n x
  simp only [mem_ball] at ho
  constructor
  · intro he
    have hn : ¬ ∀ i, 0 < x.1 i := by rw [←ho,he]; exact lt_irrefl _
    push Not at hn
    obtain ⟨i,hi⟩ := hn
    exact ⟨i,le_antisymm hi (x.2.1 i)⟩
  · rintro ⟨i,hi⟩
    apply le_antisymm h
    by_contra hn
    have hp := ho.mp (lt_of_not_ge hn)
    linarith [hp i]

noncomputable def reindex {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    simplexSet ℝ A ≃ₜ simplexSet ℝ B where
  toFun x := ⟨fun b => x.1 (e.symm b),fun b => x.2.1 _,(e.symm.sum_comp x.1).trans x.2.2⟩
  invFun x := ⟨fun a => x.1 (e a),fun a => x.2.1 _,(e.sum_comp x.1).trans x.2.2⟩
  left_inv x := by ext a; simp
  right_inv x := by ext b; simp
  continuous_toFun := (continuous_pi fun b => ((continuous_apply (e.symm b)).comp continuous_subtype_val : Continuous (fun x : simplexSet ℝ A => x.1 (e.symm b)))).subtype_mk _
  continuous_invFun := (continuous_pi fun a => ((continuous_apply (e a)).comp continuous_subtype_val : Continuous (fun x : simplexSet ℝ B => x.1 (e a)))).subtype_mk _

lemma reindex_positive {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (x : simplexSet ℝ A) :
    (∀ b, 0 < (reindex e x).1 b) ↔ ∀ a, 0 < x.1 a := by
  constructor
  · intro h a
    change ∀ b, 0 < x.1 (e.symm b) at h
    simpa only [e.symm_apply_apply] using h (e a)
  · intro h b
    change 0 < x.1 (e.symm b)
    exact h _

end GroupRingTopology.SimplexDisk
open Set Metric Topology BigOperators
namespace GroupRingTopology.Simplicial

section
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

/-- Finitely supported probability weights on a face, with the weak topology. -/
def Space := {w : V →₀ ℝ | (∀ v, 0 ≤ w v) ∧ w.sum (fun _ r => r) = 1 ∧ w.support ∈ K}
abbrev Face := {s : Finset V // s ∈ K}

lemma support_nonempty {w : V →₀ ℝ} (h : w.sum (fun _ r => r) = 1) : w.support.Nonempty := by
  classical
  by_contra hn
  have hz : w = 0 := by
    apply Finsupp.support_eq_empty.mp
    exact Finset.not_nonempty_iff_eq_empty.mp hn
  simp [hz] at h

lemma face_nonempty (s : Face K) : s.1.Nonempty := (K.isRelLowerSet_faces s.2).1

noncomputable def weight (s : Finset V) (x : simplexSet ℝ s) : V →₀ ℝ :=
  Finsupp.embDomain (Function.Embedding.subtype (· ∈ s)) (Finsupp.equivFunOnFinite.symm x.1)

lemma weight_apply (s : Finset V) (x : simplexSet ℝ s) (v : s) :
    weight s x v = x.1 v := by
  exact Finsupp.embDomain_apply_self _ _ _

lemma weight_apply_not (s : Finset V) (x : simplexSet ℝ s) {v : V} (hv : v ∉ s) :
    weight s x v = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨w,hw⟩
  exact hv (hw ▸ w.2)

lemma weight_nonneg (s : Finset V) (x : simplexSet ℝ s) (v : V) : 0 ≤ weight s x v := by
  classical
  by_cases hv : v ∈ s
  · exact (weight_apply s x ⟨v,hv⟩) ▸ x.2.1 ⟨v,hv⟩
  · rw [weight_apply_not _ _ hv]

lemma weight_sum (s : Finset V) (x : simplexSet ℝ s) : (weight s x).sum (fun _ r => r) = 1 := by
  rw [weight,Finsupp.sum_embDomain,Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact x.2.2

lemma weight_support_subset (s : Finset V) (x : simplexSet ℝ s) : (weight s x).support ⊆ s := by
  classical
  intro v hv
  by_contra hn
  exact Finsupp.mem_support_iff.mp hv (weight_apply_not _ _ hn)

noncomputable def faceMap (s : Face K) (x : simplexSet ℝ s.1) : Space K :=
  ⟨weight s.1 x,weight_nonneg _ _,weight_sum _ _,
    K.isRelLowerSet_faces.mem_of_le s.2 (weight_support_subset _ _) (support_nonempty (weight_sum _ _))⟩

noncomputable def quotient (x : Σ s : Face K, simplexSet ℝ s.1) : Space K := faceMap K x.1 x.2

instance : TopologicalSpace (Space K) := TopologicalSpace.coinduced (quotient K) inferInstance

lemma continuous_iff {Y : Type v} [TopologicalSpace Y] (f : Space K → Y) :
    Continuous f ↔ ∀ s : Face K, Continuous (f ∘ faceMap K s) := by
  rw [continuous_coinduced_dom]
  exact continuous_sigma_iff

lemma continuous_faceMap (s : Face K) : Continuous (faceMap K s) :=
  (continuous_coinduced_rng : Continuous (quotient K)).comp (continuous_sigmaMk (i := s))

lemma continuous_eval (v : V) : Continuous (fun x : Space K => x.1 v) := by
  classical
  rw [continuous_iff]
  intro s
  by_cases hv : v ∈ s.1
  · have he : (fun x : Space K => x.1 v) ∘ faceMap K s = (fun x : simplexSet ℝ s.1 => x.1 ⟨v,hv⟩) := by
      funext x
      exact weight_apply s.1 x ⟨v,hv⟩
    rw [he]
    exact (continuous_apply (⟨v,hv⟩ : s.1)).comp continuous_subtype_val
  · have he : (fun x : Space K => x.1 v) ∘ faceMap K s = (fun _ => (0:ℝ)) := by
      funext x
      exact weight_apply_not _ _ hv
    rw [he]
    exact continuous_const

instance : T2Space (Space K) :=
  T2Space.of_injective_continuous (f := fun x : Space K => (x.1 : V → ℝ))
    (fun _ _ h => Subtype.ext (Finsupp.ext fun v => congrFun h v))
    (continuous_pi fun v => continuous_eval K v)

lemma faceMap_injective (s : Face K) : Function.Injective (faceMap K s) := by
  intro x y h
  apply Subtype.ext
  funext v
  have hh := congrArg (fun p : Space K => p.1 v) h
  exact (weight_apply _ _ _).symm.trans (hh.trans (weight_apply _ _ _))

lemma faceMap_closedEmbedding (s : Face K) : IsClosedEmbedding (faceMap K s) :=
  (continuous_faceMap K s).isClosedEmbedding (faceMap_injective K s)

noncomputable def coordinates (s : Finset V) (x : Space K) (h : x.1.support ⊆ s) : simplexSet ℝ s := by
  refine ⟨fun v => x.1 v,fun v => x.2.1 _,?_⟩
  rw [Finset.sum_coe_sort]
  exact (x.1.sum_of_support_subset h _ (fun _ _ => rfl)).symm.trans x.2.2.1

lemma faceMap_coordinates (s : Face K) (x : Space K) (h : x.1.support ⊆ s.1) :
    faceMap K s (coordinates K s.1 x h) = x := by
  classical
  apply Subtype.ext
  ext v
  by_cases hv : v ∈ s.1
  · exact weight_apply _ _ ⟨v,hv⟩
  · change weight s.1 _ v = x.1 v
    rw [weight_apply_not _ _ hv,Finsupp.notMem_support_iff.mp (fun hh => hv (h hh))]

lemma range_faceMap (s : Face K) : Set.range (faceMap K s) = {x | x.1.support ⊆ s.1} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact weight_support_subset _ _
  · intro h
    exact ⟨coordinates K s.1 x h,faceMap_coordinates K s x h⟩

lemma quotient_surjective : Function.Surjective (quotient K) := by
  intro x
  exact ⟨⟨⟨x.1.support,x.2.2.2⟩,coordinates K x.1.support x (subset_refl _)⟩,
    faceMap_coordinates K ⟨x.1.support,x.2.2.2⟩ x (subset_refl _)⟩

lemma isClosed_iff (A : Set (Space K)) :
    IsClosed A ↔ ∀ s : Face K, IsClosed ((faceMap K s) ⁻¹' A) := by
  rw [isClosed_coinduced]
  exact isClosed_sigma_iff

lemma support_eq_iff (s : Face K) (x : simplexSet ℝ s.1) :
    (faceMap K s x).1.support = s.1 ↔ ∀ v, 0 < x.1 v := by
  classical
  constructor
  · intro he v
    have hn : weight s.1 x v ≠ 0 := by
      apply Finsupp.mem_support_iff.mp
      change v.1 ∈ (faceMap K s x).1.support
      rw [he]
      exact v.2
    rw [weight_apply] at hn
    exact lt_of_le_of_ne (x.2.1 v) (Ne.symm hn)
  · intro hp
    apply Finset.Subset.antisymm (weight_support_subset _ _)
    intro v hv
    apply Finsupp.mem_support_iff.mpr
    rw [weight_apply _ _ ⟨v,hv⟩]
    exact ne_of_gt (hp ⟨v,hv⟩)

end

open Set Metric Topology BigOperators
open scoped Classical
variable {V : Type u} {W : Type v} {T : Type w}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

lemma continuous_of_support_subset [TopologicalSpace T] (f : T → Space K) (s : Face K)
    (hs : ∀ x, (f x).1.support ⊆ s.1) (hc : ∀ v, Continuous fun x => (f x).1 v) : Continuous f := by
  let c : T → simplexSet ℝ s.1 := fun x => coordinates K s.1 (f x) (hs x)
  have hcc : Continuous c := (continuous_pi fun v : s.1 => hc v.1).subtype_mk _
  have he : f = (faceMap K s) ∘ c := by
    funext x
    exact (faceMap_coordinates K s (f x) (hs x)).symm
  rw [he]
  exact (continuous_faceMap K s).comp hcc

lemma push_apply (f : V → W) (w : V →₀ ℝ) (s : Finset V) (hs : w.support ⊆ s) (b : W) :
    (w.mapDomain f) b = ∑ a ∈ s, if f a = b then w a else 0 := by
  classical
  rw [Finsupp.mapDomain,Finsupp.sum_apply]
  rw [w.sum_of_support_subset hs]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [Finsupp.single_apply]
  · intro a _
    simp

lemma push_nonneg (f : V → W) (w : V →₀ ℝ) (hw : ∀ v, 0 ≤ w v) (b : W) :
    0 ≤ (w.mapDomain f) b := by
  classical
  rw [push_apply f w w.support (Finset.Subset.refl _) b]
  exact Finset.sum_nonneg fun a _ => by split; exact hw a; exact le_rfl

lemma push_sum (f : V → W) (w : V →₀ ℝ) :
    (w.mapDomain f).sum (fun _ r => r) = w.sum (fun _ r => r) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

def map (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (x : Space K) : Space L := by
  classical
  refine ⟨x.1.mapDomain f,push_nonneg f x.1 x.2.1,?_,?_⟩
  · rw [push_sum]; exact x.2.2.1
  · exact L.isRelLowerSet_faces.mem_of_le (hf ⟨x.1.support,x.2.2.2⟩) Finsupp.mapDomain_support
      (support_nonempty (by rw [push_sum]; exact x.2.2.1))

lemma map_support (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (x : Space K) :
    (map K L f hf x).1.support ⊆ x.1.support.image f := by
  classical
  exact Finsupp.mapDomain_support

lemma continuous_map (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) : Continuous (map K L f hf) := by
  classical
  rw [continuous_iff]
  intro s
  apply continuous_of_support_subset L _ ⟨s.1.image f,hf s⟩
  · intro x
    exact (map_support K L f hf _).trans (Finset.image_subset_image (weight_support_subset _ _))
  · intro b
    have he : (fun x : simplexSet ℝ s.1 => ((map K L f hf ∘ faceMap K s) x).1 b) =
        fun x => ∑ a : s.1, if f a.1 = b then x.1 a else 0 := by
      funext x
      change (Finsupp.mapDomain f (weight s.1 x)) b = _
      rw [push_apply f _ s.1 (weight_support_subset _ _) b,← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro a _
      rw [weight_apply]
    rw [he]
    apply continuous_finsetSum
    intro a _
    split_ifs
    · exact (continuous_apply a).comp continuous_subtype_val
    · exact continuous_const

def mapC (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) : C(Space K,Space L) :=
  ⟨map K L f hf,continuous_map K L f hf⟩

lemma map_id (hf : ∀ s : Face K, s.1.image id ∈ K) (x : Space K) : map K K id hf x = x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_id

lemma map_comp {U : Type*} (M : PreAbstractSimplicialComplex U)
    (f : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L)
    (g : W → U) (hg : ∀ s : Face L, s.1.image g ∈ M)
    (hgf : ∀ s : Face K, s.1.image (g ∘ f) ∈ M) (x : Space K) :
    map L M g hg (map K L f hf x) = map K M (g ∘ f) hgf x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_comp.symm

lemma quotient_quotientMap : IsQuotientMap (quotient K) :=
  ⟨⟨rfl⟩,quotient_surjective K⟩

lemma continuous_prod_iff [TopologicalSpace T] [LocallyCompactSpace T]
    {Y : Type*} [TopologicalSpace Y] (f : T × Space K → Y) :
    Continuous f ↔ ∀ s : Face K, Continuous (fun p : T × simplexSet ℝ s.1 => f (p.1,faceMap K s p.2)) := by
  constructor
  · intro hf s
    exact hf.comp (continuous_fst.prodMk ((continuous_faceMap K s).comp continuous_snd))
  · intro hf
    apply (quotient_quotientMap K).continuous_lift_prod_right
    rw [continuous_def]
    intro O hO
    have hp : (fun p : T × (Σ s : Face K, simplexSet ℝ s.1) => f (p.1,quotient K p.2)) ⁻¹' O =
      ⋃ s : Face K, (fun p : T × simplexSet ℝ s.1 => (p.1,⟨s,p.2⟩)) ''
        ((fun p : T × simplexSet ℝ s.1 => f (p.1,faceMap K s p.2)) ⁻¹' O) := by
      ext p
      simp only [mem_preimage,mem_iUnion,mem_image]
      constructor
      · intro h
        exact ⟨p.2.1,⟨p.1,p.2.2⟩,h,rfl⟩
      · rintro ⟨s,p,h,rfl⟩
        exact h
    rw [hp]
    apply isOpen_iUnion
    intro s
    exact (IsOpenMap.id.prodMap isOpenMap_sigmaMk) _ ((hf s).isOpen_preimage O hO)

end GroupRingTopology.Simplicial

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace GroupRingTopology.Simplicial

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

def mass : (V →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.lsum ℝ fun _ => LinearMap.id
lemma mass_apply (w : V →₀ ℝ) : mass w = w.sum (fun _ r => r) := rfl

lemma blend_support (x y : V →₀ ℝ) (t : I) :
    ((1-(t:ℝ)) • x + (t:ℝ) • y).support ⊆ x.support ∪ y.support :=
  Finsupp.support_add.trans (Finset.union_subset_union Finsupp.support_smul Finsupp.support_smul)

def blend (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) (t : I) : Space K := by
  let w := (1-(t:ℝ)) • x.1 + (t:ℝ) • y.1
  have hw : w.sum (fun _ r => r) = 1 := by
    rw [← mass_apply]
    simp only [w,map_add,map_smul,mass_apply,x.2.2.1,y.2.2.1,smul_eq_mul,mul_one]
    ring
  refine ⟨w,?_,hw,?_⟩
  · intro v
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (x.2.1 v)) (mul_nonneg t.2.1 (y.2.1 v))
  · exact K.isRelLowerSet_faces.mem_of_le s.2
      ((blend_support x.1 y.1 t).trans (Finset.union_subset hx hy)) (support_nonempty hw)

lemma blend_zero (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) :
    blend K s x y hx hy 0 = x := by
  apply Subtype.ext
  simp [blend]
lemma blend_one (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) :
    blend K s x y hx hy 1 = y := by
  apply Subtype.ext
  simp [blend]
lemma blend_self (s : Face K) (x : Space K) (hx : x.1.support ⊆ s.1) (t : I) :
    blend K s x x hx hx t = x := by
  apply Subtype.ext
  change (1-(t:ℝ)) • x.1 + (t:ℝ) • x.1 = x.1
  rw [← add_smul,sub_add_cancel,one_smul]

variable (f g : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (hg : ∀ s : Face K, s.1.image g ∈ L)
variable (hfg : ∀ s : Face K, s.1.image f ∪ s.1.image g ∈ L)

def straight (t : I) (x : Space K) : Space L :=
  blend L ⟨x.1.support.image f ∪ x.1.support.image g,hfg ⟨x.1.support,x.2.2.2⟩⟩
    (map K L f hf x) (map K L g hg x)
    ((map_support K L f hf x).trans Finset.subset_union_left)
    ((map_support K L g hg x).trans Finset.subset_union_right) t

lemma continuous_straight : Continuous (fun p : I × Space K => straight K L f g hf hg hfg p.1 p.2) := by
  rw [continuous_prod_iff]
  intro s
  apply continuous_of_support_subset L _ ⟨s.1.image f ∪ s.1.image g,hfg s⟩
  · intro p
    exact (blend_support _ _ p.1).trans (Finset.union_subset_union
      ((map_support K L f hf _).trans (Finset.image_subset_image (weight_support_subset _ _)))
      ((map_support K L g hg _).trans (Finset.image_subset_image (weight_support_subset _ _))))
  · intro b
    change Continuous (fun p : I × simplexSet ℝ s.1 =>
      (1-(p.1:ℝ)) * (map K L f hf (faceMap K s p.2)).1 b +
        (p.1:ℝ) * (map K L g hg (faceMap K s p.2)).1 b)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_eval L b).comp ((continuous_map K L f hf).comp ((continuous_faceMap K s).comp continuous_snd)))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_eval L b).comp ((continuous_map K L g hg).comp ((continuous_faceMap K s).comp continuous_snd))))

def straightHomotopy : (mapC K L f hf).Homotopy (mapC K L g hg) where
  toFun p := straight K L f g hf hg hfg p.1 p.2
  continuous_toFun := continuous_straight K L f g hf hg hfg
  map_zero_left _ := blend_zero L _ _ _ _ _
  map_one_left _ := blend_one L _ _ _ _ _

lemma straightHomotopy_fixed (x : Space K) (h : map K L f hf x = map K L g hg x) (t : I) :
    straightHomotopy K L f g hf hg hfg (t,x) = map K L f hf x := by
  apply Subtype.ext
  change (1-(t:ℝ)) • (map K L f hf x).1 + (t:ℝ) • (map K L g hg x).1 = (map K L f hf x).1
  rw [←h,←add_smul,sub_add_cancel,one_smul]
end
open Set Metric Topology BigOperators
open scoped Classical
variable {V : Type u} (K L : PreAbstractSimplicialComplex V) (hKL : ∀ s ∈ K, s ∈ L)

def inclusion (x : Space K) : Space L := ⟨x.1,x.2.1,x.2.2.1,hKL _ x.2.2.2⟩

lemma inclusion_injective : Function.Injective (inclusion K L hKL) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : Space L => z.1) h)

lemma inclusion_faceMap (s : Face K) (x : simplexSet ℝ s.1) :
    inclusion K L hKL (faceMap K s x) = faceMap L ⟨s.1,hKL _ s.2⟩ x := rfl

lemma continuous_inclusion : Continuous (inclusion K L hKL) := by
  rw [continuous_iff]
  intro s
  exact continuous_faceMap L ⟨s.1,hKL _ s.2⟩

lemma inclusion_isClosedMap : IsClosedMap (inclusion K L hKL) := by
  intro A hA
  rw [isClosed_iff]
  intro s
  let T : Set (Face K) := {t | t.1 ⊆ s.1}
  have hT : T.Finite := by
    have hf := s.1.powerset.finite_toSet.preimage (Subtype.val_injective : Function.Injective (Subtype.val : Face K → Finset V)).injOn
    convert hf using 1
    ext t
    simp only [T,mem_ofPred_eq,mem_preimage,Finset.mem_coe,Finset.mem_powerset]
  have hc : IsClosed (⋃ t ∈ T, inclusion K L hKL '' (A ∩ Set.range (faceMap K t))) := by
    apply hT.isClosed_biUnion
    intro t _
    exact (((isCompact_range (continuous_faceMap K t)).inter_left hA).image
      (continuous_inclusion K L hKL)).isClosed
  have he : inclusion K L hKL '' A ∩ Set.range (faceMap L s) =
      ⋃ t ∈ T, inclusion K L hKL '' (A ∩ Set.range (faceMap K t)) := by
    ext x
    simp only [mem_inter_iff,mem_image,mem_iUnion]
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hs⟩
      rw [range_faceMap] at hs
      let t : Face K := ⟨y.1.support,y.2.2.2⟩
      refine ⟨t,hs,y,⟨hy,?_⟩,rfl⟩
      rw [range_faceMap]
      exact Finset.Subset.refl _
    · rintro ⟨t,ht,y,⟨hy,hyt⟩,rfl⟩
      refine ⟨⟨y,hy,rfl⟩,?_⟩
      rw [range_faceMap] at hyt ⊢
      exact hyt.trans (show t.1 ⊆ s.1 from ht)
  rw [←he] at hc
  have hp := hc.preimage (continuous_faceMap L s)
  simpa only [preimage_inter,preimage_range,inter_univ] using hp

lemma inclusion_closedEmbedding : IsClosedEmbedding (inclusion K L hKL) :=
  .of_continuous_injective_isClosedMap (continuous_inclusion K L hKL)
    (inclusion_injective K L hKL) (inclusion_isClosedMap K L hKL)
end GroupRingTopology.Simplicial
namespace GroupRingTopology.Milnor
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical unitInterval
local instance (priority := 2000) (α : Type*) : DecidableEq α := Classical.decEq α
variable (G : Type u)

def complex : PreAbstractSimplicialComplex (ℕ × G) where
  faces := {s | s.Nonempty ∧ Set.InjOn Prod.fst (s : Set (ℕ × G))}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1,fun t hts ht => ⟨ht,hs.2.mono hts⟩⟩

abbrev Space := Simplicial.Space (complex G)

lemma mem_complex (s : Finset (ℕ × G)) : s ∈ complex G ↔
    s.Nonempty ∧ Set.InjOn Prod.fst (s : Set (ℕ × G)) := Iff.rfl

def bounded (N : ℕ) : PreAbstractSimplicialComplex (ℕ × G) where
  faces := {s | s ∈ complex G ∧ ∀ v ∈ s, v.1 < N}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1.1,fun t hts ht => ⟨(complex G).isRelLowerSet_faces.mem_of_le hs.1 hts ht,
      fun v hv => hs.2 v (hts hv)⟩⟩

lemma bounded_le (N : ℕ) : bounded G N ≤ complex G := fun _ hs => hs.1
lemma bounded_mono {N M : ℕ} (h : N ≤ M) : bounded G N ≤ bounded G M :=
  fun _ hs => ⟨hs.1,fun v hv => lt_of_lt_of_le (hs.2 v hv) h⟩

variable {G} {H : Type v}
lemma map_face (φ : G → H) (ρ : ℕ → ℕ) (hρ : Function.Injective ρ)
    (s : Face (complex G)) : s.1.image (fun v => (ρ v.1,φ v.2)) ∈ complex H := by
  refine ⟨s.2.1.image _,?_⟩
  rintro a ha b hb hab
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
  exact congrArg (fun v : ℕ × G => (ρ v.1,φ v.2)) (s.2.2 hx hy (hρ hab))

def map (φ : G → H) (ρ : ℕ → ℕ) (hρ : Function.Injective ρ) : C(Space G,Space H) :=
  Simplicial.mapC (complex G) (complex H) (fun v => (ρ v.1,φ v.2)) (map_face φ ρ hρ)

lemma map_comp {J : Type*} (φ : G → H) (ψ : H → J)
    (ρ τ : ℕ → ℕ) (hρ : Function.Injective ρ) (hτ : Function.Injective τ) (x : Space G) :
    map ψ τ hτ (map φ ρ hρ x) = map (ψ ∘ φ) (τ ∘ ρ) (hτ.comp hρ) x :=
by
  apply Subtype.ext
  exact Finsupp.mapDomain_comp.symm

lemma map_id (x : Space G) : map id id Function.injective_id x = x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_id

def vertex (v : ℕ × G) : Space G :=
  ⟨Finsupp.single v 1,by intro w; simp only [Finsupp.single_apply]; split_ifs <;> norm_num,
    by simp,by
      simp only [Finsupp.support_single _ one_ne_zero]
      exact ⟨Finset.singleton_nonempty v,by simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst v⟩⟩

lemma bounded_union_apex (N : ℕ) (g : G) (s : Face (bounded G N)) :
    s.1 ∪ {(N,g)} ∈ complex G := by
  refine ⟨s.2.1.1.mono Finset.subset_union_left,?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact s.2.1.2 hx hy hxy
  · have hyy := Finset.mem_singleton.mp hy
    subst y
    exact False.elim ((Nat.ne_of_lt (s.2.2 x hx)) hxy)
  · have hxx := Finset.mem_singleton.mp hx
    subst x
    exact False.elim ((Nat.ne_of_lt (s.2.2 y hy)) hxy.symm)
  · exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm

lemma bounded_id_face (N : ℕ) (s : Face (bounded G N)) : s.1.image id ∈ complex G := by
  simpa only [Finset.image_id] using s.2.1
lemma bounded_const_face (N : ℕ) (g : G) (s : Face (bounded G N)) :
    s.1.image (fun _ => (N,g)) ∈ complex G := by
  rw [Finset.image_const s.2.1.1]
  exact ⟨Finset.singleton_nonempty _,by simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (N,g)⟩
lemma bounded_contiguous (N : ℕ) (g : G) (s : Face (bounded G N)) :
    s.1.image id ∪ s.1.image (fun _ => (N,g)) ∈ complex G := by
  rw [Finset.image_id,Finset.image_const s.2.1.1]
  exact bounded_union_apex N g s

lemma bounded_map_id (N : ℕ) (x : Simplicial.Space (bounded G N)) :
    Simplicial.map (bounded G N) (complex G) id (bounded_id_face N) x =
      Simplicial.inclusion (bounded G N) (complex G) (fun _ h => bounded_le G N h) x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_id

lemma map_const_vertex (K : PreAbstractSimplicialComplex (ℕ × G)) (v : ℕ × G)
    (hf : ∀ s : Face K, s.1.image (fun _ => v) ∈ complex G) (x : Simplicial.Space K) :
    Simplicial.map K (complex G) (fun _ => v) hf x = vertex v := by
  apply Subtype.ext
  change x.1.mapDomain (fun _ => v) = Finsupp.single v 1
  rw [Finsupp.mapDomain,← Finsupp.single_sum]
  exact congrArg (Finsupp.single v) x.2.2.1

end GroupRingTopology.Milnor

namespace GroupRingTopology.Simplicial
open Set Metric Topology BigOperators
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

abbrev Cell (n : ℕ) := {s : Face K // s.1.card = n+1}

def cellOfFace (s : Face K) : Cell K (s.1.card-1) :=
  ⟨s,by have := Finset.card_pos.mpr (face_nonempty K s); omega⟩

def cellEquiv {n : ℕ} (s : Cell K n) : s.1.1 ≃ Fin (n+1) :=
  Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using s.2)

def faceDisk {n : ℕ} (s : Cell K n) : simplexSet ℝ s.1.1 ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (SimplexDisk.reindex (cellEquiv K s)).trans (SimplexDisk.simplexDisk n)

lemma faceDisk_open {n : ℕ} (s : Cell K n) (x : simplexSet ℝ s.1.1) :
    (faceDisk K s x).1 ∈ ball 0 1 ↔ (faceMap K s.1 x).1.support = s.1.1 := by
  rw [support_eq_iff]
  exact (SimplexDisk.simplexDisk_open n _).trans (SimplexDisk.reindex_positive _ _)

def diskMap {n : ℕ} (s : Cell K n) : C(closedBall (0 : Fin n → ℝ) 1, Space K) :=
  ⟨(faceMap K s.1) ∘ (faceDisk K s).symm,(continuous_faceMap K s.1).comp (faceDisk K s).symm.continuous⟩

lemma diskMap_injective {n : ℕ} (s : Cell K n) : Function.Injective (diskMap K s) :=
  (faceMap_injective K s.1).comp (faceDisk K s).symm.injective

lemma diskMap_range {n : ℕ} (s : Cell K n) : Set.range (diskMap K s) = Set.range (faceMap K s.1) :=
  (faceDisk K s).symm.surjective.range_comp (faceMap K s.1)

def characteristic {n : ℕ} (s : Cell K n) (x : Fin n → ℝ) : Space K := by
  classical
  exact if hx : x ∈ closedBall 0 1 then diskMap K s ⟨x,hx⟩ else diskMap K s ⟨0,by simp⟩

lemma characteristic_disk {n : ℕ} (s : Cell K n) (x : closedBall (0 : Fin n → ℝ) 1) :
    characteristic K s x.1 = diskMap K s x := by simp only [characteristic, dif_pos x.2]

lemma characteristic_bijOn {n : ℕ} (s : Cell K n) :
    Set.BijOn (characteristic K s) (ball 0 1) {x | x.1.support = s.1.1} := by
  constructor
  · intro x hx
    let d : closedBall (0 : Fin n → ℝ) 1 := ⟨x,ball_subset_closedBall hx⟩
    rw [show characteristic K s x = diskMap K s d from characteristic_disk K s d]
    exact (faceDisk_open K s ((faceDisk K s).symm d)).mp (by simpa using hx)
  constructor
  · intro x hx y hy hxy
    have hxy' : diskMap K s ⟨x,ball_subset_closedBall hx⟩ = diskMap K s ⟨y,ball_subset_closedBall hy⟩ := by
      simpa only [← characteristic_disk] using hxy
    exact congrArg Subtype.val (diskMap_injective K s hxy')
  · intro x hx
    let z := coordinates K s.1.1 x (by rw [hx])
    let d := faceDisk K s z
    have hd : d.1 ∈ ball 0 1 := (faceDisk_open K s z).mpr (by rwa [faceMap_coordinates])
    exact ⟨d.1,hd,(characteristic_disk K s d).trans (by
      change faceMap K s.1 ((faceDisk K s).symm (faceDisk K s z)) = x
      rw [Homeomorph.symm_apply_apply]
      exact faceMap_coordinates K s.1 x _)⟩

def characteristicPE {n : ℕ} (s : Cell K n) : PartialEquiv (Fin n → ℝ) (Space K) :=
  (characteristic_bijOn K s).toPartialEquiv _ _ _

lemma characteristicPE_open {n : ℕ} (s : Cell K n) :
    characteristicPE K s '' ball 0 1 = {x | x.1.support = s.1.1} :=
  (characteristic_bijOn K s).image_eq

lemma characteristicPE_closed {n : ℕ} (s : Cell K n) :
    characteristicPE K s '' closedBall 0 1 = Set.range (faceMap K s.1) := by
  rw [← diskMap_range]
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,(characteristic_disk K s ⟨z,hz⟩).symm⟩
  · rintro ⟨z,rfl⟩
    exact ⟨z.1,z.2,characteristic_disk K s z⟩

lemma characteristicPE_continuous {n : ℕ} (s : Cell K n) :
    ContinuousOn (characteristicPE K s) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (closedBall (0:Fin n→ℝ) 1).domRestrict (characteristicPE K s) = diskMap K s := by
    funext x
    exact characteristic_disk K s x
  rw [he]
  exact (diskMap K s).continuous

lemma characteristicPE_continuous_symm {n : ℕ} (s : Cell K n) :
    ContinuousOn (characteristicPE K s).symm (characteristicPE K s).target := by
  let e := characteristicPE K s
  have he : IsEmbedding (e.source.domRestrict e) := by
    let inc : ball (0:Fin n→ℝ) 1 → closedBall (0:Fin n→ℝ) 1 := fun x => ⟨x.1,ball_subset_closedBall x.2⟩
    have hi : IsEmbedding inc := IsEmbedding.subtypeVal.codRestrict _ (fun x => ball_subset_closedBall x.2)
    have heq : e.source.domRestrict e = (diskMap K s) ∘ inc := by
      funext x
      exact characteristic_disk K s (inc x)
    rw [heq]
    exact ((diskMap K s).continuous.isClosedEmbedding (diskMap_injective K s)).isEmbedding.comp hi
  let H : e.source ≃ₜ e.target := e.toEquiv.toHomeomorphOfIsInducing
    (he.isInducing.codRestrict (fun x => e.map_source x.2))
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp H.symm.continuous

lemma support_lt_of_sphere {n : ℕ} (s : Cell K n) (x : Fin n → ℝ) (hx : x ∈ sphere 0 1) :
    (characteristicPE K s x).1.support.card < s.1.1.card := by
  have hd := characteristic_disk K s ⟨x,sphere_subset_closedBall hx⟩
  have hs : (characteristicPE K s x).1.support ⊆ s.1.1 := by
    rw [show characteristicPE K s x = diskMap K s ⟨x,sphere_subset_closedBall hx⟩ from hd]
    exact weight_support_subset _ _
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hs,?_⟩
  intro he
  have ho : x ∈ ball (0:Fin n→ℝ) 1 := by
    have hh := (faceDisk_open K s ((faceDisk K s).symm ⟨x,sphere_subset_closedBall hx⟩)).mpr (by
      change (characteristic K s x).1.support = s.1.1 at he
      rwa [hd] at he)
    simpa only [Homeomorph.apply_symm_apply] using hh
  exact sphere_disjoint_ball.notMem_of_mem_left hx ho

lemma subcells_finite (s : Face K) (n : ℕ) : Set.Finite {c : Cell K n | c.1.1 ⊆ s.1} := by
  classical
  have hinj : Function.Injective (fun c : Cell K n => c.1.1) := Subtype.val_injective.comp Subtype.val_injective
  have hfin := (s.1.powerset.finite_toSet).preimage hinj.injOn
  convert hfin using 1
  ext c
  simp only [mem_ofPred_eq,mem_preimage,Finset.mem_coe,Finset.mem_powerset]

noncomputable def subcells (s : Face K) (n : ℕ) : Finset (Cell K n) := (subcells_finite K s n).toFinset

lemma characteristic_boundary {n : ℕ} (s : Cell K n) :
    MapsTo (characteristicPE K s) (sphere 0 1)
      (⋃ (m < n) (j ∈ subcells K s.1 m), characteristicPE K j '' closedBall 0 1) := by
  intro x hx
  let y := characteristicPE K s x
  let t : Face K := ⟨y.1.support,y.2.2.2⟩
  let m := y.1.support.card-1
  let c : Cell K m := cellOfFace K t
  have hpos : 0 < y.1.support.card := Finset.card_pos.mpr (support_nonempty y.2.2.1)
  have hlt : y.1.support.card < s.1.1.card := support_lt_of_sphere K s x hx
  have hmn : m < n := by dsimp [m]; rw [s.2] at hlt; omega
  have hcs : c ∈ subcells K s.1 m := by
    rw [subcells,Set.Finite.mem_toFinset]
    change y.1.support ⊆ s.1.1
    rw [show y = diskMap K s ⟨x,sphere_subset_closedBall hx⟩ from characteristic_disk K s ⟨x,sphere_subset_closedBall hx⟩]
    exact weight_support_subset _ _
  refine mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨hmn,mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hcs,?_⟩⟩⟩⟩
  rw [characteristicPE_closed,range_faceMap]
  exact Finset.Subset.refl _

instance cwComplex : Topology.CWComplex (Set.univ : Set (Space K)) where
  cell := Cell K
  map _ := characteristicPE K
  source_eq _ _ := rfl
  continuousOn _ := characteristicPE_continuous K
  continuousOn_symm _ := characteristicPE_continuous_symm K
  pairwiseDisjoint' := by
    intro a _ b _ hab
    change Disjoint (characteristicPE K a.2 '' ball 0 1) (characteristicPE K b.2 '' ball 0 1)
    rw [characteristicPE_open,characteristicPE_open]
    apply Set.disjoint_left.mpr
    intro x hx hy
    have he : a.2.1.1 = b.2.1.1 := hx.symm.trans hy
    have hn : a.1 = b.1 := by have hc := congrArg Finset.card he; rw [a.2.2,b.2.2] at hc; omega
    apply hab
    rcases a with ⟨n,a⟩
    rcases b with ⟨m,b⟩
    dsimp at hn
    subst m
    exact congrArg (Sigma.mk n) (Subtype.ext (Subtype.ext he))
  mapsTo' _ s := ⟨subcells K s.1,characteristic_boundary K s⟩
  closed' A _ hA := by
    rw [isClosed_iff]
    intro s
    have hc := hA _ (cellOfFace K s)
    rw [characteristicPE_closed] at hc
    have hp := hc.preimage (continuous_faceMap K s)
    have he : (faceMap K s) ⁻¹' (A ∩ Set.range (faceMap K (cellOfFace K s).1)) = (faceMap K s) ⁻¹' A := by
      ext z; simp only [mem_preimage,mem_inter_iff]; exact and_iff_left (mem_range_self z)
    rwa [he] at hp
  union' := by
    apply Set.Subset.antisymm (subset_univ _)
    intro x _
    let s : Face K := ⟨x.1.support,x.2.2.2⟩
    refine mem_iUnion.mpr ⟨s.1.card-1,mem_iUnion.mpr ⟨cellOfFace K s,?_⟩⟩
    rw [characteristicPE_closed,range_faceMap]
    exact Finset.Subset.refl _
end GroupRingTopology.Simplicial
open Set Metric Topology

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Cellular
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

omit [T2Space X] in
/-- Closure finiteness in terms of a single finite list of open cells. -/
lemma closedCell_subset_finite_openCells (n : ℕ) (i : RelCWComplex.cell C n) :
    ∃ I : Finset (Σ m, RelCWComplex.cell C m),
      CWComplex.closedCell n i ⊆ ⋃ p ∈ I, CWComplex.openCell p.1 p.2 := by
  classical
  obtain ⟨J,hJ⟩ := CWComplex.cellFrontier_subset_finite_openCell n i
  refine ⟨insert ⟨n,i⟩ ((Finset.range n).sigma J),?_⟩
  intro x hx
  rw [← CWComplex.cellFrontier_union_openCell_eq_closedCell] at hx
  rcases hx with hx | hx
  swap
  · exact Set.mem_iUnion.mpr ⟨⟨n,i⟩,Set.mem_iUnion.mpr ⟨Finset.mem_insert_self _ _,hx⟩⟩
  · have hxx := hJ hx
    simp only [Set.mem_iUnion] at hxx
    obtain ⟨m,hm,j,hj,hx⟩ := hxx
    exact Set.mem_iUnion.mpr ⟨⟨m,j⟩,Set.mem_iUnion.mpr
      ⟨Finset.mem_insert_of_mem (by simp only [Finset.mem_sigma,Finset.mem_range]; exact ⟨hm,hj⟩),hx⟩⟩

/-- Any selection of at most one point from each open cell has all its subsets
closed. This is the closure-finite weak-topology argument behind compactness. -/
lemma cellSelection_closed {I : Type u} (c : I → Σ n, RelCWComplex.cell C n)
    (hc : Function.Injective c) (x : I → X)
    (hx : ∀ i, x i ∈ CWComplex.openCell (c i).1 (c i).2) (S : Set X)
    (hS : S ⊆ Set.range x) : IsClosed S := by
  apply (CWComplex.closed C S ?_).mpr
  · intro n j
    obtain ⟨J,hJ⟩ := closedCell_subset_finite_openCells n j
    have hfinite : (S ∩ CWComplex.closedCell n j).Finite := by
      have hcpre : (c ⁻¹' (J : Set (Σ n, RelCWComplex.cell C n))).Finite :=
        J.finite_toSet.preimage hc.injOn
      apply (hcpre.image x).subset
      rintro y ⟨hyS,hycell⟩
      obtain ⟨i,rfl⟩ := hS hyS
      have hxx := hJ hycell
      simp only [Set.mem_iUnion] at hxx
      obtain ⟨p,hpJ,hxp⟩ := hxx
      have heq : c i = p := by
        by_contra hne
        exact (CWComplex.disjoint_openCell_of_ne hne).notMem_of_mem_left (hx i) hxp
      exact ⟨i,by change c i ∈ J; rw [heq]; exact hpJ,rfl⟩
    exact hfinite.isClosed
  · rintro y hy
    obtain ⟨i,rfl⟩ := hS hy
    exact CWComplex.openCell_subset_complex (c i).1 (c i).2 (hx i)

/-- A compact part of a CW complex can meet only finitely many open cells. -/
theorem compact_finitely_many_cells {K : Set X} (hK : IsCompact K) :
    {p : Σ n, RelCWComplex.cell C n | (K ∩ CWComplex.openCell p.1 p.2).Nonempty}.Finite := by
  classical
  let I := {p : Σ n, RelCWComplex.cell C n | (K ∩ CWComplex.openCell p.1 p.2).Nonempty}
  let x : I → X := fun i => i.2.choose
  have hx (i : I) : x i ∈ CWComplex.openCell i.1.1 i.1.2 := i.2.choose_spec.2
  have hxK (i : I) : x i ∈ K := i.2.choose_spec.1
  have hinj : Function.Injective x := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact (CWComplex.disjoint_openCell_of_ne hne).notMem_of_mem_left (hx i) (hij ▸ hx j)
  have hall : ∀ S ⊆ Set.range x, IsClosed S :=
    cellSelection_closed (C := C) Subtype.val Subtype.val_injective x hx
  have hcompact : IsCompact (Set.range x) :=
    hK.of_isClosed_subset (hall _ subset_rfl) (Set.range_subset_iff.mpr hxK)
  have hdiscrete : IsDiscrete (Set.range x) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hall S hS,Set.inter_eq_left.mpr hS⟩
  have hrange := hcompact.finite hdiscrete
  have : Finite I := (Set.finite_range_iff hinj).mp hrange
  exact Set.toFinite I

/-- Compact maps cannot run out through infinitely many dimensions. -/
theorem compact_bounded_skeleton {K : Set X} (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ n : ℕ, K ⊆ CWComplex.skeletonLT C n := by
  classical
  let S := {p : Σ n, RelCWComplex.cell C n | (K ∩ CWComplex.openCell p.1 p.2).Nonempty}
  have hS : S.Finite := compact_finitely_many_cells hK
  let I := hS.toFinset
  refine ⟨I.sup (fun p => p.1+1),?_⟩
  intro x hx
  have hxC := hKC hx
  rw [← CWComplex.iUnion_openCell_eq_complex (C := C)] at hxC
  simp only [Set.mem_iUnion] at hxC
  obtain ⟨m,j,hj⟩ := hxC
  have hmem : (⟨m,j⟩ : Σ n, RelCWComplex.cell C n) ∈ I := by
    exact hS.mem_toFinset.mpr ⟨x,hx,hj⟩
  have hm : m+1 ≤ I.sup (fun p => p.1+1) := Finset.le_sup (f := fun p => p.1+1) hmem
  apply CWComplex.skeletonLT_mono (C := C)
    (m := (m : ℕ∞)+1) (n := ((I.sup (fun p => p.1+1) : ℕ) : ℕ∞)) (by exact_mod_cast hm)
  exact CWComplex.closedCell_subset_skeletonLT m j (CWComplex.openCell_subset_closedCell m j hj)

/-- The bounded-skeleton property in its map form, used for spheres and disks. -/
theorem compactMap_bounded_skeleton {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f : C(A,X)) (hf : ∀ a, f a ∈ C) :
    ∃ n : ℕ, ∀ a, f a ∈ CWComplex.skeletonLT C n := by
  obtain ⟨n,hn⟩ := compact_bounded_skeleton (C := C) (isCompact_range f.continuous)
    (Set.range_subset_iff.mpr hf)
  exact ⟨n,fun a => hn (Set.mem_range_self a)⟩

end GroupRingTopology.Cellular

namespace GroupRingTopology.Simplicial
open Set Metric Topology BigOperators
open scoped Classical
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

lemma compact_bounded_vertices {A : Set (Space K)} (hA : IsCompact A) :
    ∃ S : Finset V, ∀ x ∈ A, x.1.support ⊆ S := by
  let T := {p : Σ n, Topology.RelCWComplex.cell (Set.univ : Set (Space K)) n |
    (A ∩ CWComplex.openCell p.1 p.2).Nonempty}
  have hT : T.Finite := Cellular.compact_finitely_many_cells hA
  let S := hT.toFinset.biUnion (fun p => p.2.1.1)
  refine ⟨S,?_⟩
  intro x hx
  let s : Face K := ⟨x.1.support,x.2.2.2⟩
  let c := cellOfFace K s
  have hc : (⟨s.1.card-1,c⟩ : Σ n, Topology.RelCWComplex.cell (Set.univ : Set (Space K)) n) ∈ hT.toFinset := by
    rw [hT.mem_toFinset]
    refine ⟨x,hx,?_⟩
    change x ∈ characteristicPE K c '' ball 0 1
    rw [characteristicPE_open]
    rfl
  exact Finset.subset_biUnion_of_mem (fun p => p.2.1.1) hc

end GroupRingTopology.Simplicial

open Set Metric Topology
namespace GroupRingTopology.SphereTopology
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def boundary (n : ℕ) : C(Sphere n,Disk n) :=
  ⟨fun x => ⟨x.1,sphere_subset_closedBall x.2⟩,continuous_subtype_val.subtype_mk _⟩

lemma sphere_norm {n : ℕ} (x : Sphere n) : ‖x.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using x.2
lemma disk_norm {n : ℕ} (x : Disk n) : ‖x.1‖ ≤ 1 := by
  simpa only [mem_closedBall,dist_zero_right] using x.2

def cone (n : ℕ) : C(unitInterval × Sphere n,Disk n) := by
  have hm (p : unitInterval × Sphere n) : (p.1:ℝ) • p.2.1 ∈ closedBall (0 : Fin n → ℝ) 1 := by
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg p.1.2.1,sphere_norm,mul_one]
    exact p.1.2.2
  exact ⟨fun p => ⟨(p.1:ℝ) • p.2.1,hm p⟩,
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk hm⟩

lemma cone_norm {n : ℕ} (p : unitInterval × Sphere n) : ‖(cone n p).1‖ = (p.1:ℝ) := by
  simp only [cone,ContinuousMap.coe_mk,norm_smul,Real.norm_eq_abs,abs_of_nonneg p.1.2.1,sphere_norm,mul_one]

lemma cone_surjective (n : ℕ) [Nonempty (Sphere n)] : Function.Surjective (cone n) := by
  intro x
  by_cases hx : x.1 = 0
  · obtain ⟨s⟩ := ‹Nonempty (Sphere n)›
    refine ⟨(0,s),Subtype.ext ?_⟩
    simp only [cone,ContinuousMap.coe_mk,Set.Icc.coe_zero,zero_smul,hx]
  · let s : Sphere n := ⟨‖x.1‖⁻¹ • x.1,by
      simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
    refine ⟨(⟨‖x.1‖,norm_nonneg _,disk_norm x⟩,s),Subtype.ext ?_⟩
    change ‖x.1‖ • (‖x.1‖⁻¹ • x.1) = x.1
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

lemma cone_quotient (n : ℕ) [Nonempty (Sphere n)] : IsQuotientMap (cone n) :=
  IsQuotientMap.of_surjective_continuous (cone_surjective n) (cone n).continuous

variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}

def Extends (f : C(Sphere n,Y)) : Prop := ∃ F : C(Disk n,Y), F.comp (boundary n) = f

lemma extends_of_nullhomotopic [Nonempty (Sphere n)] {y : Y} {f : C(Sphere n,Y)}
    (H : (ContinuousMap.const (Sphere n) y).Homotopy f) : Extends f := by
  have hf : Function.FactorsThrough H.toContinuousMap (cone n) := by
    intro p q hpq
    have ht : p.1 = q.1 := Subtype.ext ((cone_norm p).symm.trans ((congrArg (fun z : Disk n => ‖z.1‖) hpq).trans (cone_norm q)))
    by_cases hzero : (p.1:ℝ) = 0
    · have hp : p.1 = 0 := Subtype.ext hzero
      have hq : q.1 = 0 := ht.symm.trans hp
      change H (p.1,p.2) = H (q.1,q.2)
      rw [hp,hq,H.apply_zero,H.apply_zero]
      rfl
    · have hs : p.2 = q.2 := by
        apply Subtype.ext
        have heq := congrArg (fun z : Disk n => z.1) hpq
        change (p.1:ℝ) • p.2.1 = (q.1:ℝ) • q.2.1 at heq
        rw [← ht] at heq
        exact (smul_right_injective _ hzero) heq
      exact congrArg H.toContinuousMap (Prod.ext ht hs)
  let F : C(Disk n,Y) := (cone_quotient n).lift H.toContinuousMap hf
  refine ⟨F,?_⟩
  ext s
  have hh := ContinuousMap.congr_fun ((cone_quotient n).lift_comp H.toContinuousMap hf) (1,s)
  have hcone : cone n (1,s) = boundary n s := by apply Subtype.ext; simp [cone,boundary]
  simpa only [ContinuousMap.comp_apply,hcone,ContinuousMap.Homotopy.coe_toContinuousMap,
    ContinuousMap.Homotopy.apply_one] using hh

lemma nullhomotopic_of_extends {f : C(Sphere n,Y)} (hf : Extends f) :
    ∃ y : Y, Nonempty ((ContinuousMap.const (Sphere n) y).Homotopy f) := by
  obtain ⟨F,hF⟩ := hf
  let z : Disk n := ⟨0,by simp⟩
  refine ⟨F z,⟨{
    toFun := fun p => F (cone n p)
    continuous_toFun := F.continuous.comp (cone n).continuous
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro s
    exact congrArg F (Subtype.ext (by simp [cone,z]))
  · intro s
    have hs : cone n (1,s) = boundary n s := by apply Subtype.ext; simp [cone,boundary]
    rw [hs]
    exact ContinuousMap.congr_fun hF s

lemma extends_of_homotopy [Nonempty (Sphere n)] {f g : C(Sphere n,Y)}
    (H : f.Homotopy g) (hg : Extends g) : Extends f := by
  obtain ⟨y,⟨J⟩⟩ := nullhomotopic_of_extends hg
  exact extends_of_nullhomotopic (J.trans H.symm)

lemma sphere_nonempty (n : ℕ) : Nonempty (Sphere (n+1)) :=
  (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1)).coe_sort

end GroupRingTopology.SphereTopology

/-! Classical cellular lifting and its geometric foundations.
No classifying-space existence or Hurewicz theorem is assumed. -/
open Set Metric Topology

namespace GroupRingTopology.Cellular

abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def boundary (n : ℕ) : Sphere n → Disk n :=
  fun x => ⟨x.1, sphere_subset_closedBall x.2⟩

lemma continuous_boundary (n : ℕ) : Continuous (boundary n) :=
  continuous_subtype_val.subtype_mk _

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

/-- A characteristic map on its closed disk. -/
def characteristic (n : ℕ) (i : RelCWComplex.cell C n) : C(Disk n, X) :=
  ⟨fun x => RelCWComplex.map n i x.1, (RelCWComplex.continuousOn n i).domRestrict⟩

omit [T2Space X] in
lemma range_characteristic (n : ℕ) (i : RelCWComplex.cell C n) :
    Set.range (characteristic n i) = CWComplex.closedCell n i := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩; exact ⟨y.1,y.2,rfl⟩
  · rintro ⟨y,hy,rfl⟩; exact ⟨⟨y,hy⟩,rfl⟩

/-- The weak topology is genuinely final with respect to closed characteristic
maps; no finiteness or local-finiteness hypothesis is needed. -/
lemma continuousOn_iff_characteristic {Y : Type v} [TopologicalSpace Y] (f : X → Y) :
    ContinuousOn f C ↔ ∀ n (i : RelCWComplex.cell C n),
      Continuous (f ∘ characteristic n i) := by
  constructor
  · intro hf n i
    exact hf.comp_continuous (characteristic n i).continuous
      (fun x => CWComplex.closedCell_subset_complex n i ⟨x.1,x.2,rfl⟩)
  · intro hf
    rw [continuousOn_iff_continuous_domRestrict, continuous_iff_isClosed]
    intro S hS
    have hclosed : IsClosed (C ∩ f ⁻¹' S) := by
      apply (CWComplex.closed C _ inter_subset_left).2
      intro n i
      have hpre : IsClosed ((f ∘ characteristic n i) ⁻¹' S) :=
        hS.preimage (hf n i)
      have hcompact := hpre.isCompact.image (characteristic n i).continuous
      convert hcompact.isClosed using 1
      ext x
      constructor
      · rintro ⟨⟨hxC,hxS⟩, y,hy,rfl⟩
        exact ⟨⟨y,hy⟩,hxS,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨⟨CWComplex.closedCell_subset_complex n i ⟨y.1,y.2,rfl⟩,hy⟩,
          y.1,y.2,rfl⟩
    convert hclosed.preimage continuous_subtype_val using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, and_iff_right x.2, Set.domRestrict_apply]

abbrev Skeleton (C : Set X) [CWComplex C] (n : ℕ) : Set X :=
  CWComplex.skeletonLT C n

lemma skeleton_mono {m n : ℕ} (h : m ≤ n) :
    Skeleton C m ⊆ Skeleton C n :=
  CWComplex.skeletonLT_mono (by exact_mod_cast h)

lemma sphere_mem_skeleton (n : ℕ) (i : RelCWComplex.cell C n) (x : Sphere n) :
    characteristic n i (boundary n x) ∈ Skeleton C n :=
  CWComplex.cellFrontier_subset_skeletonLT n i ⟨x.1,x.2,rfl⟩

lemma characteristic_mem_skeleton {m n : ℕ} (h : m < n)
    (i : RelCWComplex.cell C m) (x : Disk m) :
    characteristic m i x ∈ Skeleton C n := by
  apply skeleton_mono (Nat.succ_le_of_lt h)
  exact CWComplex.closedCell_subset_skeletonLT m i ⟨x.1,x.2,rfl⟩

lemma openCell_not_skeleton (n : ℕ) (i : RelCWComplex.cell C n) {x : X}
    (hx : x ∈ CWComplex.openCell n i) : x ∉ Skeleton C n :=
  (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := i) le_rfl).notMem_of_mem_right hx

/-- A continuous partial lift on the (n-1)-skeleton, represented by a total
function only to avoid transported subtype terms. Values outside the skeleton
carry no condition and are never used. -/
structure PartialLift {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) (f : C(X,B)) (n : ℕ) where
  val : X → E
  continuousOn : ContinuousOn val (Skeleton C n)
  fac : ∀ x ∈ Skeleton C n, p (val x) = f x

/-- The concrete disk-boundary right lifting property. -/
def DiskRLP {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) : Prop :=
  ∀ n (a : C(Sphere n,E)) (b : C(Disk n,B)),
    (∀ x, p (a x) = b (boundary n x)) →
    ∃ e : C(Disk n,E), (∀ x, e (boundary n x) = a x) ∧ ∀ x, p (e x) = b x

variable {E : Type v} [TopologicalSpace E] {n : ℕ}

/-- Glue the old skeleton map to a prescribed disk map on each new cell. -/
noncomputable def attachValue (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (x : X) : E := by
  classical
  exact if x ∈ Skeleton C n then a x
    else if h : ∃ i : RelCWComplex.cell C n, x ∈ CWComplex.openCell n i then
      let i := h.choose
      let y := h.choose_spec.choose
      e i ⟨y,ball_subset_closedBall h.choose_spec.choose_spec.1⟩
    else a x

lemma attachValue_old (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    {x : X} (hx : x ∈ Skeleton C n) : attachValue a e x = a x := by
  classical
  simp only [attachValue, if_pos hx]

lemma attachValue_interior (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (i : RelCWComplex.cell C n) (y : Disk n) (hy : y.1 ∈ ball 0 1) :
    attachValue a e (characteristic n i y) = e i y := by
  classical
  have hx : characteristic n i y ∈ CWComplex.openCell n i := ⟨y.1,hy,rfl⟩
  have h : ∃ j : RelCWComplex.cell C n,
      characteristic n i y ∈ CWComplex.openCell n j := ⟨i,hx⟩
  rw [attachValue,if_neg (openCell_not_skeleton n i hx),dif_pos h]
  have hi : h.choose = i := by
    by_contra hne
    have hd := CWComplex.disjoint_openCell_of_ne (C := C) (i := h.choose) (j := i)
      (fun hEq => hne (sigma_mk_injective hEq))
    exact Set.disjoint_left.mp hd h.choose_spec hx
  have hz := h.choose_spec.choose_spec.1
  have hmap : RelCWComplex.map n i h.choose_spec.choose = characteristic n i y := by
    calc
      RelCWComplex.map n i h.choose_spec.choose =
          RelCWComplex.map n h.choose h.choose_spec.choose :=
        congrArg (fun k => RelCWComplex.map n k h.choose_spec.choose) hi.symm
      _ = _ := h.choose_spec.choose_spec.2
  have hcoord : h.choose_spec.choose = y.1 :=
    (RelCWComplex.map n i).injOn
      (by simpa only [RelCWComplex.source_eq] using hz)
      (by simpa only [RelCWComplex.source_eq] using hy) hmap
  exact (congrArg (fun k => e k ⟨h.choose_spec.choose,ball_subset_closedBall hz⟩) hi).trans
    (congrArg (e i) (Subtype.ext hcoord))

lemma attachValue_characteristic (a : X → E)
    (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (he : ∀ i (x : Sphere n), e i (boundary n x) =
      a (characteristic n i (boundary n x)))
    (i : RelCWComplex.cell C n) (y : Disk n) :
    attachValue a e (characteristic n i y) = e i y := by
  by_cases hy : y.1 ∈ ball 0 1
  · exact attachValue_interior a e i y hy
  · have hs : y.1 ∈ sphere 0 1 := le_antisymm y.2 (le_of_not_gt hy)
    have hx : characteristic n i y ∈ Skeleton C n := sphere_mem_skeleton n i ⟨y,hs⟩
    rw [attachValue_old a e hx]
    exact (he i ⟨y,hs⟩).symm

lemma attachValue_continuous (a : X → E) (ha : ContinuousOn a (Skeleton C n))
    (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (he : ∀ i (x : Sphere n), e i (boundary n x) =
      a (characteristic n i (boundary n x))) :
    ContinuousOn (attachValue a e) (Skeleton C (n+1)) := by
  apply (continuousOn_iff_characteristic (C := Skeleton C (n+1)) _).2
  intro m j
  change Continuous (fun x : Disk m => attachValue a e (characteristic m j.1 x))
  have hm : m < n+1 := by
    have h : (m : ℕ∞) < ((n+1 : ℕ) : ℕ∞) := by
      simpa only [RelCWComplex.skeletonLT_I,Set.mem_ofPred_eq] using j.2
    exact_mod_cast h
  rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | hm
  · have hEq : (fun x : Disk m => attachValue a e (characteristic m j.1 x)) =
        (fun x : Disk m => a (characteristic m j.1 x)) := by
      funext x
      exact attachValue_old a e (characteristic_mem_skeleton hm j.1 x)
    rw [hEq]
    exact ha.comp_continuous (characteristic m j.1).continuous
      (characteristic_mem_skeleton hm j.1)
  · subst m
    have hEq : (fun x : Disk n => attachValue a e (characteristic n j.1 x)) = e j.1 := by
      funext x
      exact attachValue_characteristic a e he j.1 x
    rw [hEq]
    exact (e j.1).continuous

end GroupRingTopology.Cellular

end

end OAI
end

section
namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
namespace GroupRingTopology.Cellular
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

namespace PartialLift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
variable {p : C(E,B)} {f : C(X,B)} {n : ℕ}

/-- The boundary lift for attaching an n-cell. -/
def onSphere (a : PartialLift (C := C) p f n) (i : RelCWComplex.cell C n) :
    C(Sphere n,E) :=
  ⟨fun x => a.val (characteristic n i (boundary n x)),
    a.continuousOn.comp_continuous
      ((characteristic n i).continuous.comp (continuous_boundary n))
      (sphere_mem_skeleton n i)⟩

lemma exists_cell_extension (a : PartialLift (C := C) p f n) (hp : DiskRLP p)
    (i : RelCWComplex.cell C n) :
    ∃ e : C(Disk n,E),
      (∀ x, e (boundary n x) = a.val (characteristic n i (boundary n x))) ∧
      ∀ x, p (e x) = f (characteristic n i x) := by
  apply hp n (a.onSphere i) (f.comp (characteristic n i))
  intro x
  exact a.fac _ (sphere_mem_skeleton n i x)

/-- Extend a partial lift across all cells of the next dimension. -/
noncomputable def next (a : PartialLift (C := C) p f n) (hp : DiskRLP p) :
    PartialLift (C := C) p f (n+1) := by
  choose e hb hf using fun i => a.exists_cell_extension hp i
  refine ⟨attachValue a.val e,attachValue_continuous a.val a.continuousOn e hb,?_⟩
  intro x hx
  have hdecomp : Skeleton C (n+1) = Skeleton C n ∪
      ⋃ i : RelCWComplex.cell C n, CWComplex.closedCell n i := by
    simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
      (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
  rw [hdecomp] at hx
  rcases hx with hx | hx
  · rw [attachValue_old a.val e hx]
    exact a.fac x hx
  · obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
    rw [show RelCWComplex.map n i y = characteristic n i ⟨y,hy⟩ from rfl,
      attachValue_characteristic a.val e hb]
    exact hf i ⟨y,hy⟩

lemma next_eq (a : PartialLift (C := C) p f n) (hp : DiskRLP p)
    {x : X} (hx : x ∈ Skeleton C n) : (a.next hp).val x = a.val x := by
  dsimp only [next]
  exact attachValue_old a.val _ hx

noncomputable def zero [Nonempty E] : PartialLift (C := C) p f 0 where
  val := fun _ => Classical.choice ‹Nonempty E›
  continuousOn := continuous_const.continuousOn
  fac := by
    intro x hx
    simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx

end PartialLift

section Lift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B] [Nonempty E]
variable {p : C(E,B)} (hp : DiskRLP p) (f : C(X,B))

noncomputable def stages : ∀ n, PartialLift (C := C) p f n
  | 0 => PartialLift.zero
  | n+1 => (stages n).next hp

lemma stages_agree {m n : ℕ} (h : m ≤ n) {x : X} (hx : x ∈ Skeleton C m) :
    (stages (C := C) hp f n).val x = (stages (C := C) hp f m).val x := by
  induction n,h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    exact ((stages (C := C) hp f n).next_eq hp (skeleton_mono hn hx)).trans ih

lemma exists_skeleton {x : X} (hx : x ∈ C) : ∃ n : ℕ, x ∈ Skeleton C n := by
  rw [← CWComplex.iUnion_skeletonLT_eq_complex (C := C)] at hx
  exact Set.mem_iUnion.mp hx

noncomputable def liftValue (x : X) : E := by
  classical
  exact if hx : x ∈ C then (stages (C := C) hp f (exists_skeleton (C := C) hx).choose).val x
    else Classical.choice ‹Nonempty E›

lemma liftValue_eq {n : ℕ} {x : X} (hx : x ∈ Skeleton C n) :
    liftValue (C := C) hp f x = (stages (C := C) hp f n).val x := by
  classical
  have hxC : x ∈ C := (CWComplex.skeletonLT C n).subset_complex hx
  rw [liftValue,dif_pos hxC]
  let m := (exists_skeleton (C := C) hxC).choose
  have hm : x ∈ Skeleton C m := (exists_skeleton (C := C) hxC).choose_spec
  exact (stages_agree hp f (Nat.le_max_left m n) hm).symm.trans
    (stages_agree hp f (Nat.le_max_right m n) hx)

lemma continuousOn_liftValue : ContinuousOn (liftValue (C := C) hp f) C := by
  apply (continuousOn_iff_characteristic _).2
  intro n i
  have hEq : liftValue (C := C) hp f ∘ characteristic n i =
      (stages (C := C) hp f (n+1)).val ∘ characteristic n i := by
    funext x
    exact liftValue_eq hp f (characteristic_mem_skeleton (Nat.lt_succ_self n) i x)
  rw [hEq]
  exact (stages (C := C) hp f (n+1)).continuousOn.comp_continuous (characteristic n i).continuous
    (characteristic_mem_skeleton (Nat.lt_succ_self n) i)

lemma liftValue_fac {x : X} (hx : x ∈ C) : p (liftValue (C := C) hp f x) = f x := by
  obtain ⟨n,hn⟩ := exists_skeleton (C := C) hx
  rw [liftValue_eq hp f hn]
  exact (stages (C := C) hp f n).fac x hn

include hp in
theorem exists_lift [CWComplex (Set.univ : Set X)] :
    ∃ g : C(X,E), ∀ x, p (g x) = f x := by
  refine ⟨⟨liftValue (C := Set.univ) hp f,
    continuousOn_univ.mp (continuousOn_liftValue (C := Set.univ) hp f)⟩,?_⟩
  intro x
  exact liftValue_fac hp f (Set.mem_univ x)

end Lift

noncomputable section
/-- Extension property with respect to the actual sup-norm disks. -/
def SphereFillable (Y : Type u) [TopologicalSpace Y] : Prop :=
  ∀ n (a : C(Sphere n,Y)), ∃ e : C(Disk n,Y), ∀ x, e (boundary n x) = a x

lemma disk_coord {n : ℕ} (x : Disk n) (i : Fin n) : |x.1 i| ≤ 1 := by
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mp
    (mem_closedBall_zero_iff.mp x.2) i

lemma disk_mem {n : ℕ} {x : Fin n → ℝ} (h : ∀ i, |x i| ≤ 1) :
    x ∈ closedBall 0 1 := by
  exact mem_closedBall_zero_iff.mpr
    ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr h)

def diskCons {n : ℕ} (x : Disk n) (t : unitInterval) : Disk (n+1) :=
  ⟨Fin.cons (2*t.1-1) x.1, disk_mem (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero,abs_le]
      constructor <;> linarith [t.2.1,t.2.2]
    · exact disk_coord x j)⟩

lemma continuous_diskCons {n : ℕ} :
    Continuous (fun q : Disk n × unitInterval => diskCons q.1 q.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Continuous (fun q : Disk n × unitInterval => 2*q.2.1-1)
    fun_prop
  · change Continuous (fun q : Disk n × unitInterval => q.1.1 j)
    exact (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)

def diskTail {n : ℕ} (x : Disk (n+1)) : Disk n :=
  ⟨Fin.tail x.1,disk_mem (fun i => disk_coord x i.succ)⟩

lemma continuous_diskTail {n : ℕ} : Continuous (@diskTail n) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (continuous_apply i.succ).comp continuous_subtype_val)

def diskTime {n : ℕ} (x : Disk (n+1)) : unitInterval :=
  ⟨(x.1 0+1)/2,by have h := (abs_le.mp (disk_coord x 0)); constructor <;> linarith⟩

lemma continuous_diskTime {n : ℕ} : Continuous (@diskTime n) := by
  exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2 |>.subtype_mk _

@[simp] lemma diskTail_cons {n : ℕ} (x : Disk n) (t : unitInterval) :
    diskTail (diskCons x t) = x := by
  apply Subtype.ext
  simp only [diskTail,diskCons,Fin.tail_cons]

@[simp] lemma diskTime_cons {n : ℕ} (x : Disk n) (t : unitInterval) :
    diskTime (diskCons x t) = t := by
  apply Subtype.ext
  simp only [diskTime,diskCons,Fin.cons_zero]
  ring

lemma sphere_iff_coord {n : ℕ} (x : Disk n) :
    x.1 ∈ sphere 0 1 ↔ ∃ i, |x.1 i| = 1 := by
  rw [sphere_pi (0 : Fin n → ℝ) (Or.inl (by norm_num))]
  simp only [Set.mem_inter_iff,Set.mem_iUnion,Set.mem_preimage,Function.eval,
    Pi.zero_apply,mem_sphere_zero_iff_norm,Real.norm_eq_abs,and_iff_left x.2]

lemma cons_mem_sphere_of_boundary {n : ℕ} (x : Sphere n) (t : unitInterval) :
    (diskCons (boundary n x) t).1 ∈ sphere 0 1 := by
  obtain ⟨i,hi⟩ := (sphere_iff_coord (boundary n x)).mp x.2
  exact (sphere_iff_coord _).mpr ⟨i.succ,hi⟩

lemma cons_zero_mem_sphere {n : ℕ} (x : Disk n) :
    (diskCons x 0).1 ∈ sphere 0 1 := by
  apply (sphere_iff_coord _).mpr
  exact ⟨0,by norm_num [diskCons]⟩

lemma cons_one_mem_sphere {n : ℕ} (x : Disk n) :
    (diskCons x 1).1 ∈ sphere 0 1 := by
  apply (sphere_iff_coord _).mpr
  exact ⟨0,by norm_num [diskCons]⟩

lemma sphere_split {n : ℕ} (x : Sphere (n+1)) :
    x.1 0 = -1 ∨ x.1 0 = 1 ∨ (diskTail (boundary (n+1) x)).1 ∈ sphere 0 1 := by
  obtain ⟨i,hi⟩ := (sphere_iff_coord (boundary (n+1) x)).mp x.2
  refine Fin.cases ?_ (fun i hi => ?_) i hi
  · intro h
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · exact Or.inr (Or.inr ((sphere_iff_coord _).mpr ⟨i,hi⟩))

/-- Finite closed pasting, in a form usable for the three cylinder faces. -/
lemma continuous_liftCover {A : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace A] [TopologicalSpace Y] [Finite ι]
    (S : ι → Set A) (f : ∀ i, C(S i,Y))
    (hcompat : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), f i ⟨x,hi⟩ = f j ⟨x,hj⟩)
    (hcover : ⋃ i, S i = Set.univ) (hclosed : ∀ i, IsClosed (S i)) :
    Continuous (Set.liftCover S (fun i => f i) hcompat hcover) := by
  rw [continuous_iff_isClosed]
  intro D hD
  rw [Set.preimage_liftCover]
  exact isClosed_iUnion_of_finite fun i => (hclosed i).isClosedMap_subtype_val _ (hD.preimage (f i).continuous)

def cylinderFace (n : ℕ) : Option Bool → Set (Sphere (n+1))
  | none => {x | (diskTail (boundary (n+1) x)).1 ∈ sphere 0 1}
  | some false => {x | x.1 0 = -1}
  | some true => {x | x.1 0 = 1}

lemma cylinderFace_closed (n : ℕ) (i : Option Bool) : IsClosed (cylinderFace n i) := by
  cases i with
  | none =>
    exact isClosed_sphere.preimage
      (continuous_subtype_val.comp (continuous_diskTail.comp (continuous_boundary (n+1))))
  | some b =>
    cases b <;>
      exact isClosed_eq ((continuous_apply 0).comp continuous_subtype_val) continuous_const

lemma cylinderFace_cover (n : ℕ) : ⋃ i, cylinderFace n i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases sphere_split x with h | h | h
  · exact Set.mem_iUnion.mpr ⟨some false,h⟩
  · exact Set.mem_iUnion.mpr ⟨some true,h⟩
  · exact Set.mem_iUnion.mpr ⟨none,h⟩

variable {Y : Type u} [TopologicalSpace Y]

def pathEndpoint : C(C(unitInterval,Y), Y × Y) :=
  ⟨fun q => (q 0,q 1), (continuous_eval_const 0).prodMk (continuous_eval_const 1)⟩

section CylinderMap
variable {n : ℕ} (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))

def faceTail (i : Option Bool) : C(cylinderFace n i,Disk n) :=
  ⟨fun x => diskTail (boundary (n+1) x.1),
    continuous_diskTail.comp ((continuous_boundary (n+1)).comp continuous_subtype_val)⟩

def faceSphere : C(cylinderFace n none,Sphere n) :=
  ⟨fun x => ⟨(faceTail none x).1,x.2⟩, (continuous_subtype_val.comp (faceTail none).continuous).subtype_mk _⟩

def faceTime (i : Option Bool) : C(cylinderFace n i,unitInterval) :=
  ⟨fun x => diskTime (boundary (n+1) x.1),
    continuous_diskTime.comp ((continuous_boundary (n+1)).comp continuous_subtype_val)⟩

def faceMap : ∀ i : Option Bool, C(cylinderFace n i,Y)
  | none => ⟨fun x => a (faceSphere x) (faceTime none x),
      continuous_eval.comp ((a.continuous.comp faceSphere.continuous).prodMk (faceTime none).continuous)⟩
  | some false => ⟨fun x => (b (faceTail (some false) x)).1,
      continuous_fst.comp (b.continuous.comp (faceTail (some false)).continuous)⟩
  | some true => ⟨fun x => (b (faceTail (some true) x)).2,
      continuous_snd.comp (b.continuous.comp (faceTail (some true)).continuous)⟩

lemma faceTime_eq_zero (x : Sphere (n+1)) (h : x.1 0 = -1) :
    diskTime (boundary (n+1) x) = 0 := by
  apply Subtype.ext
  change (x.1 0+1)/2 = 0
  rw [h]
  norm_num

lemma faceTime_eq_one (x : Sphere (n+1)) (h : x.1 0 = 1) :
    diskTime (boundary (n+1) x) = 1 := by
  apply Subtype.ext
  change (x.1 0+1)/2 = 1
  rw [h]
  norm_num

variable (h : ∀ x, pathEndpoint (a x) = b (boundary n x))

include h in
lemma faceMap_compat (i j : Option Bool) (x : Sphere (n+1))
    (hi : x ∈ cylinderFace n i) (hj : x ∈ cylinderFace n j) :
    faceMap a b i ⟨x,hi⟩ = faceMap a b j ⟨x,hj⟩ := by
  have left (hs : x ∈ cylinderFace n none) (h0 : x.1 0 = -1) :
      faceMap a b none ⟨x,hs⟩ = (b (diskTail (boundary (n+1) x))).1 := by
    change a (faceSphere ⟨x,hs⟩) (diskTime (boundary (n+1) x)) = _
    rw [faceTime_eq_zero x h0]
    exact congrArg Prod.fst (h (faceSphere ⟨x,hs⟩))
  have right (hs : x ∈ cylinderFace n none) (h1 : x.1 0 = 1) :
      faceMap a b none ⟨x,hs⟩ = (b (diskTail (boundary (n+1) x))).2 := by
    change a (faceSphere ⟨x,hs⟩) (diskTime (boundary (n+1) x)) = _
    rw [faceTime_eq_one x h1]
    exact congrArg Prod.snd (h (faceSphere ⟨x,hs⟩))
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some c => cases c; exact left hi hj; exact right hi hj
  | some c =>
    cases c
    · cases j with
      | none => exact (left hj hi).symm
      | some d =>
        cases d
        · rfl
        · have := hi.symm.trans hj; norm_num at this
    · cases j with
      | none => exact (right hj hi).symm
      | some d =>
        cases d
        · have := hi.symm.trans hj; norm_num at this
        · rfl

def cylinderBoundaryMap : C(Sphere (n+1),Y) :=
  ⟨Set.liftCover (cylinderFace n) (fun i => faceMap a b i)
    (faceMap_compat a b h) (cylinderFace_cover n),
    continuous_liftCover _ _ _ _ (cylinderFace_closed n)⟩

lemma cylinderBoundaryMap_face (i : Option Bool) (x : cylinderFace n i) :
    cylinderBoundaryMap a b h x.1 = faceMap a b i x :=
  by
    apply Set.liftCover_coe (S := cylinderFace n) (f := fun i => faceMap a b i)
      (hf := faceMap_compat a b h) (hS := cylinderFace_cover n)

end CylinderMap

/-- A disk filling extends the three compatible boundary faces of a cylinder. -/
theorem pathEndpoint_RLP (hY : SphereFillable Y) : DiskRLP (@pathEndpoint Y _) := by
  intro n a b h
  obtain ⟨F,hF⟩ := hY (n+1) (cylinderBoundaryMap a b h)
  let e : C(Disk n,C(unitInterval,Y)) :=
    (F.comp ⟨fun q : Disk n × unitInterval => diskCons q.1 q.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x
    apply ContinuousMap.ext
    intro t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = a x t
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t)) = a x t
    rw [diskTime_cons]
    congr 1
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 0))).1 = (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 1))).2 = (b x).2
      rw [diskTail_cons]

theorem contractible_of_sphereFillable {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [Nonempty Z] [CWComplex (Set.univ : Set Z)] (hZ : SphereFillable Z) :
    ContractibleSpace Z := by
  classical
  let z₀ : Z := Classical.choice ‹Nonempty Z›
  let : Nonempty C(unitInterval,Z) := ⟨ContinuousMap.const _ z₀⟩
  let f : C(Z,Z × Z) := ⟨fun z => (z,z₀),continuous_id.prodMk continuous_const⟩
  obtain ⟨g,hg⟩ := exists_lift (pathEndpoint_RLP hZ) f
  apply (contractible_iff_id_nullhomotopic Z).mpr
  refine ⟨z₀,⟨?_⟩⟩
  refine ContinuousMap.Homotopy.mk ⟨fun q => g q.2 q.1,
    continuous_eval.comp ((g.continuous.comp continuous_snd).prodMk continuous_fst)⟩ ?_ ?_
  · intro z
    exact congrArg Prod.fst (hg z)
  · intro z
    exact congrArg Prod.snd (hg z)

end
end GroupRingTopology.Cellular

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Milnor

section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical unitInterval
variable {G : Type u}
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def boundedInclusion (N : ℕ) : C(Simplicial.Space (bounded G N),Space G) :=
  ⟨Simplicial.inclusion (bounded G N) (complex G) (fun _ h => bounded_le G N h),
    Simplicial.continuous_inclusion _ _ _⟩

def boundedContraction (N : ℕ) (g : G) :
    (boundedInclusion (G := G) N).Homotopy (ContinuousMap.const _ (vertex (N,g))) := by
  let H := Simplicial.straightHomotopy (bounded G N) (complex G) id (fun _ => (N,g))
    (bounded_id_face N) (bounded_const_face N g) (bounded_contiguous N g)
  exact H.cast (ContinuousMap.ext (fun x => bounded_map_id N x))
    (ContinuousMap.ext (fun x => map_const_vertex (bounded G N) (N,g) (bounded_const_face N g) x))

lemma compactMap_bounded {A : Type v} [TopologicalSpace A] [CompactSpace A] (f : C(A,Space G)) :
    ∃ N : ℕ, ∃ F : C(A,Simplicial.Space (bounded G N)), (boundedInclusion N).comp F = f := by
  obtain ⟨S,hS⟩ := Simplicial.compact_bounded_vertices (complex G) (isCompact_range f.continuous)
  let N := S.sup Prod.fst + 1
  have hN (a : A) (v : ℕ × G) (hv : v ∈ (f a).1.support) : v.1 < N := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := Prod.fst) (hS (f a) (mem_range_self a) hv))
  let F : A → Simplicial.Space (bounded G N) := fun a =>
    ⟨(f a).1,(f a).2.1,(f a).2.2.1,(f a).2.2.2,hN a⟩
  have hc : Continuous F :=
    (Simplicial.inclusion_closedEmbedding (bounded G N) (complex G)
      (fun _ h => bounded_le G N h)).isEmbedding.continuous_iff.mpr f.continuous
  exact ⟨N,⟨F,hc⟩,rfl⟩

lemma compactMap_nullhomotopic {A : Type v} [TopologicalSpace A] [CompactSpace A]
    (g : G) (f : C(A,Space G)) : ∃ y, Nonempty (f.Homotopy (ContinuousMap.const _ y)) := by
  obtain ⟨N,F,hF⟩ := compactMap_bounded f
  exact ⟨vertex (N,g),⟨((boundedContraction N g).compContinuousMap F).cast hF rfl⟩⟩

lemma sphereFillable (g : G) : Cellular.SphereFillable (Space G) := by
  intro n f
  cases n with
  | zero =>
    refine ⟨ContinuousMap.const _ (vertex (0,g)),?_⟩
    intro x
    have hx : False := by
      have he := x.2
      simp only [Metric.mem_sphere,Subsingleton.elim x.1 0,dist_self] at he
      exact zero_ne_one he
    exact hx.elim
  | succ n =>
    let := SphereTopology.sphere_nonempty n
    obtain ⟨y,⟨H⟩⟩ := compactMap_nullhomotopic g f
    obtain ⟨F,hF⟩ := SphereTopology.extends_of_nullhomotopic H.symm
    exact ⟨F,fun x => ContinuousMap.congr_fun hF x⟩

lemma contractible [Nonempty G] : ContractibleSpace (Space G) := by
  let g : G := Classical.choice ‹Nonempty G›
  let : Nonempty (Space G) := ⟨vertex (0,g)⟩
  exact Cellular.contractible_of_sphereFillable (sphereFillable g)

end

section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical
variable {G : Type u} [Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def translate (g : G) (s : Finset (ℕ × G)) : Finset (ℕ × G) := s.image (fun v => (v.1,g*v.2))

lemma translate_one (s : Finset (ℕ × G)) : translate 1 s = s := by
  simp only [translate,one_mul,Prod.mk.eta,Finset.image_id']
lemma translate_mul (g h : G) (s : Finset (ℕ × G)) : translate g (translate h s) = translate (g*h) s := by
  simp only [translate,Finset.image_image,Function.comp_def,mul_assoc]
lemma translate_mono (g : G) {s t : Finset (ℕ × G)} (h : s ⊆ t) : translate g s ⊆ translate g t :=
  Finset.image_subset_image h
lemma translate_valid (g : G) {s : Finset (ℕ × G)} (hs : s ∈ complex G) : translate g s ∈ complex G :=
  map_face (g * ·) id Function.injective_id ⟨s,hs⟩

def orbitSpan (S : Finset (Finset (ℕ × G))) : PreAbstractSimplicialComplex (ℕ × G) where
  faces := {t | t ∈ complex G ∧ ∃ g : G, ∃ s ∈ S, t ⊆ translate g s}
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨ht.1.1,?_⟩
    intro u hut hu
    obtain ⟨g,s,hs,hts⟩ := ht.2
    exact ⟨(complex G).isRelLowerSet_faces.mem_of_le ht.1 hut hu,g,s,hs,hut.trans hts⟩

lemma orbitSpan_le (S : Finset (Finset (ℕ × G))) : orbitSpan S ≤ complex G := fun _ h => h.1
lemma orbitSpan_mono {S T : Finset (Finset (ℕ × G))} (h : S ⊆ T) : orbitSpan S ≤ orbitSpan T := by
  intro t ht
  obtain ⟨g,s,hs,hts⟩ := ht.2
  exact ⟨ht.1,g,s,h hs,hts⟩
lemma orbitSpan_contains (S : Finset (Finset (ℕ × G))) {t : Finset (ℕ × G)}
    (ht : t ∈ complex G) (h : ∃ s ∈ S, t ⊆ s) : t ∈ orbitSpan S := by
  obtain ⟨s,hs,hts⟩ := h
  exact ⟨ht,1,s,hs,by rwa [translate_one]⟩
lemma orbitSpan_invariant (S : Finset (Finset (ℕ × G))) (g : G)
    {t : Finset (ℕ × G)} (ht : t ∈ orbitSpan S) : translate g t ∈ orbitSpan S := by
  obtain ⟨h,s,hs,hts⟩ := ht.2
  exact ⟨translate_valid g ht.1,g*h,s,hs,by rw [←translate_mul]; exact translate_mono g hts⟩

lemma orbitSpan_bounded (S : Finset (Finset (ℕ × G))) :
    orbitSpan S ≤ bounded G ((S.biUnion id).sup Prod.fst + 1) := by
  intro t ht
  refine ⟨ht.1,?_⟩
  intro v hv
  obtain ⟨g,s,hs,hts⟩ := ht.2
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp (hts hv)
  have hh : w.1 ≤ (S.biUnion id).sup Prod.fst := Finset.le_sup (f := Prod.fst) (Finset.mem_biUnion.mpr ⟨s,hs,hw⟩)
  exact Nat.lt_succ_of_le hh

/-- Uniform finite orbit control, not compactness of the infinite free orbit. -/
def Controlled (K : PreAbstractSimplicialComplex (ℕ × G)) : Prop :=
  ∃ S : Finset (Finset (ℕ × G)), K ≤ orbitSpan S

lemma controlled_orbitSpan (S : Finset (Finset (ℕ × G))) : Controlled (orbitSpan S) := ⟨S,le_rfl⟩
lemma controlled_bounded {K : PreAbstractSimplicialComplex (ℕ × G)} (hK : Controlled K) :
    ∃ N, K ≤ bounded G N := by
  obtain ⟨S,hS⟩ := hK
  exact ⟨_,hS.trans (orbitSpan_bounded S)⟩

lemma orbitSpan_finite_representatives (S : Finset (Finset (ℕ × G))) :
    ∃ T : Finset (Finset (ℕ × G)), ∀ t ∈ orbitSpan S, ∃ s ∈ T, ∃ g : G, t = translate g s := by
  refine ⟨S.biUnion Finset.powerset,?_⟩
  intro t ht
  obtain ⟨g,s,hs,hts⟩ := ht.2
  have hh : translate g⁻¹ t ⊆ s := by
    have hh := translate_mono g⁻¹ hts
    simpa only [translate_mul,inv_mul_cancel,translate_one] using hh
  refine ⟨translate g⁻¹ t,Finset.mem_biUnion.mpr ⟨s,hs,Finset.mem_powerset.mpr hh⟩,g,?_⟩
  rw [translate_mul,mul_inv_cancel,translate_one]

end
section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical
variable {G : Type u} {H : Type v} [Group G] [Group H]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def vertexMap (φ : G →* H) (α : ℕ → ℕ) : ℕ × G → ℕ × H := fun v => (α v.1,φ v.2)
def faceImage (φ : G →* H) (α : ℕ → ℕ) (s : Finset (ℕ × G)) : Finset (ℕ × H) := s.image (vertexMap φ α)
def imageShapes (φ : G →* H) (α : ℕ → ℕ) (S : Finset (Finset (ℕ × G))) : Finset (Finset (ℕ × H)) := S.image (faceImage φ α)

lemma faceImage_translate (φ : G →* H) (α : ℕ → ℕ) (a : G) (s : Finset (ℕ × G)) :
    faceImage φ α (translate a s) = translate (φ a) (faceImage φ α s) := by
  simp only [faceImage,translate,Finset.image_image,vertexMap,Function.comp_def,map_mul]

lemma faceImage_valid (φ : G →* H) (α : ℕ → ℕ) (hα : Function.Injective α)
    {s : Finset (ℕ × G)} (hs : s ∈ complex G) : faceImage φ α s ∈ complex H :=
  map_face φ α hα ⟨s,hs⟩

lemma faceImage_controlled (φ : G →* H) (α : ℕ → ℕ) (hα : Function.Injective α)
    (S : Finset (Finset (ℕ × G))) (s : Face (orbitSpan S)) :
    faceImage φ α s.1 ∈ orbitSpan (imageShapes φ α S) := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  refine ⟨faceImage_valid φ α hα s.2.1,φ a,faceImage φ α t,
    Finset.mem_image.mpr ⟨t,ht,rfl⟩,?_⟩
  rw [← faceImage_translate]
  exact Finset.image_subset_image hst

lemma unionFace_valid (φ : G →* H) (α β : ℕ → ℕ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    {s : Finset (ℕ × G)} (hs : s ∈ complex G)
    (hc : ∀ v ∈ s, ∀ w ∈ s, α v.1 = β w.1 → v.1 = w.1) :
    faceImage φ α s ∪ faceImage φ β s ∈ complex H := by
  refine ⟨(faceImage_valid φ α hα hs).1.mono Finset.subset_union_left,?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact (faceImage_valid φ α hα hs).2 hx hy hxy
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hvw : v = w := hs.2 hv hw (hc v hv w hw hxy)
    subst w
    apply Prod.ext
    · exact hxy
    · rfl
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hvw : w = v := hs.2 hw hv (hc w hw v hv hxy.symm)
    subst w
    apply Prod.ext
    · exact hxy
    · rfl
  · exact (faceImage_valid φ β hβ hs).2 hx hy hxy

def unionShapes (φ : G →* H) (α β : ℕ → ℕ) (S : Finset (Finset (ℕ × G))) :
    Finset (Finset (ℕ × H)) := S.image (fun s => faceImage φ α s ∪ faceImage φ β s)

lemma translate_union (a : H) (s t : Finset (ℕ × H)) : translate a (s ∪ t) = translate a s ∪ translate a t :=
  Finset.image_union _ _

lemma unionFace_controlled (φ : G →* H) (α β : ℕ → ℕ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (S : Finset (Finset (ℕ × G))) (s : Face (orbitSpan S))
    (hc : ∀ v ∈ s.1, ∀ w ∈ s.1, α v.1 = β w.1 → v.1 = w.1) :
    faceImage φ α s.1 ∪ faceImage φ β s.1 ∈ orbitSpan (unionShapes φ α β S) := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  refine ⟨unionFace_valid φ α β hα hβ s.2.1 hc,φ a,faceImage φ α t ∪ faceImage φ β t,
    Finset.mem_image.mpr ⟨t,ht,rfl⟩,?_⟩
  rw [translate_union,←faceImage_translate,←faceImage_translate]
  exact Finset.union_subset_union (Finset.image_subset_image hst) (Finset.image_subset_image hst)

/-- A fresh relayer fixes layer zero, so the ensuing straight homotopies are
based. Positive layers move above every old layer under consideration. -/
def fresh (N : ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else N+i
lemma fresh_zero (N : ℕ) : fresh N 0 = 0 := by simp [fresh]
lemma fresh_injective (N : ℕ) : Function.Injective (fresh N) := by
  intro i j h
  unfold fresh at h
  split_ifs at h with hi hj hj
  · exact hi.trans hj.symm
  · exfalso; omega
  · exfalso; omega
  · omega

lemma fresh_cross (N : ℕ) (α : ℕ → ℕ) (hα : Function.Injective α) (hzero : α 0 = 0)
    {i j : ℕ} (hi : α i < N) (h : α i = fresh N j) : i = j := by
  by_cases hj : j = 0
  · subst j
    apply hα
    simpa only [fresh_zero,hzero] using h
  · have hh : N ≤ fresh N j := by simp only [fresh,if_neg hj]; exact Nat.le_add_right _ _
    omega
end
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical unitInterval
variable {G : Type u} {H : Type v} [Group G] [Group H]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def shapeBound (S : Finset (Finset (ℕ × G))) (α : ℕ → ℕ) : ℕ :=
  (S.biUnion id).sup (fun v => α v.1) + 1
lemma orbit_below_bound (S : Finset (Finset (ℕ × G))) (α : ℕ → ℕ)
    (s : Face (orbitSpan S)) {v : ℕ × G} (hv : v ∈ s.1) : α v.1 < shapeBound S α := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp (hst hv)
  have hh : α w.1 ≤ (S.biUnion id).sup (fun v => α v.1) :=
    Finset.le_sup (f := fun v : ℕ × G => α v.1) (Finset.mem_biUnion.mpr ⟨t,ht,hw⟩)
  exact Nat.lt_succ_of_le hh

def relayerFresh (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ) : ℕ → ℕ :=
  fresh (max (shapeBound S α) (shapeBound S β))
def relayerTarget (φ : G →* H) (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ) :=
  unionShapes φ α (relayerFresh S α β) S ∪ unionShapes φ β (relayerFresh S α β) S

lemma relayerLeftValid (φ : G →* H) (S : Finset (Finset (ℕ × G)))
    (α β : ℕ → ℕ) (hα : Function.Injective α) (hα0 : α 0 = 0) (s : Face (orbitSpan S)) :
    faceImage φ α s.1 ∪ faceImage φ (relayerFresh S α β) s.1 ∈ orbitSpan (relayerTarget φ S α β) := by
  apply orbitSpan_mono Finset.subset_union_left
  apply unionFace_controlled φ α (relayerFresh S α β) hα (fresh_injective _) S s
  intro v hv w _ h
  exact fresh_cross _ α hα hα0 ((orbit_below_bound S α s hv).trans_le (le_max_left _ _)) h

lemma relayerRightValid (φ : G →* H) (S : Finset (Finset (ℕ × G)))
    (α β : ℕ → ℕ) (hβ : Function.Injective β) (hβ0 : β 0 = 0) (s : Face (orbitSpan S)) :
    faceImage φ β s.1 ∪ faceImage φ (relayerFresh S α β) s.1 ∈ orbitSpan (relayerTarget φ S α β) := by
  apply orbitSpan_mono Finset.subset_union_right
  apply unionFace_controlled φ β (relayerFresh S α β) hβ (fresh_injective _) S s
  intro v hv w _ h
  exact fresh_cross _ β hβ hβ0 ((orbit_below_bound S β s hv).trans_le (le_max_right _ _)) h

variable (φ : G →* H) (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ)
variable (hα : Function.Injective α) (hβ : Function.Injective β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
include hα hα0 in
lemma relayerLeftMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ α) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerLeftValid φ S α β hα hα0 s)
    Finset.subset_union_left (s.2.1.1.image _)
include hβ hβ0 in
lemma relayerRightMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ β) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerRightValid φ S α β hβ hβ0 s)
    Finset.subset_union_left (s.2.1.1.image _)
include hα hα0 in
lemma relayerFreshMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ (relayerFresh S α β)) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerLeftValid φ S α β hα hα0 s)
    Finset.subset_union_right (s.2.1.1.image _)

def relayerLeftMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ α) (relayerLeftMapValid φ S α β hα hα0)
def relayerRightMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ β) (relayerRightMapValid φ S α β hβ hβ0)
def relayerFreshMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ (relayerFresh S α β)) (relayerFreshMapValid φ S α β hα hα0)

def relayerLeftHomotopy : (relayerLeftMap φ S α β hα hα0).Homotopy (relayerFreshMap φ S α β hα hα0) :=
  straightHomotopy _ _ _ _ _ _ (relayerLeftValid φ S α β hα hα0)
def relayerRightHomotopy : (relayerRightMap φ S α β hβ hβ0).Homotopy (relayerFreshMap φ S α β hα hα0) :=
  straightHomotopy _ _ _ _ _ _ (relayerRightValid φ S α β hβ hβ0)

def relayerHomotopy : (relayerLeftMap φ S α β hα hα0).Homotopy (relayerRightMap φ S α β hβ hβ0) :=
  (relayerLeftHomotopy φ S α β hα hα0).trans (relayerRightHomotopy φ S α β hα hβ hα0 hβ0).symm

lemma relayerLeftPure (x : Simplicial.Space (orbitSpan S)) (g : G) (hx : x.1 = Finsupp.single (0,g) 1) :
    relayerLeftMap φ S α β hα hα0 x = relayerFreshMap φ S α β hα hα0 x := by
  apply Subtype.ext
  change x.1.mapDomain (vertexMap φ α) = x.1.mapDomain (vertexMap φ (relayerFresh S α β))
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]
  congr 1
  exact Prod.ext (hα0.trans (fresh_zero (max (shapeBound S α) (shapeBound S β))).symm) rfl
lemma relayerRightPure (x : Simplicial.Space (orbitSpan S)) (g : G) (hx : x.1 = Finsupp.single (0,g) 1) :
    relayerRightMap φ S α β hβ hβ0 x = relayerFreshMap φ S α β hα hα0 x := by
  apply Subtype.ext
  change x.1.mapDomain (vertexMap φ β) = x.1.mapDomain (vertexMap φ (relayerFresh S α β))
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]
  congr 1
  exact Prod.ext (hβ0.trans (fresh_zero (max (shapeBound S α) (shapeBound S β))).symm) rfl

lemma relayerLeftHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerLeftHomotopy φ S α β hα hα0 (t,x) = relayerLeftMap φ S α β hα hα0 x :=
  straightHomotopy_fixed _ _ _ _ _ _ (relayerLeftValid φ S α β hα hα0) x
    (relayerLeftPure φ S α β hα hα0 x g hx) t
lemma relayerRightHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerRightHomotopy φ S α β hα hβ hα0 hβ0 (t,x) = relayerRightMap φ S α β hβ hβ0 x :=
  straightHomotopy_fixed _ _ _ _ _ _ (relayerRightValid φ S α β hβ hβ0) x
    (relayerRightPure φ S α β hα hβ hα0 hβ0 x g hx) t

/-- The controlled relayer comparison is stationary on all layer-zero points. -/
theorem relayerHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerHomotopy φ S α β hα hβ hα0 hβ0 (t,x) = relayerLeftMap φ S α β hα hα0 x := by
  rw [relayerHomotopy,ContinuousMap.Homotopy.trans_apply]
  split
  · exact relayerLeftHomotopy_fixed φ S α β hα hα0 x g hx _
  · rw [ContinuousMap.Homotopy.symm_apply]
    exact (relayerRightHomotopy_fixed φ S α β hα hβ hα0 hβ0 x g hx _).trans
      ((relayerRightPure φ S α β hα hβ hα0 hβ0 x g hx).trans
        (relayerLeftPure φ S α β hα hα0 x g hx).symm)
end GroupRingTopology.Milnor

/-! Functoriality and product additivity on actual higher homotopy groups.
This is geometric support for the literal finite idempotent diagrams. -/
namespace GroupRingTopology.HomotopyFunctor
open scoped Topology Topology.Homotopy
variable {N : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}

def loopMap (f : C(X,Y)) (hf : f x = y) (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.1,fun t ht => by change f (p t) = y; rw [GenLoop.boundary p t ht,hf]⟩

lemma loopMap_homotopic (f : C(X,Y)) (hf : f x = y) {p q : GenLoop N X x}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (loopMap f hf p) (loopMap f hf q) :=
  h.comp_continuousMap f

def map (f : C(X,Y)) (hf : f x = y) : HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (loopMap f hf) (fun _ _ h => loopMap_homotopic f hf h)

@[simp] lemma map_mk (f : C(X,Y)) (hf : f x = y) (p : GenLoop N X x) :
    map f hf (Quotient.mk' p) = Quotient.mk' (loopMap f hf p) := rfl

lemma loopMap_const (f : C(X,Y)) (hf : f x = y) :
    loopMap (N := N) f hf GenLoop.const = GenLoop.const := by
  ext t
  exact hf

lemma loopMap_transAt [DecidableEq N] (i : N) (f : C(X,Y)) (hf : f x = y)
    (p q : GenLoop N X x) :
    loopMap f hf (GenLoop.transAt i p q) = GenLoop.transAt i (loopMap f hf p) (loopMap f hf q) := by
  ext t
  change f (if (t i : ℝ) ≤ 1/2 then p _ else q _) =
    if (t i : ℝ) ≤ 1/2 then f (p _) else f (q _)
  split <;> rfl

def mapHom [DecidableEq N] [Nonempty N] (f : C(X,Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := map f hf
  map_one' := by
    change Quotient.mk' (loopMap f hf GenLoop.const) = Quotient.mk' GenLoop.const
    exact congrArg Quotient.mk' (loopMap_const f hf)
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    have h₁ := HomotopyGroup.mul_spec (i := Classical.arbitrary N) (p := p) (q := q)
    have h₂ := HomotopyGroup.mul_spec (i := Classical.arbitrary N)
      (p := loopMap f hf p) (q := loopMap f hf q)
    exact (congrArg (map f hf) h₁).trans
      ((congrArg Quotient.mk' (loopMap_transAt (Classical.arbitrary N) f hf q p)).trans h₂.symm)

lemma map_id (a : HomotopyGroup N X x) : map (y := x) (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with | h p =>
  exact congrArg Quotient.mk' (by ext t; rfl)

lemma map_comp {Z : Type*} [TopologicalSpace Z] {z : Z}
    (f : C(X,Y)) (hf : f x = y) (g : C(Y,Z)) (hg : g y = z)
    (a : HomotopyGroup N X x) :
    map g hg (map f hf a) = map (g.comp f) (by change g (f x) = z; rw [hf,hg]) a := by
  induction a using Quotient.inductionOn with | h p =>
  rfl

lemma map_const [DecidableEq N] [Nonempty N] (a : HomotopyGroup N X x) :
    map (ContinuousMap.const X y) rfl a = 1 := by
  induction a using Quotient.inductionOn with | h p =>
  rfl

variable {Z : Type*} [TopologicalSpace Z] {z : Z}

def loopPair (p : GenLoop N X x) (q : GenLoop N Y y) : GenLoop N (X × Y) (x,y) :=
  ⟨p.1.prodMk q.1,fun t ht => Prod.ext (GenLoop.boundary p t ht) (GenLoop.boundary q t ht)⟩

lemma pair_homotopic {p p' : GenLoop N X x} {q q' : GenLoop N Y y}
    (h : GenLoop.Homotopic p p') (k : GenLoop.Homotopic q q') :
    GenLoop.Homotopic (loopPair p q) (loopPair p' q') := by
  rcases h with ⟨h⟩
  rcases k with ⟨k⟩
  refine ⟨{ toHomotopy := h.toHomotopy.prodMk k.toHomotopy,prop' := ?_ }⟩
  intro t a ha
  exact Prod.ext (h.eq_fst t ha) (k.eq_fst t ha)

lemma product_ext (a b : HomotopyGroup N (X × Y) (x,y))
    (h₁ : map ((ContinuousMap.fst : C(X × Y,X))) rfl a = map ((ContinuousMap.fst : C(X × Y,X))) rfl b)
    (h₂ : map ((ContinuousMap.snd : C(X × Y,Y))) rfl a = map ((ContinuousMap.snd : C(X × Y,Y))) rfl b) : a = b := by
  induction a using Quotient.inductionOn with | h p =>
  induction b using Quotient.inductionOn with | h q =>
  apply Quotient.sound
  have hh := pair_homotopic (Quotient.exact h₁) (Quotient.exact h₂)
  exact hh

/-- The diagonal class in a product is the product of its two coordinate
classes. This is a statement about genuine based homotopy groups. -/
lemma diagonal_split [DecidableEq N] [Nonempty N] (a : HomotopyGroup N X x) :
    map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl a =
      (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl a) *
      (map (y := (x,x)) ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl a) := by
  apply product_ext
  · change mapHom ((ContinuousMap.fst : C(X × X,X))) rfl _ = mapHom ((ContinuousMap.fst : C(X × X,X))) rfl _
    rw [map_mul]
    change map (y := x) _ _ (map (y := (x,x)) _ _ a) =
      map (y := x) _ _ (map (y := (x,x)) _ _ a) * map (y := x) _ _ (map (y := (x,x)) _ _ a)
    erw [map_comp, map_comp, map_comp]
    change map (y := x) (ContinuousMap.id X) rfl a = map (y := x) (ContinuousMap.id X) rfl a * map (y := x) (ContinuousMap.const X x) rfl a
    erw [map_id,map_const,mul_one]
  · change mapHom ((ContinuousMap.snd : C(X × X,X))) rfl _ = mapHom ((ContinuousMap.snd : C(X × X,X))) rfl _
    rw [map_mul]
    change map (y := x) _ _ (map (y := (x,x)) _ _ a) =
      map (y := x) _ _ (map (y := (x,x)) _ _ a) * map (y := x) _ _ (map (y := (x,x)) _ _ a)
    erw [map_comp, map_comp, map_comp]
    change map (y := x) (ContinuousMap.id X) rfl a = map (y := x) (ContinuousMap.const X x) rfl a * map (y := x) (ContinuousMap.id X) rfl a
    erw [map_id,map_const,one_mul]

/-- Product additivity requires no homological comparison or Hurewicz theorem. -/
theorem product_additivity [DecidableEq N] [Nonempty N] (F : C(X × X,Y))
    (hF : F (x,x) = y) (a : HomotopyGroup N X x) :
    map (F.comp ((ContinuousMap.id X).prodMk (ContinuousMap.id X))) hF a =
      map (F.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X x))) hF a *
      map (F.comp ((ContinuousMap.const X x).prodMk (ContinuousMap.id X))) hF a := by
  have h := map_comp (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl F hF a
  rw [← h,diagonal_split]
  change mapHom (N := N) F hF (_ * _) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) (map_comp _ _ _ _ a) (map_comp _ _ _ _ a)
end GroupRingTopology.HomotopyFunctor

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.HomotopyFunctor
open scoped Topology Topology.Homotopy
variable {N : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}
lemma map_eq_of_homotopy (f g : C(X,Y)) (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t,x) = y) (a : HomotopyGroup N X x) :
    map f hf a = map g hg a := by
  induction a using Quotient.inductionOn with | h p =>
  apply Quotient.sound
  refine ⟨{ toHomotopy := H.compContinuousMap p.1,prop' := ?_ }⟩
  intro t z hz
  change H (t,p z) = f (p z)
  rw [GenLoop.boundary p z hz,hH,hf]
end GroupRingTopology.HomotopyFunctor
namespace GroupRingTopology.Milnor

section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical Topology.Homotopy
variable (G : Type u) [Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

abbrev Shapes := Finset (Finset (ℕ × G))
def basedShapes (S : Shapes G) : Shapes G := insert {(0,1)} S
def stage (S : Shapes G) := orbitSpan (basedShapes G S)

lemma stage_mono {S T : Shapes G} (h : S ⊆ T) : stage G S ≤ stage G T :=
  orbitSpan_mono (Finset.insert_subset_insert _ h)

lemma stage_point_face (S : Shapes G) : {(0,1)} ∈ stage G S := by
  apply orbitSpan_contains (basedShapes G S)
  · exact ⟨Finset.singleton_nonempty _,by simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (0,(1:G))⟩
  · exact ⟨{(0,1)},Finset.mem_insert_self _ _,Finset.Subset.refl _⟩

def stagePoint (S : Shapes G) : Simplicial.Space (stage G S) :=
  ⟨Finsupp.single (0,1) 1,by intro w; simp only [Finsupp.single_apply]; split_ifs <;> norm_num,
    by simp,by simpa only [Finsupp.support_single _ one_ne_zero] using stage_point_face G S⟩

def stageIncl (S T : Shapes G) (h : S ⊆ T) : C(Simplicial.Space (stage G S),Simplicial.Space (stage G T)) :=
  ⟨inclusion _ _ (fun _ hs => stage_mono G h hs),continuous_inclusion _ _ _⟩

lemma stageIncl_point (S T : Shapes G) (h : S ⊆ T) : stageIncl G S T h (stagePoint G S) = stagePoint G T := rfl

variable (N : Type v) [DecidableEq N] [Nonempty N]
def stageHom (S T : Shapes G) (h : S ⊆ T) :
    HomotopyGroup N (Simplicial.Space (stage G S)) (stagePoint G S) →*
      HomotopyGroup N (Simplicial.Space (stage G T)) (stagePoint G T) :=
  HomotopyFunctor.mapHom (stageIncl G S T h) rfl

instance : DirectedSystem (fun S : Shapes G => HomotopyGroup N (Simplicial.Space (stage G S)) (stagePoint G S))
    (fun S T h => stageHom G N S T h) where
  map_self _ a := by
    exact HomotopyFunctor.map_id a
  map_map _ _ _ h₁ h₂ a := by
    exact HomotopyFunctor.map_comp _ _ _ _ a

end

section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical unitInterval
variable {G : Type u} [Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

instance : MulAction G (Space G) where
  smul g x := map (g * ·) id Function.injective_id x
  one_smul x := by
    change map (1 * ·) id Function.injective_id x = x
    apply Subtype.ext
    change x.1.mapDomain (fun v => (v.1,1*v.2)) = x.1
    rw [show (fun v : ℕ × G => (v.1,1*v.2)) = id from funext (fun v => Prod.ext rfl (one_mul v.2))]
    exact Finsupp.mapDomain_id
  mul_smul g h x := by
    change map ((g*h) * ·) id Function.injective_id x = map (g * ·) id Function.injective_id (map (h * ·) id Function.injective_id x)
    rw [map_comp]
    have he : (fun a => (g*h)*a) = ((g * ·) ∘ (h * ·)) := funext (mul_assoc g h)
    rw [he]
    rfl

instance : ContinuousConstSMul G (Space G) where
  continuous_const_smul g := (map (g * ·) id Function.injective_id).continuous

lemma smul_weight (g : G) (x : Space G) (v : ℕ × G) : (g • x).1 (v.1,g*v.2) = x.1 v := by
  change (x.1.mapDomain (fun w => (w.1,g*w.2))) (v.1,g*v.2) = x.1 v
  apply Finsupp.mapDomain_apply (f := fun w : ℕ × G => (w.1,g*w.2))
  intro a b hab
  have hfst := congrArg (fun p : ℕ × G => p.1) hab
  have hsnd := congrArg (fun p : ℕ × G => p.2) hab
  exact Prod.ext hfst (mul_left_cancel hsnd)

lemma smul_weight_inv (g : G) (x : Space G) (v : ℕ × G) : (g • x).1 v = x.1 (v.1,g⁻¹*v.2) := by
  simpa only [mul_inv_cancel_left] using smul_weight g x (v.1,g⁻¹*v.2)

lemma exists_disjoint_nhds (x : Space G) :
    ∃ U ∈ 𝓝 x, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  obtain ⟨v,hv⟩ := Simplicial.support_nonempty x.2.2.1
  let U : Set (Space G) := {y | 0 < y.1 v}
  have hx : x ∈ U := lt_of_le_of_ne (x.2.1 v) (Ne.symm (Finsupp.mem_support_iff.mp hv))
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_eval (complex G) v)
  refine ⟨U,hU.mem_nhds hx,?_⟩
  intro g hg
  obtain ⟨z,⟨y,hy,rfl⟩,hgy⟩ := hg
  have h1 : v ∈ y.1.support := Finsupp.mem_support_iff.mpr (ne_of_gt hy)
  have h2 : (v.1,g⁻¹*v.2) ∈ y.1.support := by
    apply Finsupp.mem_support_iff.mpr
    have hp : 0 < (g • y).1 v := hgy
    rw [smul_weight_inv] at hp
    exact ne_of_gt hp
  have he := congrArg Prod.snd (y.2.2.2.2 h1 h2 rfl)
  have hi : g⁻¹ = 1 := (mul_right_cancel (he.symm.trans (one_mul v.2).symm))
  exact inv_eq_one.mp hi

lemma quotientCovering : IsQuotientCoveringMap
    (Quotient.mk (MulAction.orbitRel G (Space G))) G where
  __ := isQuotientMap_quotient_mk'
  continuous_const_smul g := continuous_const_smul g
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint := exists_disjoint_nhds

end
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical
variable (G : Type u) [Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

abbrev Stage (S : Shapes G) := Simplicial.Space (stage G S)

def stageFull (S : Shapes G) : C(Stage G S,Space G) :=
  ⟨inclusion _ _ (fun _ h => orbitSpan_le _ h),continuous_inclusion _ _ _⟩
lemma stageFull_embedding (S : Shapes G) : IsClosedEmbedding (stageFull G S) :=
  inclusion_closedEmbedding _ _ (fun _ h => orbitSpan_le _ h)

lemma stage_translate (S : Shapes G) (g : G) (s : Face (stage G S)) :
    s.1.image (fun v => (v.1,g*v.2)) ∈ stage G S := orbitSpan_invariant _ g s.2

def stageSmul (S : Shapes G) (g : G) : C(Stage G S,Stage G S) :=
  Simplicial.mapC _ _ (fun v => (v.1,g*v.2)) (stage_translate G S g)

instance stageAction (S : Shapes G) : MulAction G (Stage G S) where
  smul g x := stageSmul G S g x
  one_smul x := by
    apply Subtype.ext
    change x.1.mapDomain (fun v => (v.1,1*v.2)) = x.1
    rw [show (fun v : ℕ × G => (v.1,1*v.2)) = id from funext (fun v => Prod.ext rfl (one_mul v.2))]
    exact Finsupp.mapDomain_id
  mul_smul g h x := by
    apply Subtype.ext
    change x.1.mapDomain (fun v => (v.1,(g*h)*v.2)) =
      (x.1.mapDomain (fun v => (v.1,h*v.2))).mapDomain (fun v => (v.1,g*v.2))
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext v
    exact Prod.ext rfl (mul_assoc _ _ _)

instance stageContinuousAction (S : Shapes G) : ContinuousConstSMul G (Stage G S) where
  continuous_const_smul g := (stageSmul G S g).continuous

lemma stageFull_smul (S : Shapes G) (g : G) (x : Stage G S) :
    stageFull G S (g • x) = g • stageFull G S x := rfl
lemma stageIncl_smul (S T : Shapes G) (h : S ⊆ T) (g : G) (x : Stage G S) :
    stageIncl G S T h (g • x) = g • stageIncl G S T h x := rfl

/-- Any one compact set is contained in a finite-orbit Milnor stage. -/
lemma compact_controlled {K : Set (Space G)} (hK : IsCompact K) :
    ∃ S : Shapes G, K ⊆ Set.range (stageFull G S) := by
  obtain ⟨V,hV⟩ := Simplicial.compact_bounded_vertices (complex G) hK
  refine ⟨V.powerset,?_⟩
  intro x hx
  have hm : x.1.support ∈ stage G V.powerset := by
    apply orbitSpan_contains (basedShapes G V.powerset) x.2.2.2
    exact ⟨x.1.support,Finset.mem_insert_of_mem (Finset.mem_powerset.mpr (hV x hx)),Finset.Subset.refl _⟩
  exact ⟨⟨x.1,x.2.1,x.2.2.1,hm⟩,rfl⟩

/-- Arbitrarily many translates of a compact set have ONE controlled target. -/
lemma compact_orbit_controlled {K : Set (Space G)} (hK : IsCompact K) :
    ∃ S : Shapes G, ∀ g : G, (g • ·) '' K ⊆ Set.range (stageFull G S) := by
  obtain ⟨S,hS⟩ := compact_controlled G hK
  refine ⟨S,?_⟩
  intro g y hy
  obtain ⟨x,hx,rfl⟩ := hy
  obtain ⟨z,rfl⟩ := hS hx
  exact ⟨g • z,stageFull_smul G S g z⟩

variable {X : Type v} [TopologicalSpace X] [MulAction G X]
/-- A compact fundamental set need not be disjoint or a strict domain. -/
def CompactFundamentalSet : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, ∃ y ∈ K, x = g • y

lemma equivariant_controlled (hX : CompactFundamentalSet G (X := X))
    (f : C(X,Space G)) (hf : ∀ (g : G) x, f (g • x) = g • f x) :
    ∃ S : Shapes G, Set.range f ⊆ Set.range (stageFull G S) := by
  obtain ⟨K,hK,hcov⟩ := hX
  obtain ⟨S,hS⟩ := compact_orbit_controlled G (hK.image f.continuous)
  refine ⟨S,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨g,y,hy,rfl⟩ := hcov x
  rw [hf]
  exact hS g ⟨f y,⟨y,hy,rfl⟩,rfl⟩

/-- Factoring through a stage preserves topology and equivariance, rather than
only factoring an underlying set map. -/
def factorStage (f : C(X,Space G)) (S : Shapes G)
    (hf : Set.range f ⊆ Set.range (stageFull G S)) : C(X,Stage G S) where
  toFun x := (hf (Set.mem_range_self x)).choose
  continuous_toFun := (stageFull_embedding G S).isEmbedding.continuous_iff.mpr (by
    convert f.continuous using 1
    funext x
    exact (hf (Set.mem_range_self x)).choose_spec)
omit [MulAction G X] in
lemma factorStage_spec (f : C(X,Space G)) (S : Shapes G)
    (hf : Set.range f ⊆ Set.range (stageFull G S)) (x : X) :
    stageFull G S (factorStage G f S hf x) = f x := (hf (Set.mem_range_self x)).choose_spec
lemma factorStage_smul (f : C(X,Space G)) (S : Shapes G)
    (hf : Set.range f ⊆ Set.range (stageFull G S))
    (he : ∀ (g : G) x, f (g • x) = g • f x) (g : G) (x : X) :
    factorStage G f S hf (g • x) = g • factorStage G f S hf x := by
  apply (stageFull_embedding G S).injective
  rw [factorStage_spec,stageFull_smul,factorStage_spec,he]
end GroupRingTopology.Milnor
open Set Metric Topology
namespace GroupRingTopology.Attachment
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1
abbrev OpenDisk (n : ℕ) := ball (0 : Fin n → ℝ) 1

def boundary (n : ℕ) : Sphere n → Disk n :=
  fun x => ⟨x.1, sphere_subset_closedBall x.2⟩
def interior (n : ℕ) : OpenDisk n → Disk n :=
  fun x => ⟨x.1, ball_subset_closedBall x.2⟩
lemma continuous_boundary (n : ℕ) : Continuous (boundary n) :=
  continuous_subtype_val.subtype_mk _
lemma continuous_interior (n : ℕ) : Continuous (interior n) :=
  continuous_subtype_val.subtype_mk _
lemma boundary_closedEmbedding (n : ℕ) : IsClosedEmbedding (boundary n) :=
  (continuous_boundary n).isClosedEmbedding (fun _ _ h => Subtype.ext (congrArg (fun z : Disk n => z.1) h))

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,X))

/-- The points of an adjunction are the old points and the interiors of the new disks. -/
def Space (_a : ι → C(Sphere n,X)) := X ⊕ (Σ _ : ι, OpenDisk n)

noncomputable def quotient : (X ⊕ (Σ _ : ι, Disk n)) → Space a := by
  classical
  intro z
  cases z with
  | inl x => exact Sum.inl x
  | inr p =>
    exact if h : p.2.1 ∈ ball (0 : Fin n → ℝ) 1 then Sum.inr ⟨p.1,⟨p.2.1,h⟩⟩
    else Sum.inl (a p.1 ⟨p.2.1,by
      have hd := p.2.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hd (le_of_not_gt h)⟩)

instance : TopologicalSpace (Space a) := TopologicalSpace.coinduced (quotient a) inferInstance

@[simp] lemma quotient_inl (x : X) : quotient a (Sum.inl x) = Sum.inl x := rfl

@[simp] lemma quotient_interior (i : ι) (x : OpenDisk n) :
    quotient a (Sum.inr ⟨i,interior n x⟩) = Sum.inr ⟨i,x⟩ := by
  classical
  dsimp only [quotient, interior]
  erw [dif_pos x.2]

@[simp] lemma quotient_boundary (i : ι) (x : Sphere n) :
    quotient a (Sum.inr ⟨i,boundary n x⟩) = Sum.inl (a i x) := by
  classical
  have hx : x.1 ∉ ball (0 : Fin n → ℝ) 1 := by
    simpa only [mem_ball,mem_sphere,x.2,lt_self_iff_false,not_false_eq_true] using
      (sphere_disjoint_ball.notMem_of_mem_left x.2)
  dsimp only [quotient, boundary]
  erw [dif_neg hx]

lemma quotient_surjective : Function.Surjective (quotient a) := by
  intro z
  cases z with
  | inl x => exact ⟨Sum.inl x,rfl⟩
  | inr p => exact ⟨Sum.inr ⟨p.1,interior n p.2⟩,quotient_interior a p.1 p.2⟩

lemma continuous_quotient : Continuous (quotient a) := continuous_coinduced_rng

/-- The old space embeds as a closed subspace of the adjunction. -/
def base : X → Space a := Sum.inl
noncomputable def cell (i : ι) : C(Disk n,Space a) :=
  ⟨fun x => quotient a (Sum.inr ⟨i,x⟩),
    (continuous_quotient a).comp (continuous_inr.comp continuous_sigmaMk)⟩
lemma continuous_base : Continuous (base a) :=
  (continuous_quotient a).comp continuous_inl

@[simp] lemma cell_boundary (i : ι) (x : Sphere n) :
    cell a i (boundary n x) = base a (a i x) := quotient_boundary a i x
@[simp] lemma cell_interior (i : ι) (x : OpenDisk n) :
    cell a i (interior n x) = Sum.inr ⟨i,x⟩ := quotient_interior a i x

lemma continuous_iff {Y : Type w} [TopologicalSpace Y] (f : Space a → Y) :
    Continuous f ↔ Continuous (f ∘ base a) ∧ ∀ i, Continuous (f ∘ cell a i) := by
  change Continuous[TopologicalSpace.coinduced (quotient a) inferInstance,_] f ↔ _
  rw [continuous_coinduced_dom,continuous_sum_dom,continuous_sigma_iff]
  rfl

lemma isClosed_iff (S : Set (Space a)) :
    IsClosed S ↔ IsClosed (base a ⁻¹' S) ∧ ∀ i, IsClosed (cell a i ⁻¹' S) := by
  change @IsClosed _ (TopologicalSpace.coinduced (quotient a) inferInstance) S ↔ _
  rw [isClosed_coinduced,isClosed_sum_iff,isClosed_sigma_iff]
  rfl

lemma cell_preimage_base_image (i : ι) (S : Set X) :
    cell a i ⁻¹' (base a '' S) = boundary n '' ((a i) ⁻¹' S) := by
  classical
  ext d
  by_cases h : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have hd : d = interior n ⟨d.1,h⟩ := rfl
    rw [hd]
    simp only [Set.mem_preimage,cell_interior,base,Set.mem_image]
    constructor
    · rintro ⟨x,_,hx⟩; cases hx
    · rintro ⟨x,_,hx⟩
      have heq := congrArg (fun d : Disk n => d.1) hx
      have hh : x.1 ∈ ball (0 : Fin n → ℝ) 1 := heq ▸ h
      exact False.elim ((sphere_disjoint_ball.notMem_of_mem_left x.2) hh)
  · let x : Sphere n := ⟨d.1,by
      have hd := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hd (le_of_not_gt h)⟩
    have hd : d = boundary n x := rfl
    rw [hd]
    simp only [Set.mem_preimage,cell_boundary,Set.mem_image]
    constructor
    · rintro ⟨y,hy,hyx⟩
      have heq : y = a i x := Sum.inl_injective hyx
      exact ⟨x,heq ▸ hy,rfl⟩
    · rintro ⟨y,hy,hyx⟩
      have heq : y = x := Subtype.ext (congrArg (fun d : Disk n => d.1) hyx)
      subst y
      exact ⟨a i x,hy,rfl⟩

lemma base_isClosedMap : IsClosedMap (base a) := by
  intro S hS
  rw [isClosed_iff]
  constructor
  · change IsClosed ((Sum.inl : X → X ⊕ (Σ _ : ι, OpenDisk n)) ⁻¹' Sum.inl '' S)
    simpa only [Set.preimage_image_eq _ Sum.inl_injective] using hS
  · intro i
    rw [cell_preimage_base_image]
    exact (boundary_closedEmbedding n).isClosedMap _ (hS.preimage (a i).continuous)

lemma base_closedEmbedding : IsClosedEmbedding (base a) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_base a) Sum.inl_injective (base_isClosedMap a)

/-- The universal mapping property, with all attaching equations explicit. -/
noncomputable def lift {Y : Type w} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(Disk n,Y)) (h : ∀ i x, g i (boundary n x) = f (a i x)) : C(Space a,Y) := by
  classical
  let F : Space a → Y := Sum.elim f (fun p => g p.1 (interior n p.2))
  have hcell (i : ι) : F ∘ cell a i = g i := by
    funext d
    by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : d = interior n ⟨d.1,hd⟩ := rfl
      rw [heq,Function.comp_apply,cell_interior]
      rfl
    · let x : Sphere n := ⟨d.1,by
        have hm := d.2
        simp only [mem_closedBall,mem_ball,mem_sphere] at *
        exact le_antisymm hm (le_of_not_gt hd)⟩
      have heq : d = boundary n x := rfl
      rw [heq,Function.comp_apply,cell_boundary]
      exact (h i x).symm
  exact ⟨F,(continuous_iff a F).mpr ⟨f.continuous,fun i => by rw [hcell]; exact (g i).continuous⟩⟩

@[simp] lemma lift_base {Y : Type w} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(Disk n,Y)) (h : ∀ i x, g i (boundary n x) = f (a i x)) (x : X) :
    lift a f g h (base a x) = f x := rfl

@[simp] lemma lift_cell {Y : Type w} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(Disk n,Y)) (h : ∀ i x, g i (boundary n x) = f (a i x))
    (i : ι) (d : Disk n) : lift a f g h (cell a i d) = g i d := by
  classical
  by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d = interior n ⟨d.1,hd⟩ := rfl
    rw [heq,cell_interior]
    rfl
  · let x : Sphere n := ⟨d.1,by
      have hm := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have heq : d = boundary n x := rfl
    rw [heq,cell_boundary,lift_base,h]

lemma lift_unique {Y : Type w} [TopologicalSpace Y] (f g : C(Space a,Y))
    (hb : ∀ x, f (base a x) = g (base a x))
    (hc : ∀ i d, f (cell a i d) = g (cell a i d)) : f = g := by
  ext z
  obtain ⟨q,rfl⟩ := quotient_surjective a z
  cases q with
  | inl x => exact hb x
  | inr p => exact hc p.1 p.2

lemma interior_openEmbedding (n : ℕ) : IsOpenEmbedding (interior n) :=
  .inclusion ball_subset_closedBall (isOpen_ball.preimage continuous_subtype_val)

/-- Open disks are inserted as genuine open embeddings. -/
def openCell (i : ι) : OpenDisk n → Space a := fun x => Sum.inr ⟨i,x⟩

lemma openCell_eq (i : ι) : openCell a i = cell a i ∘ interior n := by
  funext x
  exact (cell_interior a i x).symm

lemma quotient_preimage_openCell_image (i : ι) (S : Set (OpenDisk n)) :
    quotient a ⁻¹' (openCell a i '' S) =
      Sum.inr '' (Sigma.mk i '' (interior n '' S)) := by
  classical
  ext q
  cases q with
  | inl x =>
    simp only [Set.mem_preimage,quotient_inl,Set.mem_image]
    constructor
    · rintro ⟨y,_,hy⟩; cases hy
    · rintro ⟨y,_,hy⟩; cases hy
  | inr p =>
    by_cases hp : p.2.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : p.2 = interior n ⟨p.2.1,hp⟩ := rfl
      change (∃ x ∈ S, openCell a i x = quotient a (Sum.inr ⟨p.1,p.2⟩)) ↔ _
      rw [heq,quotient_interior]
      constructor
      · rintro ⟨x,hx,he⟩
        have hh : (⟨i,x⟩ : Σ _ : ι, OpenDisk n) = ⟨p.1,⟨p.2.1,hp⟩⟩ := Sum.inr_injective he
        have hh' : (⟨i,interior n x⟩ : Σ _ : ι, Disk n) = ⟨p.1,p.2⟩ :=
          congrArg (fun p : Σ _ : ι, OpenDisk n => (⟨p.1,interior n p.2⟩ : Σ _ : ι, Disk n)) hh
        exact ⟨⟨i,interior n x⟩,⟨interior n x,⟨x,hx,rfl⟩,rfl⟩,congrArg Sum.inr hh'⟩
      · rintro ⟨y,⟨d,⟨x,hx,hxd⟩,hdy⟩,hy⟩
        subst d; subst y
        have hh := Sum.inr_injective hy
        have hi : i = p.1 := congrArg Sigma.fst hh
        subst i
        have hh' : interior n x = interior n ⟨p.2.1,hp⟩ := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
        have he : x = ⟨p.2.1,hp⟩ := (interior_openEmbedding n).injective hh'
        exact ⟨x,hx,by subst x; rfl⟩
    · let x : Sphere n := ⟨p.2.1,by
        have hm := p.2.2
        simp only [mem_closedBall,mem_ball,mem_sphere] at *
        exact le_antisymm hm (le_of_not_gt hp)⟩
      have heq : p.2 = boundary n x := rfl
      change (∃ y ∈ S, openCell a i y = quotient a (Sum.inr ⟨p.1,p.2⟩)) ↔ _
      rw [heq,quotient_boundary]
      constructor
      · rintro ⟨y,_,hy⟩; cases hy
      · rintro ⟨y,⟨d,⟨z,_,hzd⟩,hdy⟩,hy⟩
        subst d; subst y
        have hh := Sum.inr_injective hy
        have hi : i = p.1 := congrArg Sigma.fst hh
        subst i
        have hh' : interior n z = boundary n x := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
        have hh'' := congrArg (fun d : Disk n => d.1) hh'
        exact False.elim (hp (hh'' ▸ z.2))

lemma openCell_openEmbedding (i : ι) : IsOpenEmbedding (openCell a i) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · rw [openCell_eq]
    exact (cell a i).continuous.comp (continuous_interior n)
  · intro x y h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr_injective h)).2
  · intro S hS
    change @IsOpen _ (TopologicalSpace.coinduced (quotient a) inferInstance) _
    rw [isOpen_coinduced,quotient_preimage_openCell_image]
    exact isOpenMap_inr _ (isOpenMap_sigmaMk _ ((interior_openEmbedding n).isOpenMap S hS))

/-- Real-valued maps on the old space extend over any family of attached disks. -/
lemma exists_real_extension (f : C(X,ℝ)) :
    ∃ F : C(Space a,ℝ), ∀ x, F (base a x) = f x := by
  classical
  have hi (i : ι) : ∃ g : C(Disk n,ℝ), ∀ x, g (boundary n x) = f (a i x) := by
    obtain ⟨g,hg⟩ := (f.comp (a i)).exists_extension' (boundary_closedEmbedding n)
    exact ⟨g,fun x => congrFun hg x⟩
  choose g hg using hi
  exact ⟨lift a f g hg,fun x => lift_base a f g hg x⟩

/-- Functional Hausdorffness is convenient for iterated attachments: separating
functions, unlike chosen open neighborhoods, extend across every new disk. -/
def RealSeparated (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ x y : Y, x ≠ y → ∃ f : C(Y,ℝ), f x ≠ f y

lemma RealSeparated.t2Space {Y : Type*} [TopologicalSpace Y] (h : RealSeparated Y) :
    T2Space Y := by
  constructor
  intro x y hxy
  obtain ⟨f,hf⟩ := h x y hxy
  exact separated_by_continuous f.continuous hf

lemma realSeparated_of_tychonoff {Y : Type*} [TopologicalSpace Y]
    [T1Space Y] [CompletelyRegularSpace Y] : RealSeparated Y := by
  intro x y hxy
  obtain ⟨f,hf,hfx,hfy⟩ := CompletelyRegularSpace.completely_regular x {y} isClosed_singleton
    (by simpa only [Set.mem_singleton_iff] using hxy)
  refine ⟨⟨fun q => (f q : ℝ),continuous_subtype_val.comp hf⟩,?_⟩
  change (f x : ℝ) ≠ (f y : ℝ)
  rw [hfx,hfy (Set.mem_singleton y)]
  norm_num

lemma exists_interior_separator [T1Space X] (i : ι) (x : OpenDisk n) (z : Space a)
    (hxz : openCell a i x ≠ z) :
    ∃ F : C(Space a,ℝ), F (openCell a i x) = 1 ∧ F z = 0 := by
  classical
  let K : Set (Disk n) := Set.range (boundary n) ∪ cell a i ⁻¹' {z}
  have hKc : IsClosed K := by
    -- Only the part of the inverse image inside this disk is used; the point
    -- set is closed directly, without presupposing Hausdorffness of the adjunction.
    have hz : IsClosed (cell a i ⁻¹' {z}) := by
      cases z with
      | inl y =>
        have heq : ({Sum.inl y} : Set (Space a)) = base a '' {y} := by
          exact (Set.image_singleton (f := base a) (a := y)).symm
        erw [heq,cell_preimage_base_image]
        -- For base points this will follow from a T1 hypothesis below.
        exact (boundary_closedEmbedding n).isClosedMap _
          (isClosed_singleton.preimage (a i).continuous)
      | inr p =>
        have heq : ({Sum.inr p} : Set (Space a)) = openCell a p.1 '' {p.2} := by
          exact (Set.image_singleton (f := openCell a p.1) (a := p.2)).symm
        have hpre := quotient_preimage_openCell_image a p.1 ({p.2} : Set (OpenDisk n))
        have hclosed : IsClosed (quotient a ⁻¹' {Sum.inr p}) := by
          erw [heq,hpre]
          exact isClosedMap_inr _ (isClosedMap_sigmaMk _
            ((isCompact_singleton.image (continuous_interior n)).isClosed))
        exact hclosed.preimage (continuous_inr.comp continuous_sigmaMk)
    exact (boundary_closedEmbedding n).isClosed_range.union hz
  have hxK : interior n x ∉ K := by
    rintro (hx | hx)
    · obtain ⟨s,hs⟩ := hx
      have heq := congrArg (fun d : Disk n => d.1) hs
      exact sphere_disjoint_ball.notMem_of_mem_left s.2 (heq ▸ x.2)
    · apply hxz
      change cell a i (interior n x) = z at hx
      exact (cell_interior a i x).symm.trans hx
  obtain ⟨f,hf0,hf1,_⟩ := exists_continuous_zero_one_of_isClosed hKc
    (isClosed_singleton (x := interior n x)) (Set.disjoint_singleton_right.mpr hxK)
  let g : ι → C(Disk n,ℝ) := fun j => if j = i then f else ContinuousMap.const _ 0
  have hgb (j : ι) (s : Sphere n) : g j (boundary n s) = (0 : ℝ) := by
    dsimp [g]
    split_ifs with hji
    · exact hf0 (Set.mem_union_left _ (Set.mem_range_self s))
    · rfl
  let F : C(Space a,ℝ) := lift a (ContinuousMap.const _ 0) g hgb
  have hFcell (j : ι) (d : Disk n) : F (cell a j d) = g j d := lift_cell a _ _ _ j d
  refine ⟨F,?_,?_⟩
  · change F (Sum.inr ⟨i,x⟩) = 1
    rw [← cell_interior a i x,hFcell]
    simpa only [g,if_pos rfl,Pi.one_apply] using hf1 (Set.mem_singleton _)
  · cases z with
    | inl y => exact lift_base a _ _ _ y
    | inr p =>
      rw [← cell_interior a p.1 p.2,hFcell]
      by_cases hpi : p.1 = i
      · have hm : interior n p.2 ∈ K := by
          right
          change cell a i (interior n p.2) = Sum.inr p
          rw [cell_interior]
          cases p with
          | mk j y =>
            dsimp only at hpi
            subst j
            rfl
        simpa only [g,if_pos hpi,Pi.zero_apply] using hf0 hm
      · simp only [g,if_neg hpi,ContinuousMap.const_apply]

lemma realSeparated (hX : RealSeparated X) : RealSeparated (Space a) := by
  classical
  let : T2Space X := hX.t2Space
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hne : x ≠ y := fun heq => hxy (congrArg Sum.inl heq)
      obtain ⟨f,hf⟩ := hX x y hne
      obtain ⟨F,hF⟩ := exists_real_extension a f
      refine ⟨F,?_⟩
      change F (base a x) ≠ F (base a y)
      rwa [hF,hF]
    | inr p =>
      obtain ⟨F,hF1,hF0⟩ := exists_interior_separator a p.1 p.2 (Sum.inl x)
        (by exact fun h => hxy h.symm)
      refine ⟨F,?_⟩
      change F (Sum.inl x) ≠ F (openCell a p.1 p.2)
      rw [hF0,hF1]
      norm_num
  | inr p =>
    obtain ⟨F,hF1,hF0⟩ := exists_interior_separator a p.1 p.2 y hxy
    refine ⟨F,?_⟩
    change F (openCell a p.1 p.2) ≠ F y
    rw [hF1,hF0]
    norm_num

lemma t2Space (hX : RealSeparated X) : T2Space (Space a) := (realSeparated a hX).t2Space

variable [Nonempty X]

/-- The characteristic map is defined on the entire parameter space, as required
by Mathlib's classical CW definition, but only its closed-disk values matter. -/
def characteristic (i : ι) (x : Fin n → ℝ) : Space a := by
  classical
  exact if hx : x ∈ closedBall 0 1 then cell a i ⟨x,hx⟩ else base a (Classical.choice ‹Nonempty X›)

lemma characteristic_disk (i : ι) (d : Disk n) :
    characteristic a i d.1 = cell a i d := by
  simp only [characteristic,dif_pos d.2]

lemma characteristic_open (i : ι) (x : OpenDisk n) :
    characteristic a i x.1 = openCell a i x := by
  exact (characteristic_disk a i (interior n x)).trans (cell_interior a i x)

lemma characteristic_bijOn (i : ι) :
    Set.BijOn (characteristic a i) (ball 0 1) (Set.range (openCell a i)) := by
  constructor
  · intro x hx
    exact ⟨⟨x,hx⟩,(characteristic_open a i ⟨x,hx⟩).symm⟩
  constructor
  · intro x hx y hy hxy
    have hxy' : openCell a i ⟨x,hx⟩ = openCell a i ⟨y,hy⟩ := by
      rwa [characteristic_open a i ⟨x,hx⟩,characteristic_open a i ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val ((openCell_openEmbedding a i).injective hxy')
  · rintro z ⟨x,rfl⟩
    exact ⟨x.1,x.2,characteristic_open a i x⟩

def characteristicPE (i : ι) : PartialEquiv (Fin n → ℝ) (Space a) :=
  (characteristic_bijOn a i).toPartialEquiv _ _ _

lemma characteristicPE_continuousOn (i : ι) :
    ContinuousOn (characteristicPE a i) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (closedBall (0:Fin n→ℝ) 1).domRestrict (characteristicPE a i) = cell a i := by
    funext x
    exact characteristic_disk a i x
  rw [heq]
  exact (cell a i).continuous

lemma characteristicPE_continuousOn_symm (i : ι) :
    ContinuousOn (characteristicPE a i).symm (characteristicPE a i).target := by
  let e := characteristicPE a i
  have he : IsEmbedding (e.source.domRestrict e) := by
    have heq : e.source.domRestrict e = openCell a i := by
      funext x
      exact characteristic_open a i x
    rw [heq]
    exact (openCell_openEmbedding a i).isEmbedding
  let H : e.source ≃ₜ e.target := e.toEquiv.toHomeomorphOfIsInducing
    (he.isInducing.codRestrict (fun x => e.map_source x.2))
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp H.symm.continuous

lemma characteristicPE_image_ball (i : ι) :
    characteristicPE a i '' ball 0 1 = Set.range (openCell a i) :=
  (characteristic_bijOn a i).image_eq

lemma characteristicPE_image_closedBall (i : ι) :
    characteristicPE a i '' closedBall 0 1 = Set.range (cell a i) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,(characteristic_disk a i ⟨x,hx⟩).symm⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,x.2,characteristic_disk a i x⟩

abbrev CellIndex (m n : ℕ) (ι : Type v) := ULift.{u} (PLift (m = n) × ι)

def cellMap (m : ℕ) (i : CellIndex.{u,v} m n ι) :
    PartialEquiv (Fin m → ℝ) (Space a) := by
  obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
  subst m
  exact characteristicPE a i

/-- Attaching disks is a classical relative CW complex, not merely an abstract
cell-complex object in a category. -/
@[instance_reducible]
def relCWComplex : RelCWComplex (Set.univ : Set (Space a)) (Set.range (base a)) where
  cell m := CellIndex.{u,v} m n ι
  map := cellMap a
  source_eq := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    rfl
  continuousOn := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    exact characteristicPE_continuousOn a i
  continuousOn_symm := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    exact characteristicPE_continuousOn_symm a i
  pairwiseDisjoint' := by
    rintro ⟨m,⟨⟨⟨hm⟩,i⟩⟩⟩ _ ⟨k,⟨⟨⟨hk⟩,j⟩⟩⟩ _ hne
    subst m; subst k
    change Disjoint (characteristicPE a i '' ball 0 1) (characteristicPE a j '' ball 0 1)
    rw [characteristicPE_image_ball,characteristicPE_image_ball]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,rfl⟩ ⟨y,h⟩
    have hij : j = i := congrArg Sigma.fst (Sum.inr_injective h)
    subst j
    exact hne rfl
  disjointBase' := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    change Disjoint (characteristicPE a i '' ball 0 1) _
    rw [characteristicPE_image_ball]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,rfl⟩ ⟨y,h⟩
    cases h
  mapsTo := by
    rintro m ⟨⟨⟨hm⟩,i⟩⟩
    subst m
    refine ⟨fun _ => ∅,?_⟩
    intro x hx
    left
    refine ⟨a i ⟨x,hx⟩,?_⟩
    change base a (a i ⟨x,hx⟩) = characteristic a i x
    exact (cell_boundary a i ⟨x,hx⟩).symm.trans
      (characteristic_disk a i (boundary n ⟨x,hx⟩)).symm
  closed' := by
    intro A _ hA
    apply (isClosed_iff a A).mpr
    constructor
    · have h := hA.2.preimage (continuous_base a)
      convert h using 1
      ext x
      simp only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_range_self,and_true]
    · intro i
      have h := (hA.1 n ⟨⟨⟨rfl⟩,i⟩⟩).preimage (cell a i).continuous
      change IsClosed ((cell a i) ⁻¹' (A ∩ characteristicPE a i '' closedBall 0 1)) at h
      rw [characteristicPE_image_closedBall] at h
      convert h using 1
      ext x
      simp only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_range_self,and_true]
  isClosedBase := (base_closedEmbedding a).isClosed_range
  union' := by
    apply Set.eq_univ_of_forall
    intro z
    cases z with
    | inl x => exact Or.inl ⟨x,rfl⟩
    | inr p =>
      right
      refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨⟨⟨⟨rfl⟩,p.1⟩⟩,?_⟩⟩
      change Sum.inr p ∈ characteristicPE a p.1 '' closedBall 0 1
      rw [characteristicPE_image_closedBall]
      exact ⟨interior n p.2,cell_interior a p.1 p.2⟩

end GroupRingTopology.Attachment
open Set Metric Topology

end

end OAI
end


