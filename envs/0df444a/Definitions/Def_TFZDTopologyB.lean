-- Prove2me | Definitions.Def_TFZDTopologyB
-- name    : TFZDTopologyB
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T01:07:57.638563+00:00
-- url     : https://prove2.me/theorems/5c06f4ff-dcb7-4ddf-b8e7-703c948e7b3e
-- title:
--   OpenAI's torsion-free zero-divisor construction — cell attachment, Cayley complexes and sphere filling (part B)
-- statement:
--   General topology used in Section 5 of OpenAI's *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026, [github.com/openai/math](https://github.com/openai/math)) to build the finite two-dimensional classifying space. It imports part A (`Def_TFZDTopologyA`). The code is OpenAI's Lean modules `Attachment`, `Cayley`, `LoopSphere`, `CayleyFurther`, `GeneralPosition`, `CellularFurther`, `AttachmentFurther`, `CellularFurther2` and `SphereTopology` from `lean/OAI/Algebra/GroupRing` (Apache License 2.0), concatenated with identifier-level edits for this platform's Lean and Mathlib. Its names are in the namespaces `OAI.GroupRingTopology.*`.
--
--   It contains:
--   - attaching cells to a space along maps of their boundary spheres, and the resulting CW structure;
--   - the Cayley complex of a group with respect to a generating map, with its free group action and loops in it;
--   - general-position and cellular-approximation results for maps of spheres;
--   - the criterion that a simply connected complex in which every sphere can be filled is contractible (`contractible_of_two_dimensional_fills` and related lemmas).
--
--   Like part A, it holds definitions together with the lemmas proved about them, and nothing in it is specific to group rings.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, Section 5 (cell attachment, Cayley complexes, general position, sphere filling); Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), Attachment, Cayley, LoopSphere, CayleyFurther, GeneralPosition, CellularFurther, AttachmentFurther, CellularFurther2, SphereTopology

import Mathlib
import Definitions.Def_TFZDTopologyA
universe u z v w

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Cellular
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
variable {C : Set X} [CWComplex C] {f : X → Y} (hf : IsClosedEmbedding f)

def transportedMap (n : ℕ) (i : RelCWComplex.cell C n) : PartialEquiv (Fin n → ℝ) Y :=
  (RelCWComplex.map n i).trans (hf.isEmbedding.toPartialHomeomorph f).toPartialEquiv

@[simp] lemma transportedMap_apply (n : ℕ) (i : RelCWComplex.cell C n) (x : Fin n → ℝ) :
    transportedMap hf n i x = f (RelCWComplex.map n i x) := rfl

lemma transportedMap_source (n : ℕ) (i : RelCWComplex.cell C n) :
    (transportedMap hf n i).source = ball 0 1 := by
  simp only [transportedMap,PartialEquiv.trans_source,
    IsEmbedding.toPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ,
    RelCWComplex.source_eq]

lemma transportedMap_image (n : ℕ) (i : RelCWComplex.cell C n) (S : Set (Fin n → ℝ)) :
    transportedMap hf n i '' S = f '' (RelCWComplex.map n i '' S) :=
  Set.image_comp f (RelCWComplex.map n i) S

lemma transportedMap_continuousOn (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (transportedMap hf n i) (closedBall 0 1) :=
  hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n i)

lemma transportedMap_continuousOn_symm (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (transportedMap hf n i).symm (transportedMap hf n i).target := by
  let e := hf.isEmbedding.toPartialHomeomorph f
  change ContinuousOn (fun y => (RelCWComplex.map n i).symm (e.symm y))
    (e.target ∩ e.symm ⁻¹' (RelCWComplex.map n i).target)
  exact (RelCWComplex.continuousOn_symm n i).comp
    (e.continuousOn_symm.mono Set.inter_subset_left) (fun _ h => h.2)

variable [T2Space X]

/-- Closed embeddings transport classical CW structures, including their weak
 topology, with precisely the same cells. -/
@[instance_reducible]
def transportCW : CWComplex (f '' C) where
  cell := RelCWComplex.cell C
  map := transportedMap hf
  source_eq := transportedMap_source hf
  continuousOn := transportedMap_continuousOn hf
  continuousOn_symm := transportedMap_continuousOn_symm hf
  pairwiseDisjoint' := by
    intro p _ q _ hpq
    change Disjoint (transportedMap hf p.1 p.2 '' ball 0 1)
      (transportedMap hf q.1 q.2 '' ball 0 1)
    rw [transportedMap_image,transportedMap_image]
    exact (CWComplex.disjoint_openCell_of_ne hpq).image hf.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
  mapsTo' := by
    intro n i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n i
    refine ⟨I,?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map n i x ∈ CWComplex.cellFrontier n i from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨m,hm,j,hj,hx⟩ := h
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
      ⟨j,Set.mem_iUnion.mpr ⟨hj,?_⟩⟩⟩⟩
    rw [transportedMap_image]
    exact ⟨_,hx,rfl⟩
  closed' := by
    intro A hA hclosed
    have hpre : IsClosed (f ⁻¹' A) := by
      apply (CWComplex.closed C (f ⁻¹' A) ?_).mpr
      · intro n i
        have h := (hclosed n i).preimage hf.continuous
        rw [transportedMap_image,Set.preimage_inter,
          Set.preimage_image_eq _ hf.injective] at h
        exact h
      · intro x hx
        obtain ⟨y,hy,hyx⟩ := hA hx
        exact hf.injective hyx ▸ hy
    have h := hf.isClosedMap _ hpre
    rwa [Set.image_preimage_eq_of_subset (hA.trans (Set.image_subset_range f C))] at h
  union' := by
    simp only [transportedMap_image,← Set.image_iUnion]
    change f '' (⋃ n, ⋃ i, CWComplex.closedCell n i) = f '' C
    rw [CWComplex.union]

end GroupRingTopology.Cellular
open Set Metric Topology
namespace GroupRingTopology.Attachment

section
open Set Metric Topology
variable {X : Type z} [TopologicalSpace X] [T2Space X] [Nonempty X]
variable [CWComplex (Set.univ : Set X)] {ι : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,X))

abbrev OldCell (m : ℕ) := RelCWComplex.cell (Set.univ : Set X) m

omit [Nonempty X] in
lemma attaching_finite_frontier
    (hdim : ∀ m (_ : OldCell (X := X) m), m < n) (i : ι) :
    ∃ I : ∀ m, Finset (OldCell (X := X) m),
      ∀ x, a i x ∈ ⋃ m < n, ⋃ j ∈ I m, CWComplex.closedCell m j := by
  classical
  let S := {p : Σ m, OldCell (X := X) m |
    (Set.range (a i) ∩ CWComplex.openCell p.1 p.2).Nonempty}
  have hS : S.Finite := Cellular.compact_finitely_many_cells (C := (Set.univ : Set X))
    (isCompact_range (a i).continuous)
  have hSm (m : ℕ) : ((Sigma.mk m) ⁻¹' S).Finite :=
    hS.preimage (Set.injOn_of_injective (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2))
  refine ⟨fun m => (hSm m).toFinset,?_⟩
  intro x
  have hx : a i x ∈ (Set.univ : Set X) := Set.mem_univ _
  rw [← CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set X))] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨m,j,hx⟩ := hx
  exact Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hdim m j,Set.mem_iUnion.mpr
    ⟨j,Set.mem_iUnion.mpr ⟨(hSm m).mem_toFinset.mpr ⟨a i x,⟨x,rfl⟩,hx⟩,
      CWComplex.openCell_subset_closedCell m j hx⟩⟩⟩⟩

abbrev LayerCell (m : ℕ) := OldCell (X := X) m ⊕ CellIndex.{z,z} m n ι

def layerMap (m : ℕ) : LayerCell (X := X) (ι := ι) (n := n) m →
    PartialEquiv (Fin m → ℝ) (Space a)
  | Sum.inl i => Cellular.transportedMap (C := Set.univ) (base_closedEmbedding a) m i
  | Sum.inr i => cellMap a m i

omit [T2Space X] in
lemma layerMap_old_apply (m : ℕ) (i : OldCell (X := X) m) (x : Fin m → ℝ) :
    layerMap a m (Sum.inl i) x = base a (RelCWComplex.map m i x) := rfl

omit [T2Space X] in
lemma layerMap_old_image (m : ℕ) (i : OldCell (X := X) m) (S : Set (Fin m → ℝ)) :
    layerMap a m (Sum.inl i) '' S = base a '' (RelCWComplex.map m i '' S) :=
  Cellular.transportedMap_image (base_closedEmbedding a) m i S

omit [T2Space X] in
lemma layerMap_new (i : ι) :
    layerMap a n (Sum.inr ⟨⟨⟨rfl⟩,i⟩⟩) = characteristicPE a i := rfl

@[instance_reducible]
def layerCW (hdim : ∀ m (_ : OldCell (X := X) m), m < n) :
    CWComplex (Set.univ : Set (Space a)) where
  cell := LayerCell (X := X) (ι := ι) (n := n)
  map := layerMap a
  source_eq := by
    intro m i
    cases i with
    | inl i => exact Cellular.transportedMap_source (base_closedEmbedding a) m i
    | inr i => exact (relCWComplex a).source_eq m i
  continuousOn := by
    intro m i
    cases i with
    | inl i => exact Cellular.transportedMap_continuousOn (base_closedEmbedding a) m i
    | inr i => exact (relCWComplex a).continuousOn m i
  continuousOn_symm := by
    intro m i
    cases i with
    | inl i => exact Cellular.transportedMap_continuousOn_symm (base_closedEmbedding a) m i
    | inr i => exact (relCWComplex a).continuousOn_symm m i
  pairwiseDisjoint' := by
    rintro ⟨m,i⟩ _ ⟨k,j⟩ _ hne
    change Disjoint (layerMap a m i '' ball 0 1) (layerMap a k j '' ball 0 1)
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        rw [layerMap_old_image,layerMap_old_image]
        apply (CWComplex.disjoint_openCell_of_ne ?_).image (base_closedEmbedding a).injective.injOn (Set.subset_univ _) (Set.subset_univ _)
        intro h
        cases h
        exact hne rfl
      | inr j =>
        obtain ⟨⟨⟨hk⟩,j⟩⟩ := j
        subst k
        rw [layerMap_old_image,layerMap_new,characteristicPE_image_ball]
        apply Set.disjoint_left.mpr
        rintro z ⟨x,_,rfl⟩ ⟨y,h⟩
        cases h
    | inr i =>
      obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
      subst m
      cases j with
      | inl j =>
        rw [layerMap_new,characteristicPE_image_ball,layerMap_old_image]
        apply Set.disjoint_left.mpr
        rintro z ⟨x,rfl⟩ ⟨y,_,h⟩
        cases h
      | inr j =>
        obtain ⟨⟨⟨hk⟩,j⟩⟩ := j
        subst k
        rw [layerMap_new,layerMap_new,characteristicPE_image_ball,characteristicPE_image_ball]
        apply Set.disjoint_left.mpr
        rintro z ⟨x,rfl⟩ ⟨y,h⟩
        have hij : j = i := congrArg Sigma.fst (Sum.inr_injective h)
        subst j
        exact hne rfl
  mapsTo' := by
    classical
    intro m c
    cases c with
    | inl i =>
      obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell m i
      refine ⟨fun k => (I k).image Sum.inl,?_⟩
      intro x hx
      have hh := hI (show RelCWComplex.map m i x ∈ CWComplex.cellFrontier m i from ⟨x,hx,rfl⟩)
      simp only [Set.mem_iUnion] at hh
      obtain ⟨k,hkm,j,hj,hx⟩ := hh
      refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hkm,Set.mem_iUnion.mpr
        ⟨Sum.inl j,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
      rw [layerMap_old_image]
      exact ⟨_,hx,rfl⟩
    | inr i =>
      obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
      subst m
      obtain ⟨I,hI⟩ := attaching_finite_frontier a hdim i
      refine ⟨fun k => (I k).image Sum.inl,?_⟩
      intro x hx
      have hh := hI ⟨x,hx⟩
      simp only [Set.mem_iUnion] at hh
      obtain ⟨k,hkn,j,hj,hx'⟩ := hh
      refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hkn,Set.mem_iUnion.mpr
        ⟨Sum.inl j,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
      rw [layerMap_old_image]
      refine ⟨a i ⟨x,hx⟩,hx',?_⟩
      change base a (a i ⟨x,hx⟩) = characteristic a i x
      exact (cell_boundary a i ⟨x,hx⟩).symm.trans
        (characteristic_disk a i (boundary n ⟨x,hx⟩)).symm
  closed' := by
    intro A _ hA
    apply (isClosed_iff a A).mpr
    constructor
    · apply (CWComplex.closed Set.univ (base a ⁻¹' A) (Set.subset_univ _)).mpr
      intro m i
      have h := (hA m (Sum.inl i)).preimage (continuous_base a)
      rw [layerMap_old_image,Set.preimage_inter,
        Set.preimage_image_eq _ (base_closedEmbedding a).injective] at h
      exact h
    · intro i
      have h := (hA n (Sum.inr ⟨⟨⟨rfl⟩,i⟩⟩)).preimage (cell a i).continuous
      rw [layerMap_new,characteristicPE_image_closedBall,Set.preimage_inter] at h
      simpa only [Set.preimage_range,Set.inter_univ] using h
  union' := by
    apply Set.eq_univ_of_forall
    intro z
    cases z with
    | inl x =>
      have hx : x ∈ (Set.univ : Set X) := Set.mem_univ _
      rw [← CWComplex.union (C := (Set.univ : Set X))] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨m,i,hx⟩ := hx
      refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨Sum.inl i,?_⟩⟩
      rw [layerMap_old_image]
      exact ⟨x,hx,rfl⟩
    | inr p =>
      refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨Sum.inr ⟨⟨⟨rfl⟩,p.1⟩⟩,?_⟩⟩
      rw [layerMap_new,characteristicPE_image_closedBall]
      exact ⟨interior n p.2,cell_interior a p.1 p.2⟩

lemma layerCW_dimensions (hdim : ∀ m (_ : OldCell (X := X) m), m < n)
    (m : ℕ) (i : (layerCW a hdim).cell m) : m < n+1 := by
  cases i with
  | inl i => exact (hdim m i).trans (Nat.lt_succ_self n)
  | inr i =>
    obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
    subst m
    exact Nat.lt_succ_self n

lemma layerCW_finite_cells [Finite ι]
    (hfin : ∀ m, Finite (OldCell (X := X) m))
    (hdim : ∀ m (_ : OldCell (X := X) m), m < n) (m : ℕ) :
    Finite ((layerCW a hdim).cell m) := by
  let := hfin m
  change Finite (LayerCell (X := X) (ι := ι) (n := n) m)
  infer_instance

end

section
open Set Metric Topology
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,X))
variable {G : Type w} [Group G] [MulAction G X] [MulAction G ι]

instance spaceMulAction : MulAction G (Space a) where
  smul g := Sum.elim (fun x => Sum.inl (g • x)) (fun p => Sum.inr ⟨g • p.1,p.2⟩)
  one_smul := by
    intro x
    cases x with
    | inl x => change Sum.inl ((1 : G) • x) = Sum.inl x; rw [one_smul]
    | inr p => change Sum.inr ⟨(1 : G) • p.1,p.2⟩ = Sum.inr p; rw [one_smul]
  mul_smul := by
    intro g h x
    cases x with
    | inl x => change Sum.inl ((g * h) • x) = Sum.inl (g • h • x); rw [mul_smul]
    | inr p => change (Sum.inr ⟨(g * h) • p.1,p.2⟩ : Space a) = Sum.inr ⟨g • h • p.1,p.2⟩; rw [mul_smul]

@[simp] lemma smul_base (g : G) (x : X) : g • base a x = base a (g • x) := rfl
@[simp] lemma smul_openCell (g : G) (i : ι) (x : OpenDisk n) :
    g • openCell a i x = openCell a (g • i) x := rfl

variable (ha : ∀ (g : G) i x, a (g • i) x = g • a i x)
include ha
lemma smul_cell (g : G) (i : ι) (d : Disk n) :
    g • cell a i d = cell a (g • i) d := by
  classical
  by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d = interior n ⟨d.1,hd⟩ := rfl
    rw [heq,cell_interior,cell_interior]
    rfl
  · let x : Sphere n := ⟨d.1,by
      have hm := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have heq : d = boundary n x := rfl
    rw [heq,cell_boundary,cell_boundary,smul_base,ha]

lemma continuousConstSMul [ContinuousConstSMul G X] : ContinuousConstSMul G (Space a) where
  continuous_const_smul g := (continuous_iff a _).mpr ⟨
    (continuous_base a).comp (continuous_const_smul g),fun i => by
      have heq : (g • ·) ∘ cell a i = cell a (g • i) := funext (smul_cell a ha g i)
      rw [heq]
      exact (cell a (g • i)).continuous⟩

omit ha in
lemma isOpen_iff (S : Set (Space a)) :
    IsOpen S ↔ IsOpen (base a ⁻¹' S) ∧ ∀ i, IsOpen (cell a i ⁻¹' S) := by
  change @IsOpen _ (TopologicalSpace.coinduced (quotient a) inferInstance) S ↔ _
  rw [isOpen_coinduced,isOpen_sum_iff,isOpen_sigma_iff]
  rfl

end

open Set Metric Topology
abbrev Collar (n : ℕ) := {d : Disk n | (1 / 2 : ℝ) < ‖d.1‖}

def collarInclusion (n : ℕ) : Collar n → Disk n := Subtype.val

def radial (n : ℕ) : Collar n → Sphere n := fun d =>
  ⟨‖d.1.1‖⁻¹ • d.1.1,by
    have hn : ‖d.1.1‖ ≠ 0 := ne_of_gt (lt_trans (by norm_num) d.2)
    rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
      inv_mul_cancel₀ hn]⟩

lemma continuous_radial (n : ℕ) : Continuous (radial n) := by
  apply Continuous.subtype_mk
  have hn : ∀ d : Collar n, ‖d.1.1‖ ≠ 0 := fun d => ne_of_gt (lt_trans (by norm_num) d.2)
  exact ((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀ hn).smul
    (continuous_subtype_val.comp continuous_subtype_val)

lemma collar_openEmbedding (n : ℕ) : IsOpenEmbedding (collarInclusion n) :=
  (isOpen_lt continuous_const continuous_subtype_val.norm).isOpenEmbedding_subtypeVal

lemma radial_boundary (n : ℕ) (x : Sphere n) (h : (1/2:ℝ) < ‖(boundary n x).1‖) :
    radial n ⟨boundary n x,h⟩ = x := by
  apply Subtype.ext
  have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  simp only [radial,boundary,hx,inv_one,one_smul]

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,X))

/-- An open old-space neighborhood thickened by the outer half of each disk.
Membership is tested by radial retraction of the disk to its attaching sphere. -/
def thickening (U : Set X) : Set (Space a) := fun z =>
  match z with
  | Sum.inl x => x ∈ U
  | Sum.inr p => ∃ h : (1/2:ℝ) < ‖p.2.1‖,
      a p.1 (radial n ⟨interior n p.2,h⟩) ∈ U

@[simp] lemma base_mem_thickening (U : Set X) (x : X) :
    base a x ∈ thickening a U ↔ x ∈ U := Iff.rfl

lemma cell_preimage_thickening (U : Set X) (i : ι) :
    cell a i ⁻¹' thickening a U =
      collarInclusion n '' ((a i ∘ radial n) ⁻¹' U) := by
  classical
  ext d
  by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d = interior n ⟨d.1,hd⟩ := rfl
    rw [heq]
    simp only [Set.mem_preimage,cell_interior,Set.mem_image]
    constructor
    · rintro ⟨h,hh⟩
      exact ⟨⟨d,h⟩,hh,rfl⟩
    · rintro ⟨y,hy,he⟩
      have heq' : y.1 = d := he
      subst d
      exact ⟨y.2,hy⟩
  · let x : Sphere n := ⟨d.1,by
      have hm := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have heq : d = boundary n x := rfl
    have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
    have hhalf : (1/2:ℝ) < ‖(boundary n x).1‖ := by change (1/2:ℝ) < ‖x.1‖; rw [hx]; norm_num
    rw [heq]
    simp only [Set.mem_preimage,cell_boundary,base_mem_thickening,Set.mem_image]
    constructor
    · intro h
      exact ⟨⟨boundary n x,hhalf⟩,by simpa only [Function.comp_apply,radial_boundary] using h,rfl⟩
    · rintro ⟨y,hy,he⟩
      have heq' : y = ⟨boundary n x,hhalf⟩ := Subtype.ext he
      simpa only [heq',Function.comp_apply,radial_boundary] using hy

lemma thickening_isOpen {U : Set X} (hU : IsOpen U) : IsOpen (thickening a U) := by
  rw [isOpen_iff]
  refine ⟨hU,fun i => ?_⟩
  rw [cell_preimage_thickening]
  exact (collar_openEmbedding n).isOpenMap _
    (hU.preimage ((a i).continuous.comp (continuous_radial n)))

variable {G : Type w} [Group G] [MulAction G X] [MulAction G ι]
variable (ha : ∀ (g : G) i x, a (g • i) x = g • a i x)
include ha
lemma thickening_disjoint {U : Set X}
    (hU : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∀ g : G, ((g • ·) '' thickening a U ∩ thickening a U).Nonempty → g = 1 := by
  intro g h
  obtain ⟨_,⟨z,hz,rfl⟩,hgz⟩ := h
  cases z with
  | inl x => exact hU g ⟨g • x,⟨x,hz,rfl⟩,hgz⟩
  | inr p =>
    obtain ⟨hhalf,hz⟩ := hz
    obtain ⟨_,hgz⟩ := hgz
    change a (g • p.1) (radial n ⟨interior n p.2,hhalf⟩) ∈ U at hgz
    rw [ha] at hgz
    exact hU g ⟨g • a p.1 (radial n ⟨interior n p.2,hhalf⟩),⟨_,hz,rfl⟩,hgz⟩

lemma exists_disjoint_nhds [IsCancelSMul G ι]
    (hX : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∀ z : Space a, ∃ U ∈ 𝓝 z, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  intro z
  cases z with
  | inl x =>
    obtain ⟨U,hUx,hU⟩ := hX x
    obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUx
    refine ⟨thickening a V,(thickening_isOpen a hV).mem_nhds hxV,
      thickening_disjoint a ha (fun g hg => hU g ?_)⟩
    exact hg.mono (Set.inter_subset_inter (Set.image_mono hVU) hVU)
  | inr p =>
    refine ⟨Set.range (openCell a p.1),(openCell_openEmbedding a p.1).isOpen_range.mem_nhds
      (Set.mem_range_self p.2),?_⟩
    intro g hg
    obtain ⟨_,⟨_,⟨x,rfl⟩,rfl⟩,⟨y,hy⟩⟩ := hg
    have hi : p.1 = g • p.1 := congrArg Sigma.fst (Sum.inr_injective hy)
    apply IsCancelSMul.right_cancel g 1 p.1
    simpa only [one_smul] using hi.symm

end GroupRingTopology.Attachment

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Attachment

section
open Set Metric Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι : Type w} {κ : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,X)) (b : κ → C(Sphere n,Y))

def map (p : C(X,Y)) (σ : ι → κ) (h : ∀ i x, p (a i x) = b (σ i) x) :
    C(Space a,Space b) :=
  lift a ⟨base b ∘ p,(continuous_base b).comp p.continuous⟩
    (fun i => cell b (σ i)) (fun i x => by simp only [cell_boundary,ContinuousMap.coe_mk,Function.comp_apply,h])

@[simp] lemma map_base (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (x : X) :
    map a b p σ h (base a x) = base b (p x) := rfl

@[simp] lemma map_cell (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (i : ι) (d : Disk n) :
    map a b p σ h (cell a i d) = cell b (σ i) d := lift_cell a _ _ _ i d

@[simp] lemma map_openCell (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (i : ι) (d : OpenDisk n) :
    map a b p σ h (openCell a i d) = openCell b (σ i) d := by
  change map a b p σ h (Sum.inr ⟨i,d⟩) = Sum.inr ⟨σ i,d⟩
  rw [← cell_interior a i d,map_cell,cell_interior]

lemma map_surjective (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x)
    (hp : Function.Surjective p) (hσ : Function.Surjective σ) :
    Function.Surjective (map a b p σ h) := by
  intro z
  cases z with
  | inl y =>
    obtain ⟨x,rfl⟩ := hp y
    exact ⟨base a x,rfl⟩
  | inr q =>
    obtain ⟨i,hi⟩ := hσ q.1
    exact ⟨openCell a i q.2,by rw [map_openCell,hi]; rfl⟩

lemma map_isQuotientMap (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x)
    (hp : IsQuotientMap p) (hσ : Function.Surjective σ) :
    IsQuotientMap (map a b p σ h) := by
  refine ⟨?_,map_surjective a b p σ h hp.surjective hσ⟩
  rw [isCoinducing_iff]
  intro U
  constructor
  · intro hU
    rw [isOpen_iff] at hU ⊢
    constructor
    · apply hp.isOpen_preimage.mp
      exact hU.1
    · intro j
      obtain ⟨i,rfl⟩ := hσ j
      convert hU.2 i using 1
      ext d
      simp only [Set.mem_preimage,map_cell]
  · exact fun hU => hU.preimage (map a b p σ h).continuous

end

open Set Metric Topology

def FreeIndex (G : Type u) (ι : Type v) := G × ι

instance {G : Type u} [Group G] {ι : Type v} : MulAction G (FreeIndex G ι) where
  smul g p := (g * p.1,p.2)
  one_smul p := by change ((1:G)*p.1,p.2)=p; simp only [one_mul]; rfl
  mul_smul g h p := by change ((g*h)*p.1,p.2)=(g*(h*p.1),p.2); rw [mul_assoc]

instance {G : Type u} [Group G] {ι : Type v} : IsCancelSMul G (FreeIndex G ι) where
  right_cancel' _ _ _ he := mul_right_cancel (congrArg (fun p : FreeIndex G ι => p.1) he)

variable {G : Type u} [Group G]
variable {E : Type v} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]
variable {X : Type w} [TopologicalSpace X] {ι : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,E))

def equivariantFamily : FreeIndex G ι → C(Sphere n,E) :=
  fun i => ⟨fun x => i.1 • a i.2 x,(continuous_const_smul i.1).comp (a i.2).continuous⟩

lemma equivariantFamily_smul (g : G) (i : FreeIndex G ι) (x : Sphere n) :
    equivariantFamily (G := G) a (g • i) x = g • equivariantFamily a i x := mul_smul g i.1 _

instance equivariantAttachmentContinuousAction :
    ContinuousConstSMul G (Space (equivariantFamily (G := G) a)) :=
  continuousConstSMul _ (equivariantFamily_smul a)

variable (p : C(E,X)) (hp : IsQuotientCoveringMap p G)
variable (b : ι → C(Sphere n,X)) (h : ∀ i x, p (a i x) = b i x)

include hp h in
lemma equivariantFamily_over (i : FreeIndex G ι) (x : Sphere n) :
    p (equivariantFamily (G := G) a i x) = b i.2 x :=
  (hp.map_smul i.1).trans (h i.2 x)

def coverMap : C(Space (equivariantFamily (G := G) a),Space b) :=
  map _ b p Prod.snd (equivariantFamily_over a p hp b h)

lemma coverMap_isQuotient : IsQuotientMap (coverMap a p hp b h) :=
  map_isQuotientMap _ b p Prod.snd _ hp.toIsQuotientMap (fun i => ⟨(1,i),rfl⟩)

lemma coverMap_fibers {e₁ e₂ : Space (equivariantFamily (G := G) a)} :
    coverMap a p hp b h e₁ = coverMap a p hp b h e₂ ↔ e₁ ∈ MulAction.orbit G e₂ := by
  classical
  cases e₁ with
  | inl x =>
    cases e₂ with
    | inl y =>
      change Sum.inl (p x) = Sum.inl (p y) ↔ _
      rw [Sum.inl.injEq,hp.apply_eq_iff_mem_orbit]
      constructor
      · rintro ⟨g,hg⟩; exact ⟨g,congrArg Sum.inl hg⟩
      · rintro ⟨g,hg⟩; exact ⟨g,Sum.inl_injective hg⟩
    | inr q =>
      constructor
      · intro hh
        change base b (p x) = map _ b p Prod.snd _ (openCell _ q.1 q.2) at hh
        erw [map_openCell] at hh
        cases hh
      · rintro ⟨g,hg⟩; cases hg
  | inr q =>
    cases e₂ with
    | inl y =>
      constructor
      · intro hh
        change map _ b p Prod.snd _ (openCell _ q.1 q.2) = base b (p y) at hh
        erw [map_openCell] at hh
        cases hh
      · rintro ⟨g,hg⟩; cases hg
    | inr r =>
      change map _ b p Prod.snd _ (openCell _ q.1 q.2) =
        map _ b p Prod.snd _ (openCell _ r.1 r.2) ↔ _
      erw [map_openCell,map_openCell]
      constructor
      · intro hh
        have hi : q.1.2 = r.1.2 := congrArg Sigma.fst (Sum.inr_injective hh)
        have hd : q.2 = r.2 := congrArg (fun p : Σ _ : ι, OpenDisk n => p.2) (Sum.inr_injective hh)
        refine ⟨q.1.1 * r.1.1⁻¹,?_⟩
        change Sum.inr ⟨((q.1.1 * r.1.1⁻¹) * r.1.1,r.1.2),r.2⟩ = Sum.inr q
        simp only [inv_mul_cancel_right,← hi,← hd]
        rfl
      · rintro ⟨g,hg⟩
        change (Sum.inr ⟨g • r.1,r.2⟩ : Space (equivariantFamily (G := G) a)) = Sum.inr q at hg
        have hi : (g • r.1) = q.1 := congrArg Sigma.fst (Sum.inr_injective hg)
        have htuple : (⟨g • r.1,r.2⟩ : Σ _ : FreeIndex G ι, OpenDisk n) = q := Sum.inr_injective hg
        have hd' := congrArg (fun p : Σ _ : FreeIndex G ι, OpenDisk n => p.2) htuple
        have hd : r.2 = q.2 := hd' 
        have his' := congrArg (fun p : FreeIndex G ι => p.2) hi
        have his : r.1.2 = q.1.2 := his'
        change (Sum.inr ⟨q.1.2,q.2⟩ : Space b) = Sum.inr ⟨r.1.2,r.2⟩
        rw [his,hd]

/-- Free, equivariant cell attachments preserve a genuine regular covering.
The proof constructs collars of disjoint slices; no local-finiteness or
local-compactness hypothesis is imposed. -/
lemma coverMap_isQuotientCovering : IsQuotientCoveringMap (coverMap a p hp b h) G where
  __ := coverMap_isQuotient a p hp b h
  __ := equivariantAttachmentContinuousAction a
  apply_eq_iff_mem_orbit := coverMap_fibers a p hp b h
  disjoint := exists_disjoint_nhds _ (equivariantFamily_smul a) hp.disjoint

lemma coverMap_isCovering : IsCoveringMap (coverMap a p hp b h) :=
  (coverMap_isQuotientCovering a p hp b h).isCoveringMap

end GroupRingTopology.Attachment

namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment

lemma sphere_one_cases (x : Sphere 1) : x.1 0 = -1 ∨ x.1 0 = 1 := by
  have hn : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  have hc : x.1 = fun _ => x.1 0 := funext (fun i => congrArg x.1 (Subsingleton.elim i 0))
  rw [hc,pi_norm_const,Real.norm_eq_abs] at hn
  exact ((abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hn).symm

instance : Finite (Sphere 1) := by
  have he : {r : ℝ | r = -1 ∨ r = 1} = {-1,1} := by ext r; simp
  have hS : Set.Finite {r : ℝ | r = -1 ∨ r = 1} := he.symm ▸ ((Set.finite_singleton (1 : ℝ)).insert (-1))
  let : Finite {r : ℝ // r = -1 ∨ r = 1} := hS.to_subtype
  apply Finite.of_injective (fun x : Sphere 1 => (⟨x.1 0,sphere_one_cases x⟩ :
    {r : ℝ // r = -1 ∨ r = 1}))
  intro x y h
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi] using congrArg Subtype.val h

instance : DiscreteTopology (Sphere 1) := inferInstance

def minus : Sphere 1 := ⟨fun _ => -1,by norm_num [mem_sphere,dist_pi_def]⟩
def plus : Sphere 1 := ⟨fun _ => 1,by norm_num [mem_sphere,dist_pi_def]⟩

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

def attaching (i : S) : C(Sphere 1,G) :=
  ⟨fun x => if x.1 0 = -1 then 1 else s i,continuous_of_discreteTopology⟩

abbrev Graph := Space (equivariantFamily (G := G) (attaching s))

instance : Nonempty (Graph s) := ⟨base _ 1⟩

def vertex (g : G) : Graph s := base _ g

omit [Group G] in
lemma discrete_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set G) m) : m < 1 := by
  cases m with
  | zero => omega
  | succ m => exact i.elim

instance graphCW : CWComplex (Set.univ : Set (Graph s)) :=
  layerCW _ discrete_dimension

instance : T2Space (Graph s) :=
  t2Space _ ((realSeparated_of_tychonoff (Y := G)))

lemma graph_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Graph s)) m) : m < 2 :=
  layerCW_dimensions _ discrete_dimension m i

lemma vertex_injective : Function.Injective (vertex s) := Sum.inl_injective

lemma cell_minus (g : G) (i : S) :
    cell (equivariantFamily (G := G) (attaching s)) (g,i) (boundary 1 minus) = vertex s g := by
  erw [cell_boundary]
  simp only [equivariantFamily,attaching,ContinuousMap.coe_mk,minus,ite_true,smul_eq_mul,mul_one]
  rfl

lemma cell_plus (g : G) (i : S) :
    cell (equivariantFamily (G := G) (attaching s)) (g,i) (boundary 1 plus) = vertex s (g*s i) := by
  erw [cell_boundary]
  norm_num only [equivariantFamily,attaching,ContinuousMap.coe_mk,plus,ite_false,smul_eq_mul]
  rfl

instance disk_pathConnected (n : ℕ) : PathConnectedSpace (Disk n) :=
  isPathConnected_iff_pathConnectedSpace.mp ((convex_closedBall (0 : Fin n → ℝ) 1).isPathConnected ⟨0,mem_closedBall_self (by norm_num)⟩)

lemma cell_joined (g : G) (i : S) : Joined (vertex s g) (vertex s (g*s i)) := by
  have h : Joined (boundary 1 minus) (boundary 1 plus) := PathConnectedSpace.joined _ _
  have hh := h.map (cell (equivariantFamily (G := G) (attaching s)) (g,i)).continuous
  simpa only [cell_minus,cell_plus] using hh

lemma vertex_smul (g h : G) : g • vertex s h = vertex s (g*h) := rfl

lemma vertices_joined (hs : Subgroup.closure (Set.range s) = ⊤) (g : G) :
    Joined (vertex s 1) (vertex s g) := by
  let K : Subgroup G :=
    { carrier := {g | Joined (vertex s 1) (vertex s g)}
      one_mem' := Joined.refl _
      mul_mem' := by
        intro g h hg hh
        have hh' := hh.map (continuous_const_smul g : Continuous (fun x : Graph s => g • x))
        rw [vertex_smul,vertex_smul,mul_one] at hh'
        exact hg.trans hh'
      inv_mem' := by
        intro g hg
        have hh := hg.symm.map (continuous_const_smul g⁻¹ : Continuous (fun x : Graph s => g⁻¹ • x))
        change Joined (vertex s 1) (vertex s g⁻¹)
        simpa only [vertex_smul,mul_one,inv_mul_cancel] using hh }
  have hK : Subgroup.closure (Set.range s) ≤ K := (Subgroup.closure_le K).2 (by
    rintro _ ⟨i,rfl⟩
    change Joined (vertex s 1) (vertex s (s i))
    simpa only [one_mul] using cell_joined s 1 i)
  rw [hs] at hK
  exact hK (Subgroup.mem_top g)

lemma graph_pathConnected (hs : Subgroup.closure (Set.range s) = ⊤) : PathConnectedSpace (Graph s) := by
  have hj : ∀ x : Graph s, Joined (vertex s 1) x := by
    intro x
    cases x with
    | inl g => exact vertices_joined s hs g
    | inr p =>
      have h : Joined (boundary 1 minus) (interior 1 p.2) := PathConnectedSpace.joined _ _
      have hh := h.map (cell (equivariantFamily (G := G) (attaching s)) p.1).continuous
      rw [cell_interior] at hh
      have hp : cell (equivariantFamily (G := G) (attaching s)) p.1 (boundary 1 minus) = vertex s p.1.1 :=
        cell_minus s p.1.1 p.1.2
      rw [hp] at hh
      exact (vertices_joined s hs p.1.1).trans hh
  exact ⟨inferInstance,fun x y => (hj x).symm.trans (hj y)⟩

end GroupRingTopology.Cayley

namespace GroupRingTopology.PathSquares
open Set
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X] {x a b : X}

lemma turn (p : Path x a) (q : Path x b) (e : Path a b)
    (h : (p.trans e).Homotopic q) : e.Homotopic (p.symm.trans q) := by
  apply (Path.Homotopic.refl_trans e).symm.trans
  apply ((Path.Homotopic.symm_trans p).symm.hcomp (Path.Homotopic.refl e)).trans
  exact (Path.Homotopic.trans_assoc p.symm p e).trans ((Path.Homotopic.refl p.symm).hcomp h)

def spanContract (p : Path x a) (q : Path x b) :
    (p.symm.trans q).toContinuousMap.Homotopy (.const _ x) where
  toFun z := if (z.2 : ℝ) ≤ 1/2 then p.extend ((1-z.1)*(1-2*z.2))
    else q.extend ((1-z.1)*(2*z.2-1))
  continuous_toFun := continuous_if_le (by fun_prop) continuous_const
    (by fun_prop) (by fun_prop) (by intro z hz; simp [hz])
  map_zero_left z := by simp [Path.trans,Path.extend_symm_apply]
  map_one_left z := by simp

lemma spanContract_source (p : Path x a) (q : Path x b) (t : I) :
    spanContract p q (t,0) = p.symm t := by
  change (if (0 : ℝ) ≤ 1/2 then p.extend ((1-(t:ℝ))*(1-2*0)) else q.extend ((1-(t:ℝ))*(2*0-1))) = _
  norm_num only [show (0:ℝ)≤1/2 by norm_num,ite_true,mul_zero,sub_zero,mul_one]
  rw [← Path.extend_symm_apply,Path.extend_extends' ]
lemma spanContract_target (p : Path x a) (q : Path x b) (t : I) :
    spanContract p q (t,1) = q.symm t := by
  change (if (1 : ℝ) ≤ 1/2 then p.extend ((1-(t:ℝ))*(1-2*1)) else q.extend ((1-(t:ℝ))*(2*1-1))) = _
  norm_num only [mul_one,show (2:ℝ)-1=1 by norm_num,show ¬(1:ℝ)≤1/2 by norm_num,ite_false]
  rw [← Path.extend_symm_apply,Path.extend_extends' ]

def pauseReverse (p : Path x a) : C(I,X) := ((Path.refl a).trans p.symm).toContinuousMap

/-- Compatible vertex paths fill every edge square, without any path-word
approximation assertion. The pause at the vertex is the same for every edge. -/
theorem edgeSquare (p : Path x a) (q : Path x b) (e : Path a b)
    (h : (p.trans e).Homotopic q) :
    ∃ H : e.toContinuousMap.Homotopy (.const _ x),
      (∀ t, H (t,0) = pauseReverse p t) ∧ (∀ t, H (t,1) = pauseReverse q t) := by
  obtain ⟨A⟩ := turn p q e h
  refine ⟨A.toHomotopy.trans (spanContract p q),?_,?_⟩
  · intro t
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change (t:ℝ) ≤ 1/2 at ht
      change A (_,0) = ((Path.refl a).trans p.symm) t
      rw [Path.trans_apply,dif_pos ht]
      exact A.source _
    · change ¬(t:ℝ) ≤ 1/2 at ht
      change spanContract p q (_,0) = ((Path.refl a).trans p.symm) t
      rw [Path.trans_apply,dif_neg ht,spanContract_source]
  · intro t
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change (t:ℝ) ≤ 1/2 at ht
      change A (_,1) = ((Path.refl b).trans q.symm) t
      rw [Path.trans_apply,dif_pos ht]
      exact A.target _
    · change ¬(t:ℝ) ≤ 1/2 at ht
      change spanContract p q (_,1) = ((Path.refl b).trans q.symm) t
      rw [Path.trans_apply,dif_neg ht,spanContract_target]
end GroupRingTopology.PathSquares
namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment
open scoped unitInterval

def edgeParam (t : I) : Disk 1 := ⟨fun _ => 2*(t:ℝ)-1,by
  rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs,abs_le]
  constructor <;> linarith [t.2.1,t.2.2]⟩
lemma continuous_edgeParam : Continuous edgeParam := by unfold edgeParam; fun_prop

def edgeTime (d : Disk 1) : I := ⟨(d.1 0+1)/2,by
  have hh : |d.1 0| ≤ 1 := by
    have := d.2
    rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one] at this
    exact this 0
  rw [abs_le] at hh
  constructor <;> linarith⟩
lemma continuous_edgeTime : Continuous edgeTime := by
  apply Continuous.subtype_mk
  exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2
lemma edgeParam_time (d : Disk 1) : edgeParam (edgeTime d) = d := by
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  dsimp [edgeParam,edgeTime]
  ring
lemma edgeTime_param (t : I) : edgeTime (edgeParam t) = t := by
  apply Subtype.ext
  dsimp [edgeTime,edgeParam]
  ring
lemma edgeParam_zero : edgeParam 0 = boundary 1 minus := by
  apply Subtype.ext
  funext i
  norm_num [edgeParam,minus,boundary]
lemma edgeParam_one : edgeParam 1 = boundary 1 plus := by
  apply Subtype.ext
  funext i
  norm_num [edgeParam,plus,boundary]
lemma edgeTime_minus : edgeTime (boundary 1 minus) = 0 := by
  rw [←edgeParam_zero,edgeTime_param]
lemma edgeTime_plus : edgeTime (boundary 1 plus) = 1 := by
  rw [←edgeParam_one,edgeTime_param]
lemma sphere_one_eq (t : Sphere 1) : t = minus ∨ t = plus := by
  obtain h|h := sphere_one_cases t
  · left; apply Subtype.ext; funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; exact h
  · right; apply Subtype.ext; funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; exact h

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

def edge (g : G) (i : S) : Path (vertex s g) (vertex s (g*s i)) where
  toFun t := cell (equivariantFamily (G := G) (attaching s)) (g,i) (edgeParam t)
  continuous_toFun := (cell _ _).continuous.comp continuous_edgeParam
  source' := by rw [edgeParam_zero,cell_minus]
  target' := by rw [edgeParam_one,cell_plus]

variable {Y : Type v} [TopologicalSpace Y] (f : C(Graph s,Y)) (y : Y)
variable (p : ∀ g, Path y (f (vertex s g)))
variable (hp : ∀ g i, ((p g).trans ((edge s g i).map f.continuous)).Homotopic (p (g*s i)))

def edgeSquare (g : G) (i : S) : ((edge s g i).map f.continuous).toContinuousMap.Homotopy (.const _ y) :=
  (PathSquares.edgeSquare (p g) (p (g*s i)) ((edge s g i).map f.continuous) (hp g i)).choose
lemma edgeSquare_source (g : G) (i : S) (t : I) :
    edgeSquare s f y p hp g i (t,0) = PathSquares.pauseReverse (p g) t :=
  (PathSquares.edgeSquare (p g) (p (g*s i)) ((edge s g i).map f.continuous) (hp g i)).choose_spec.1 t
lemma edgeSquare_target (g : G) (i : S) (t : I) :
    edgeSquare s f y p hp g i (t,1) = PathSquares.pauseReverse (p (g*s i)) t :=
  (PathSquares.edgeSquare (p g) (p (g*s i)) ((edge s g i).map f.continuous) (hp g i)).choose_spec.2 t

def edgePaths (i : FreeIndex G S) : C(Disk 1,C(I,Y)) :=
  ContinuousMap.curry ⟨fun z => edgeSquare s f y p hp i.1 i.2 (z.2,edgeTime z.1),
    (edgeSquare s f y p hp i.1 i.2).continuous.comp
      (continuous_snd.prodMk (continuous_edgeTime.comp continuous_fst))⟩
def vertexPaths : C(G,C(I,Y)) := ⟨fun g => PathSquares.pauseReverse (p g),continuous_of_discreteTopology⟩
lemma edgePaths_boundary (i : FreeIndex G S) (t : Sphere 1) :
    edgePaths s f y p hp i (boundary 1 t) =
      vertexPaths s f y p (equivariantFamily (G := G) (attaching s) i t) := by
  obtain rfl|rfl := sphere_one_eq t
  · apply ContinuousMap.ext; intro z
    change edgeSquare s f y p hp i.1 i.2 (z,edgeTime (boundary 1 minus)) = _
    rw [edgeTime_minus,edgeSquare_source]
    simp only [vertexPaths,equivariantFamily,attaching,ContinuousMap.coe_mk,minus,ite_true,smul_eq_mul,mul_one]
  · apply ContinuousMap.ext; intro z
    change edgeSquare s f y p hp i.1 i.2 (z,edgeTime (boundary 1 plus)) = _
    rw [edgeTime_plus,edgeSquare_target]
    norm_num [vertexPaths,equivariantFamily,attaching,plus]

def graphPaths : C(Graph s,C(I,Y)) :=
  lift _ (vertexPaths s f y p) (edgePaths s f y p hp) (edgePaths_boundary s f y p hp)

lemma graphPaths_zero (z : Graph s) : graphPaths s f y p hp z 0 = f z := by
  cases z with
  | inl g =>
    change PathSquares.pauseReverse (p g) 0 = _
    exact Path.source _
  | inr z =>
    change edgeSquare s f y p hp z.1.1 z.1.2 (0,edgeTime (interior 1 z.2)) = _
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (cell _ z.1 (edgeParam (edgeTime (interior 1 z.2)))) = f _
    rw [edgeParam_time,cell_interior]
lemma graphPaths_one (z : Graph s) : graphPaths s f y p hp z 1 = y := by
  cases z with
  | inl g =>
    change PathSquares.pauseReverse (p g) 1 = y
    exact Path.target _
  | inr z =>
    change edgeSquare s f y p hp z.1.1 z.1.2 (1,edgeTime (interior 1 z.2)) = y
    exact ContinuousMap.Homotopy.apply_one _ _

/-- A coherent system of vertex paths contracts the entire graph map. -/
def graphNullhomotopy : f.Homotopy (.const _ y) where
  toFun z := graphPaths s f y p hp z.2 z.1
  continuous_toFun := (graphPaths s f y p hp).uncurry.continuous.comp continuous_swap
  map_zero_left := graphPaths_zero s f y p hp
  map_one_left := graphPaths_one s f y p hp
end GroupRingTopology.Cayley
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
open Set Metric Topology
variable {Y : Type*} [TopologicalSpace Y]

/-- One cylinder boundary filling is enough for its path-space lift. -/
theorem cylinderFill {n : ℕ} (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x, pathEndpoint (a x) = b (boundary n x))
    (F : C(Disk (n+1),Y)) (hF : ∀ x, F (boundary (n+1) x) = cylinderBoundaryMap a b h x) :
    ∃ e : C(Disk n,C(unitInterval,Y)),
      (∀ x, e (boundary n x) = a x) ∧ (∀ x, pathEndpoint (e x) = b x) := by
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

end GroupRingTopology.Cellular
namespace GroupRingTopology.LoopSphere
open Set Metric Topology Cellular
open scoped unitInterval
variable {X : Type u} [TopologicalSpace X] {x : X}

def sides : C(Sphere 1,C(I,X)) := .const _ (.const _ x)
def ends (p : Path x x) : C(Disk 1,X × X) :=
  ⟨fun d => (p (Cayley.edgeTime d),x),
    (p.continuous.comp Cayley.continuous_edgeTime).prodMk continuous_const⟩
lemma ends_sides (p : Path x x) (z : Sphere 1) :
    pathEndpoint (sides (x := x) z) = ends p (boundary 1 z) := by
  obtain rfl|rfl := Cayley.sphere_one_eq z
  · change (x,x) = (p (Cayley.edgeTime (Attachment.boundary 1 Cayley.minus)),x)
    rw [Cayley.edgeTime_minus,p.source]
  · change (x,x) = (p (Cayley.edgeTime (Attachment.boundary 1 Cayley.plus)),x)
    rw [Cayley.edgeTime_plus,p.target]

def map (p : Path x x) : C(Sphere 2,X) := cylinderBoundaryMap sides (ends p) (ends_sides p)

/-- Attaching one ordinary 2-cell along this square boundary kills its loop. -/
theorem homotopic_of_fill (p : Path x x) (F : C(Disk 2,X))
    (hF : ∀ z, F (boundary 2 z) = map p z) : p.Homotopic (Path.refl x) := by
  obtain ⟨e,he,hep⟩ := cylinderFill sides (ends p) (ends_sides p) F hF
  refine ⟨{
    toFun := fun z => e (Cayley.edgeParam z.2) z.1
    continuous_toFun := e.uncurry.continuous.comp
      ((Cayley.continuous_edgeParam.comp continuous_snd).prodMk continuous_fst)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    have h := congrArg Prod.fst (hep (Cayley.edgeParam t))
    change e (Cayley.edgeParam t) 0 = p t
    change e (Cayley.edgeParam t) 0 = p (Cayley.edgeTime (Cayley.edgeParam t)) at h
    simpa only [Cayley.edgeTime_param] using h
  · intro t
    exact congrArg Prod.snd (hep (Cayley.edgeParam t))
  · intro t q hq
    obtain rfl|hq := hq
    · change e (Cayley.edgeParam 0) t = p 0
      rw [Cayley.edgeParam_zero,p.source]
      exact ContinuousMap.congr_fun (he Cayley.minus) t
    · obtain rfl := Set.mem_singleton_iff.mp hq
      change e (Cayley.edgeParam 1) t = p 1
      rw [Cayley.edgeParam_one,p.target]
      exact ContinuousMap.congr_fun (he Cayley.plus) t

variable {Y : Type v} [TopologicalSpace Y]
lemma natural (p : Path x x) (f : C(X,Y)) : map (p.map f.continuous) = f.comp (map p) := by
  apply ContinuousMap.ext; intro z
  have hz : z ∈ ⋃ i, cylinderFace 1 i := by rw [cylinderFace_cover]; trivial
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  change cylinderBoundaryMap sides (ends (p.map f.continuous)) (ends_sides _) z =
    f (cylinderBoundaryMap sides (ends p) (ends_sides p) z)
  rw [cylinderBoundaryMap_face _ _ _ i ⟨z,hi⟩,cylinderBoundaryMap_face _ _ _ i ⟨z,hi⟩]
  cases i with
  | none => rfl
  | some b => cases b <;> rfl

lemma homotopic_map_of_fill (p : Path x x) (f : C(X,Y)) (F : C(Disk 2,Y))
    (hF : ∀ z, F (boundary 2 z) = f (map p z)) :
    (p.map f.continuous).Homotopic (Path.refl (f x)) := by
  apply homotopic_of_fill _ F
  intro z
  rw [natural]
  exact hF z
end GroupRingTopology.LoopSphere

/-! The path-class extension of an acting group. This is geometric support for
the finite presentation Cayley cover, not an assumption of simple connectivity. -/

namespace GroupRingTopology.PathExtension

section
open Path.Homotopic
variable {X : Type u} [TopologicalSpace X]

namespace Q
variable {x y z : X}
lemma trans_cast {x' y' z' : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) (hx : x' = x) (hy : y' = y) (hz : z' = z) :
    (p.cast hx hy).trans (q.cast hy hz) = (p.trans q).cast hx hz := by
  subst x'; subst y'; subst z'; simp
lemma map_trans {Y : Type*} [TopologicalSpace Y]
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) (f : C(X,Y)) :
    (p.trans q).map f = (p.map f).trans (q.map f) := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  induction q using Path.Homotopic.Quotient.ind with | mk q =>
  exact congrArg Path.Homotopic.Quotient.mk (p.map_trans q f.continuous)
lemma map_refl {Y : Type*} [TopologicalSpace Y] (x : X) (f : C(X,Y)) :
    (Path.Homotopic.Quotient.refl x).map f = Path.Homotopic.Quotient.refl (f x) := rfl
lemma map_symm {Y : Type*} [TopologicalSpace Y] (p : Path.Homotopic.Quotient x y) (f : C(X,Y)) :
    p.symm.map f = (p.map f).symm := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact congrArg Path.Homotopic.Quotient.mk (p.map_symm f.continuous)
/-- Equality of path classes together with equality of both endpoint labels. -/
structure Equal {x' y' : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient x' y') : Prop where
  source : x = x'
  target : y = y'
  path : HEq p q

namespace Equal
lemma refl (p : Path.Homotopic.Quotient x y) : Equal p p := ⟨rfl,rfl,HEq.rfl⟩
lemma ofEq {p q : Path.Homotopic.Quotient x y} (h : p = q) : Equal p q := ⟨rfl,rfl,heq_of_eq h⟩
lemma symm {x' y' : X} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient x' y'} (h : Equal p q) : Equal q p :=
  ⟨h.source.symm,h.target.symm,h.path.symm⟩
lemma trans {x' y' x'' y'' : X} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient x' y'} {r : Path.Homotopic.Quotient x'' y''}
    (h : Equal p q) (k : Equal q r) : Equal p r :=
  ⟨h.source.trans k.source,h.target.trans k.target,h.path.trans k.path⟩
lemma map {Y : Type*} [TopologicalSpace Y] {x' y' : X}
    {p : Path.Homotopic.Quotient x y} {q : Path.Homotopic.Quotient x' y'}
    (h : Equal p q) (f : C(X,Y)) : Equal (p.map f) (q.map f) := by
  rcases h with ⟨hx,hy,hp⟩
  subst x'; subst y'
  cases eq_of_heq hp
  exact .refl _
lemma comp {x' y' z' : X} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient y z} {p' : Path.Homotopic.Quotient x' y'}
    {q' : Path.Homotopic.Quotient y' z'} (hp : Equal p p') (hq : Equal q q') :
    Equal (p.trans q) (p'.trans q') := by
  rcases hp with ⟨hx,hy,hp⟩
  rcases hq with ⟨_,hz,hq⟩
  subst x'; subst y'; subst z'
  cases eq_of_heq hp; cases eq_of_heq hq
  exact .refl _
end Equal
lemma cast_equal {x' y' : X} (p : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) :
    Equal (p.cast hx hy) p := ⟨hx,hy,Path.Homotopic.Quotient.cast_heq hx hy⟩
lemma refl_equal {x y : X} (h : x = y) :
    Equal (Path.Homotopic.Quotient.refl x) (Path.Homotopic.Quotient.refl y) := by
  subst y
  exact .refl _

end Q

variable {G : Type v} [Group G] [MulAction G X] [ContinuousConstSMul G X]

def smulMap (g : G) : C(X,X) := ⟨fun x => g • x,continuous_const_smul g⟩

lemma map_one_equal {x y : X} (p : Path.Homotopic.Quotient x y) :
    Q.Equal (p.map (smulMap (1 : G))) p := by
  refine ⟨one_smul G x,one_smul G y,?_⟩
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.hpath_hext (fun t => one_smul G (p t))

lemma map_mul_equal {x y : X} (p : Path.Homotopic.Quotient x y) (g h : G) :
    Q.Equal ((p.map (smulMap h)).map (smulMap g)) (p.map (smulMap (g*h))) := by
  refine ⟨(mul_smul g h x).symm,(mul_smul g h y).symm,?_⟩
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.hpath_hext (fun t => (mul_smul g h (p t)).symm)

variable (G) (x₀ : X)
abbrev Extension := Σ g : G, Path.Homotopic.Quotient x₀ (g • x₀)
variable {G x₀}

omit [ContinuousConstSMul G X] in
@[ext] lemma ext {a b : Extension G x₀} (hg : a.1 = b.1) (hp : HEq a.2 b.2) : a = b :=
  Sigma.ext hg hp

instance : One (Extension G x₀) :=
  ⟨⟨1,(Path.Homotopic.Quotient.refl x₀).cast rfl (one_smul G x₀)⟩⟩
instance : Mul (Extension G x₀) :=
  ⟨fun a b => ⟨a.1*b.1,(a.2.trans (b.2.map (smulMap a.1))).cast rfl (mul_smul ..)⟩⟩
instance : Inv (Extension G x₀) :=
  ⟨fun a => ⟨a.1⁻¹,((a.2.map (smulMap a.1⁻¹)).symm).cast (inv_smul_smul a.1 x₀).symm rfl⟩⟩

lemma mul_path_equal (a b : Extension G x₀) :
    Q.Equal (a*b).2 (a.2.trans (b.2.map (smulMap a.1))) :=
  Q.cast_equal _ _ _

omit [ContinuousConstSMul G X] in
lemma one_path_equal : Q.Equal (1 : Extension G x₀).2 (Path.Homotopic.Quotient.refl x₀) := by
  change Q.Equal ((Path.Homotopic.Quotient.refl x₀).cast rfl (one_smul G x₀)) _
  exact Q.cast_equal _ _ _

lemma mul_assoc (a b c : Extension G x₀) : a*b*c = a*(b*c) := by
  apply ext (_root_.mul_assoc _ _ _)
  apply Q.Equal.path
  apply Q.Equal.trans (mul_path_equal (a*b) c)
  apply Q.Equal.trans (Q.Equal.comp (mul_path_equal a b) (map_mul_equal c.2 a.1 b.1).symm)
  apply Q.Equal.trans (Q.Equal.ofEq (Path.Homotopic.Quotient.trans_assoc _ _ _))
  apply Q.Equal.trans ?_ (mul_path_equal a (b*c)).symm
  apply Q.Equal.comp (Q.Equal.refl _)
  apply Q.Equal.trans ?_ ((mul_path_equal b c).map (smulMap a.1)).symm
  exact Q.Equal.ofEq (Q.map_trans _ _ _).symm

lemma one_mul (a : Extension G x₀) : 1*a = a := by
  apply ext (_root_.one_mul _)
  apply Q.Equal.path
  exact (mul_path_equal 1 a).trans
    ((Q.Equal.comp one_path_equal (map_one_equal a.2)).trans
      (Q.Equal.ofEq (Path.Homotopic.Quotient.refl_trans a.2)))

lemma mul_one (a : Extension G x₀) : a*1 = a := by
  apply ext (_root_.mul_one _)
  apply Q.Equal.path
  apply Q.Equal.trans (mul_path_equal a 1)
  apply Q.Equal.trans (Q.Equal.comp (Q.Equal.refl _) (one_path_equal.map (smulMap a.1)))
  rw [Q.map_refl]
  exact Q.Equal.ofEq (Path.Homotopic.Quotient.trans_refl a.2)

lemma inv_mul_cancel (a : Extension G x₀) : a⁻¹*a = 1 := by
  apply ext (_root_.inv_mul_cancel _)
  apply Q.Equal.path
  apply Q.Equal.trans (mul_path_equal a⁻¹ a)
  have hi : Q.Equal (a⁻¹).2 (a.2.map (smulMap a.1⁻¹)).symm := Q.cast_equal _ _ _
  exact (Q.Equal.comp hi (Q.Equal.refl _)).trans
    ((Q.Equal.ofEq (Path.Homotopic.Quotient.symm_trans _)).trans
      ((Q.refl_equal (inv_smul_smul a.1 x₀)).trans one_path_equal.symm))

instance : Group (Extension G x₀) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := inv_mul_cancel

/-- Endpoint projection of the genuine path-class extension. -/
def projection : Extension G x₀ →* G where
  toFun := Sigma.fst
  map_one' := rfl
  map_mul' _ _ := rfl

end
open Path.Homotopic
variable {G : Type u} [Group G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable {Y : Type w} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable (f : C(X,Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

include hf in
lemma natural_smul_equal {x y : X} (p : Path.Homotopic.Quotient x y) (g : G) :
    Q.Equal ((p.map (smulMap g)).map f) ((p.map f).map (smulMap g)) := by
  refine ⟨hf g x,hf g y,?_⟩
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.hpath_hext (fun t => hf g (p t))

variable (x₀ : X)
def mapFun (a : Extension G x₀) : Extension G (f x₀) :=
  ⟨a.1,(a.2.map f).cast rfl (hf a.1 x₀).symm⟩
omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
lemma mapFun_equal (a : Extension G x₀) :
    Q.Equal (mapFun f hf x₀ a).2 (a.2.map f) := Q.cast_equal _ _ _
omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
lemma mapFun_one : mapFun f hf x₀ 1 = 1 := by
  apply ext rfl
  apply Q.Equal.path
  apply (mapFun_equal f hf x₀ 1).trans
  apply (one_path_equal.map f).trans
  rw [Q.map_refl]
  exact one_path_equal.symm
lemma mapFun_mul (a b : Extension G x₀) : mapFun f hf x₀ (a*b) = mapFun f hf x₀ a * mapFun f hf x₀ b := by
  apply ext (a := mapFun f hf x₀ (a*b)) (b := mapFun f hf x₀ a * mapFun f hf x₀ b) (by rfl)
  apply Q.Equal.path
  apply (mapFun_equal f hf x₀ (a*b)).trans
  apply ((mul_path_equal a b).map f).trans
  apply (Q.Equal.ofEq (Q.map_trans _ _ _)).trans
  apply Q.Equal.trans ?_ (mul_path_equal (mapFun f hf x₀ a) (mapFun f hf x₀ b)).symm
  exact Q.Equal.comp (mapFun_equal f hf x₀ a).symm
    ((natural_smul_equal f hf b.2 a.1).trans
      ((mapFun_equal f hf x₀ b).map (smulMap a.1)).symm)

def map : Extension G x₀ →* Extension G (f x₀) where
  toFun := mapFun f hf x₀
  map_one' := mapFun_one f hf x₀
  map_mul' := mapFun_mul f hf x₀

lemma projection_map : projection.comp (map f hf x₀) = projection := rfl
end GroupRingTopology.PathExtension
namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment PathExtension
open scoped unitInterval
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

lemma smul_vertex (g h : G) : g • vertex s h = vertex s (g*h) := rfl

def pathGenerator (i : S) : PathExtension.Extension G (vertex s 1) :=
  ⟨s i,Path.Homotopic.Quotient.mk ((edge s 1 i).cast rfl (by
    rw [smul_vertex]; simp only [_root_.mul_one,_root_.one_mul]))⟩
def wordLift : FreeGroup S →* PathExtension.Extension G (vertex s 1) :=
  FreeGroup.lift (pathGenerator s)
lemma projection_wordLift : PathExtension.projection.comp (wordLift s) = FreeGroup.lift s := by
  ext i
  simp only [MonoidHom.comp_apply,wordLift,FreeGroup.lift_apply_of]
  rfl
lemma wordLift_fst (w : FreeGroup S) : (wordLift s w).1 = FreeGroup.lift s w :=
  DFunLike.congr_fun (projection_wordLift s) w

variable (rels : Set (FreeGroup S)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
def relatorClass (r : rels) : Path.Homotopic.Quotient (vertex s 1) (vertex s 1) :=
  (wordLift s r.1).2.cast rfl (by rw [wordLift_fst,hrel r.1 r.2,one_smul])
def relatorLoop (r : rels) : Path (vertex s 1) (vertex s 1) :=
  (Path.Homotopic.Quotient.mk_surjective (relatorClass s rels hrel r)).choose
lemma relatorLoop_eq (r : rels) : Path.Homotopic.Quotient.mk (relatorLoop s rels hrel r) =
    relatorClass s rels hrel r :=
  (Path.Homotopic.Quotient.mk_surjective (relatorClass s rels hrel r)).choose_spec
lemma relatorLoop_equal (r : rels) :
    PathExtension.Q.Equal (Path.Homotopic.Quotient.mk (relatorLoop s rels hrel r))
      (wordLift s r.1).2 :=
  (PathExtension.Q.Equal.ofEq (relatorLoop_eq s rels hrel r)).trans (PathExtension.Q.cast_equal _ _ _)

def relatorAttaching (r : rels) : C(Sphere 2,Graph s) := LoopSphere.map (relatorLoop s rels hrel r)
abbrev PresentationCover := Space (equivariantFamily (G := G) (relatorAttaching s rels hrel))
def presentationBase : C(Graph s,PresentationCover s rels hrel) := ⟨base _,continuous_base _⟩
lemma presentationBase_smul (g : G) (x : Graph s) :
    presentationBase s rels hrel (g • x) = g • presentationBase s rels hrel x := rfl

def coverWordLift : FreeGroup S →* PathExtension.Extension G (presentationBase s rels hrel (vertex s 1)) :=
  (PathExtension.map (presentationBase s rels hrel) (presentationBase_smul s rels hrel) (vertex s 1)).comp
    (wordLift s)

lemma mapped_relator_homotopic (r : rels) :
    ((relatorLoop s rels hrel r).map (presentationBase s rels hrel).continuous).Homotopic
      (Path.refl (presentationBase s rels hrel (vertex s 1))) := by
  apply LoopSphere.homotopic_map_of_fill _ _ (cell _ ((1:G),r))
  intro z
  change cell (equivariantFamily (G := G) (relatorAttaching s rels hrel)) ((1:G),r)
    (Attachment.boundary 2 z) = _
  erw [cell_boundary]
  simp only [equivariantFamily,ContinuousMap.coe_mk,one_smul]
  rfl

lemma coverWordLift_relator (r : rels) : coverWordLift s rels hrel r.1 = 1 := by
  apply PathExtension.ext (a := coverWordLift s rels hrel r.1) (b := 1)
    ((wordLift_fst s r.1).trans (hrel r.1 r.2))
  apply PathExtension.Q.Equal.path
  apply (PathExtension.mapFun_equal (presentationBase s rels hrel)
    (presentationBase_smul s rels hrel) (vertex s 1) (wordLift s r.1)).trans
  apply ((relatorLoop_equal s rels hrel r).map (presentationBase s rels hrel)).symm.trans
  apply (PathExtension.Q.Equal.ofEq (Quotient.sound (mapped_relator_homotopic s rels hrel r))).trans
  exact PathExtension.one_path_equal.symm

lemma coverWordLift_ker (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) :
    (FreeGroup.lift s).ker ≤ (coverWordLift s rels hrel).ker := by
  rw [hker]
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact coverWordLift_relator s rels hrel ⟨r,hr⟩

def presentationSection (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) :
    G →* PathExtension.Extension G (presentationBase s rels hrel (vertex s 1)) :=
  (FreeGroup.lift s).liftOfSurjective hs ⟨coverWordLift s rels hrel,coverWordLift_ker s rels hrel hker⟩
lemma presentationSection_lift (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) (w : FreeGroup S) :
    presentationSection s rels hrel hs hker (FreeGroup.lift s w) = coverWordLift s rels hrel w :=
  MonoidHom.liftOfRightInverse_comp_apply ..
lemma presentationSection_fst (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) (g : G) :
    (presentationSection s rels hrel hs hker g).1 = g := by
  obtain ⟨w,rfl⟩ := hs g
  rw [presentationSection_lift]
  exact wordLift_fst s w
end GroupRingTopology.Cayley

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Cayley

section
open Set Metric Topology Attachment PathExtension
open scoped unitInterval
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)
variable {Y : Type v} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable (f : C(Graph s,Y)) (hf : ∀ (g : G) x, f (g • x) = g • f x)
include hf in
omit [ContinuousConstSMul G Y] in
lemma vertex_action (g : G) : f (vertex s g) = g • f (vertex s 1) := by
  rw [← hf,smul_vertex,_root_.mul_one]

lemma pathGenerator_equal (i : S) : Q.Equal (pathGenerator s i).2 (Path.Homotopic.Quotient.mk (edge s 1 i)) := by
  refine ⟨rfl,?_,?_⟩
  · rw [smul_vertex]; simp only [_root_.one_mul,_root_.mul_one]; rfl
  · exact Path.Homotopic.hpath_hext (fun _ => rfl)

include hf in
lemma edge_smul_equal (g : G) (i : S) :
    Q.Equal (((Path.Homotopic.Quotient.mk (edge s 1 i)).map f).map (smulMap g))
      (Path.Homotopic.Quotient.mk ((edge s g i).map f.continuous)) := by
  refine ⟨(vertex_action s f hf g).symm,?_,?_⟩
  · change g • f (vertex s (1*s i)) = f (vertex s (g*s i))
    rw [←hf,smul_vertex,_root_.one_mul]
  · apply Path.Homotopic.hpath_hext
    intro t
    change g • f (cell _ ((1:G),i) (edgeParam t)) = f (cell _ (g,i) (edgeParam t))
    erw [←hf,smul_cell _ (equivariantFamily_smul (attaching s))]
    change f (cell _ (g*1,i) (edgeParam t)) = _
    rw [_root_.mul_one]

variable (τ : G →* PathExtension.Extension G (f (vertex s 1)))
variable (hτ : ∀ g, (τ g).1 = g)
def coherentClass (g : G) : Path.Homotopic.Quotient (f (vertex s 1)) (f (vertex s g)) :=
  (τ g).2.cast rfl (by rw [hτ]; exact vertex_action s f hf g)
def coherentPath (g : G) : Path (f (vertex s 1)) (f (vertex s g)) :=
  (Path.Homotopic.Quotient.mk_surjective (coherentClass s f hf τ hτ g)).choose
lemma coherentPath_equal (g : G) : Q.Equal (Path.Homotopic.Quotient.mk (coherentPath s f hf τ hτ g)) (τ g).2 :=
  (Q.Equal.ofEq (Path.Homotopic.Quotient.mk_surjective (coherentClass s f hf τ hτ g)).choose_spec).trans
    (Q.cast_equal _ _ _)

variable (hgen : ∀ i, Q.Equal (τ (s i)).2 (Path.Homotopic.Quotient.mk ((edge s 1 i).map f.continuous)))
include hgen in
lemma coherentPath_edge (g : G) (i : S) :
    ((coherentPath s f hf τ hτ g).trans ((edge s g i).map f.continuous)).Homotopic
      (coherentPath s f hf τ hτ (g*s i)) := by
  apply Path.Homotopic.Quotient.exact
  change (Path.Homotopic.Quotient.mk (coherentPath s f hf τ hτ g)).trans
    (Path.Homotopic.Quotient.mk ((edge s g i).map f.continuous)) = _
  apply eq_of_heq
  apply Q.Equal.path
  have he : Q.Equal ((τ (s i)).2.map (smulMap (τ g).1))
      (Path.Homotopic.Quotient.mk ((edge s g i).map f.continuous)) := by
    apply ((hgen i).map (smulMap (τ g).1)).trans
    rw [hτ]
    exact edge_smul_equal s f hf g i
  apply (Q.Equal.comp (coherentPath_equal s f hf τ hτ g) he.symm).trans
  apply (mul_path_equal (τ g) (τ (s i))).symm.trans
  have hm : Q.Equal (τ g * τ (s i)).2 (τ (g*s i)).2 := by
    rw [←τ.map_mul]
    exact .refl _
  exact hm.trans (coherentPath_equal s f hf τ hτ (g*s i)).symm

def nullhomotopyOfSection : f.Homotopy (.const _ (f (vertex s 1))) :=
  graphNullhomotopy s f (f (vertex s 1)) (coherentPath s f hf τ hτ)
    (coherentPath_edge s f hf τ hτ hgen)
end
open PathExtension Attachment
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G) (rels : Set (FreeGroup S))
variable (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
variable (hs : Function.Surjective (FreeGroup.lift s))
variable (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels)
lemma presentationSection_generator (i : S) :
    Q.Equal (presentationSection s rels hrel hs hker (s i)).2
      (Path.Homotopic.Quotient.mk ((edge s 1 i).map (presentationBase s rels hrel).continuous)) := by
  have hh : presentationSection s rels hrel hs hker (s i) =
      PathExtension.map (presentationBase s rels hrel) (presentationBase_smul s rels hrel) (vertex s 1)
        (pathGenerator s i) := by
    simpa only [FreeGroup.lift_apply_of,coverWordLift,MonoidHom.comp_apply,wordLift]
      using presentationSection_lift s rels hrel hs hker (FreeGroup.of i)
  rw [hh]
  exact (PathExtension.mapFun_equal (presentationBase s rels hrel) (presentationBase_smul s rels hrel) (vertex s 1) (pathGenerator s i)).trans
    ((pathGenerator_equal s i).map (presentationBase s rels hrel))

def presentationGraphNullhomotopy :
    (presentationBase s rels hrel).Homotopy
      (.const _ (presentationBase s rels hrel (vertex s 1))) :=
  nullhomotopyOfSection s (presentationBase s rels hrel) (presentationBase_smul s rels hrel)
    (presentationSection s rels hrel hs hker) (presentationSection_fst s rels hrel hs hker)
    (presentationSection_generator s rels hrel hs hker)
end GroupRingTopology.Cayley
namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {G : Type u} [Group G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable {Y : Type w} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι : Type z} {n : ℕ} (a : ι → C(Sphere n,X))

/-- Fill one disk per orbit and translate the fillings, preserving the action. -/
lemma exists_equivariant_extension (f : C(X,Y))
    (hf : ∀ (g : G) x, f (g • x) = g • f x) (hY : Cellular.SphereFillable Y) :
    ∃ F : C(Space (equivariantFamily (G := G) a),Y),
      (∀ x, F (base _ x) = f x) ∧ (∀ (g : G) x, F (g • x) = g • F x) := by
  choose e he using fun i => hY n (f.comp (a i))
  let b : FreeIndex G ι → C(Disk n,Y) := fun i =>
    ⟨fun d => i.1 • e i.2 d,(continuous_const_smul i.1).comp (e i.2).continuous⟩
  have hb (i : FreeIndex G ι) (x : Sphere n) :
      b i (boundary n x) = f (equivariantFamily a i x) := by
    change i.1 • e i.2 (Cellular.boundary n x) = f (i.1 • a i.2 x)
    rw [he,hf]
    rfl
  refine ⟨lift _ f b hb,fun _ => rfl,?_⟩
  intro g x
  cases x with
  | inl x => exact hf g x
  | inr p => exact (mul_smul g p.1.1 (e p.1.2 (interior n p.2)))

/-- Finitely many free cell orbits preserve existence of a compact fundamental set. -/
lemma compactFundamentalSet [Finite ι] (hX : Milnor.CompactFundamentalSet G (X := X)) :
    Milnor.CompactFundamentalSet G (X := Space (equivariantFamily (G := G) a)) := by
  let b := equivariantFamily (G := G) a
  obtain ⟨K,hK,hcov⟩ := hX
  let L : Set (Space b) := (base b '' K) ∪ ⋃ i : ι, Set.range (cell b ((1:G),i))
  refine ⟨L,(hK.image (continuous_base b)).union (isCompact_iUnion (fun i =>
    isCompact_range (cell b ((1:G),i)).continuous)),?_⟩
  intro x
  cases x with
  | inl x =>
    obtain ⟨g,y,hy,rfl⟩ := hcov x
    exact ⟨g,base b y,Or.inl ⟨y,hy,rfl⟩,rfl⟩
  | inr p =>
    refine ⟨p.1.1,cell b ((1:G),p.1.2) (interior n p.2),?_,?_⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨p.1.2,Set.mem_range_self _⟩)
    · erw [smul_cell _ (equivariantFamily_smul a)]
      change Sum.inr p = cell b (p.1.1*1,p.1.2) (interior n p.2)
      erw [mul_one,cell_interior]
      rfl
end GroupRingTopology.Attachment

namespace GroupRingTopology.Milnor
open Set Metric Topology Attachment
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {A : Type u} (s : A → G)

omit [DiscreteTopology G] in
lemma group_compactFundamentalSet : CompactFundamentalSet G (X := G) := by
  refine ⟨{1},isCompact_singleton,?_⟩
  intro g
  exact ⟨g,1,Set.mem_singleton _,by simp only [smul_eq_mul,mul_one]⟩

lemma graph_compactFundamentalSet [Finite A] : CompactFundamentalSet G (X := Cayley.Graph s) :=
  Attachment.compactFundamentalSet (Cayley.attaching s) group_compactFundamentalSet

variable (rels : Set (FreeGroup A)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
lemma presentation_compactFundamentalSet [Finite A] (hrels : rels.Finite) :
    CompactFundamentalSet G (X := Cayley.PresentationCover s rels hrel) := by
  let := hrels.to_subtype
  exact Attachment.compactFundamentalSet (Cayley.relatorAttaching s rels hrel)
    (graph_compactFundamentalSet s)

lemma presentation_equivariant_map :
    ∃ f : C(Cayley.PresentationCover s rels hrel,Space G),
      ∀ (g : G) x, f (g • x) = g • f x := by
  let f₀ : C(G,Space G) := ⟨fun g => g • vertex (0,1),continuous_of_discreteTopology⟩
  have hf₀ (g h : G) : f₀ (g • h) = g • f₀ h := mul_smul g h _
  obtain ⟨f₁,_,hf₁⟩ := Attachment.exists_equivariant_extension (Cayley.attaching s) f₀ hf₀
    (sphereFillable (1:G))
  obtain ⟨f₂,_,hf₂⟩ := Attachment.exists_equivariant_extension (Cayley.relatorAttaching s rels hrel)
    f₁ hf₁ (sphereFillable (1:G))
  exact ⟨f₂,hf₂⟩

include hrel in
/-- Finite presentability supplies a coherent group section in ONE Milnor stage.
This is genuine low-dimensional control, not a simply-connected-stage assumption. -/
lemma exists_stage_section [Finite A] (hrels : rels.Finite)
    (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) :
    ∃ (S : Shapes G) (x : Stage G S) (τ : G →* PathExtension.Extension G x), ∀ g, (τ g).1 = g := by
  obtain ⟨f,hf⟩ := presentation_equivariant_map s rels hrel
  obtain ⟨S,hS⟩ := equivariant_controlled G (presentation_compactFundamentalSet s rels hrel hrels) f hf
  let F := factorStage G f S hS
  have hF : ∀ (g : G) x, F (g • x) = g • F x := factorStage_smul G f S hS hf
  let x := Cayley.presentationBase s rels hrel (Cayley.vertex s 1)
  let τ := (PathExtension.map F hF x).comp (Cayley.presentationSection s rels hrel hs hker)
  refine ⟨S,F x,τ,?_⟩
  intro g
  exact Cayley.presentationSection_fst s rels hrel hs hker g
end GroupRingTopology.Milnor

namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X))

def cellCenter (i : ι) : Space a := openCell a i ⟨0,by simp⟩
def punctured : Set (Space a) := (Set.range (cellCenter a))ᶜ

def rawCoordinate : Space a → (Fin n → ℝ)
  | Sum.inl _ => 0 | Sum.inr p => p.2.1

lemma base_mem_punctured (x : X) : base a x ∈ punctured a := by
  rintro ⟨i,h⟩
  cases h

lemma cell_mem_punctured (i : ι) (d : Disk n) : cell a i d ∈ punctured a ↔ d.1 ≠ 0 := by
  classical
  constructor
  · intro hd hzero
    apply hd
    refine ⟨i,?_⟩
    have heq : d = interior n ⟨0,by simp⟩ := Subtype.ext hzero
    rw [heq,cell_interior]
    rfl
  · intro hzero
    rintro ⟨j,hj⟩
    by_cases h : d.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : d = interior n ⟨d.1,h⟩ := rfl
      rw [heq,cell_interior] at hj
      exact hzero (congrArg (rawCoordinate a) hj).symm
    · let s : Sphere n := ⟨d.1,by
        have hd := d.2
        simp only [mem_sphere,mem_ball,mem_closedBall] at *
        exact le_antisymm hd (le_of_not_gt h)⟩
      have heq : d = boundary n s := rfl
      rw [heq,cell_boundary] at hj
      cases hj

lemma punctured_open : IsOpen (punctured a) := by
  change IsOpen (Set.range (cellCenter a))ᶜ
  rw [isOpen_compl_iff]
  rw [isClosed_iff]
  constructor
  · have h : base a ⁻¹' Set.range (cellCenter a) = ∅ := by
      ext x
      simp only [mem_preimage,mem_empty_iff_false,iff_false]
      exact base_mem_punctured a x
    rw [h]
    exact isClosed_empty
  · intro i
    have h : cell a i ⁻¹' Set.range (cellCenter a) = {d : Disk n | d.1 = 0} := by
      ext d
      exact not_iff_not.mp (cell_mem_punctured a i d)
    rw [h]
    exact isClosed_eq continuous_subtype_val continuous_const

lemma continuous_punctured {Y : Type*} [TopologicalSpace Y] (F : punctured a → Y)
    (hb : Continuous (fun x : X => F ⟨base a x,base_mem_punctured a x⟩))
    (hc : ∀ i, Continuous (fun d : {d : Disk n // d.1 ≠ 0} =>
      F ⟨cell a i d.1,(cell_mem_punctured a i d.1).mpr d.2⟩)) : Continuous F := by
  let q := quotient a
  have hq : IsQuotientMap q := ⟨⟨rfl⟩,quotient_surjective a⟩
  have hp := hq.restrictPreimage_isOpen (punctured_open a)
  apply hp.continuous_iff.mpr
  apply continuous_iff_continuousAt.mpr
  rintro ⟨z,hz⟩
  cases z with
  | inl x =>
    let e : X → q ⁻¹' punctured a := fun x => ⟨Sum.inl x,base_mem_punctured a x⟩
    have he : IsOpenEmbedding e := by
      have hi : IsOpenEmbedding (Sum.inl : X → X ⊕ (Σ _ : ι, Disk n)) := .inl
      exact ⟨hi.isEmbedding.codRestrict (q ⁻¹' punctured a) (fun x => base_mem_punctured a x),by
        have hr : Set.range e = Subtype.val ⁻¹' Set.range Sum.inl := by
          ext z
          simp only [mem_range,mem_preimage,e]
          constructor
          · rintro ⟨x,rfl⟩; exact ⟨x,rfl⟩
          · rintro ⟨x,hx⟩; exact ⟨x,Subtype.ext hx⟩
        rw [hr]
        exact hi.isOpen_range.preimage continuous_subtype_val⟩
    exact (he.continuousAt_iff (g := F ∘ (punctured a).restrictPreimage q)).mp (hb.continuousAt (x := x))
  | inr p =>
    rcases p with ⟨i,d⟩
    have hd : d.1 ≠ 0 := (cell_mem_punctured a i d).mp hz
    let e : {d : Disk n // d.1 ≠ 0} → q ⁻¹' punctured a :=
      fun d => ⟨Sum.inr ⟨i,d.1⟩,(cell_mem_punctured a i d.1).mpr d.2⟩
    have he : IsOpenEmbedding e := by
      have hi : IsOpenEmbedding (fun d : Disk n => (Sum.inr ⟨i,d⟩ : X ⊕ (Σ _ : ι, Disk n))) :=
        IsOpenEmbedding.inr.comp IsOpenEmbedding.sigmaMk
      exact hi.restrict (fun d hd => (cell_mem_punctured a i d).mpr hd)
        (isClosed_eq continuous_subtype_val continuous_const).isOpen_compl
    have hc' : ContinuousAt ((F ∘ (punctured a).restrictPreimage q) ∘ e) ⟨d,hd⟩ := by
      change ContinuousAt (fun d : {d : Disk n // d.1 ≠ 0} =>
        F ⟨cell a i d.1,(cell_mem_punctured a i d.1).mpr d.2⟩) ⟨d,hd⟩
      exact (hc i).continuousAt
    have result := (he.continuousAt_iff (g := F ∘ (punctured a).restrictPreimage q)).mp hc'
    exact result

abbrev PuncturedDisk (n : ℕ) := {d : Disk n // d.1 ≠ 0}

def puncturedBoundary (x : Sphere n) : PuncturedDisk n :=
  ⟨boundary n x,by
    intro h
    change x.1 = 0 at h
    have hx := x.2
    simp only [mem_sphere,dist_zero_right] at hx
    rw [h,norm_zero] at hx
    norm_num at hx⟩

def puncturedCell (i : ι) (d : PuncturedDisk n) : punctured a :=
  ⟨cell a i d.1,(cell_mem_punctured a i d.1).mpr d.2⟩

def puncturedBase (x : X) : punctured a := ⟨base a x,base_mem_punctured a x⟩

lemma puncturedCell_boundary (i : ι) (x : Sphere n) :
    puncturedCell a i (puncturedBoundary x) = puncturedBase a (a i x) :=
  Subtype.ext (cell_boundary a i x)

noncomputable def puncturedLift {Y : Type*} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(PuncturedDisk n,Y))
    (h : ∀ i x, g i (puncturedBoundary x) = f (a i x)) : C(punctured a,Y) := by
  classical
  let F : punctured a → Y := fun z => match heq : z.1 with
    | Sum.inl x => f x
    | Sum.inr p => g p.1 ⟨interior n p.2,by
        exact (cell_mem_punctured a p.1 (interior n p.2)).mp
          (by simpa only [cell_interior,← heq] using z.2)⟩
  have hcell (i : ι) : F ∘ puncturedCell a i = g i := by
    funext d
    by_cases hd : d.1.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : d.1 = interior n ⟨d.1.1,hd⟩ := rfl
      change F ⟨cell a i d.1,_⟩ = g i d
      have hc : cell a i d.1 = Sum.inr ⟨i,⟨d.1.1,hd⟩⟩ := (congrArg (cell a i) heq).trans (cell_interior a i ⟨d.1.1,hd⟩)
      simp only [hc,F]
      exact congrArg (g i) (Subtype.ext (Subtype.ext rfl))
    · let x : Sphere n := ⟨d.1.1,by
        have hm := d.1.2
        simp only [mem_closedBall,mem_ball,mem_sphere] at *
        exact le_antisymm hm (le_of_not_gt hd)⟩
      have heq : d.1 = boundary n x := rfl
      change F ⟨cell a i d.1,_⟩ = g i d
      have hc : cell a i d.1 = base a (a i x) := (congrArg (cell a i) heq).trans (cell_boundary a i x)
      simp only [hc,base,F]
      exact (h i x).symm.trans (congrArg (g i) (Subtype.ext (Subtype.ext rfl)))
  exact ⟨F,continuous_punctured a F f.continuous (fun i => by
    change Continuous (F ∘ puncturedCell a i)
    rw [hcell]
    exact (g i).continuous)⟩

@[simp] lemma puncturedLift_base {Y : Type*} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(PuncturedDisk n,Y))
    (h : ∀ i x, g i (puncturedBoundary x) = f (a i x)) (x : X) :
    puncturedLift a f g h (puncturedBase a x) = f x := rfl

@[simp] lemma puncturedLift_cell {Y : Type*} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(PuncturedDisk n,Y))
    (h : ∀ i x, g i (puncturedBoundary x) = f (a i x))
    (i : ι) (d : PuncturedDisk n) :
    puncturedLift a f g h (puncturedCell a i d) = g i d := by
  classical
  by_cases hd : d.1.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d.1 = interior n ⟨d.1.1,hd⟩ := rfl
    change puncturedLift a f g h ⟨cell a i d.1,_⟩ = _
    have hc : cell a i d.1 = Sum.inr ⟨i,⟨d.1.1,hd⟩⟩ := (congrArg (cell a i) heq).trans (cell_interior a i ⟨d.1.1,hd⟩)
    simp only [hc,puncturedLift,ContinuousMap.coe_mk]
    exact congrArg (g i) (Subtype.ext (Subtype.ext rfl))
  · let x : Sphere n := ⟨d.1.1,by
      have hm := d.1.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have hd : d = puncturedBoundary x := rfl
    rw [hd,puncturedCell_boundary,puncturedLift_base,h]

lemma punctured_surjective (z : punctured a) :
    (∃ x, z = puncturedBase a x) ∨ ∃ i d, z = puncturedCell a i d := by
  cases heq : z.1 with
  | inl x => exact Or.inl ⟨x,Subtype.ext heq⟩
  | inr p =>
    have hd : p.2.1 ≠ 0 := (cell_mem_punctured a p.1 (interior n p.2)).mp
      (by simpa only [cell_interior,← heq] using z.2)
    exact Or.inr ⟨p.1,⟨interior n p.2,hd⟩,Subtype.ext (heq.trans (cell_interior a p.1 p.2).symm)⟩

/-- Radial projection of a nonzero disk point onto its sphere. -/
def radialSphere : C(PuncturedDisk n,Sphere n) := by
  have hm (d : PuncturedDisk n) : ‖d.1.1‖⁻¹ • d.1.1 ∈ sphere (0 : Fin n → ℝ) 1 := by
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,
      abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr d.2)]
  refine ⟨fun d => ⟨‖d.1.1‖⁻¹ • d.1.1,hm d⟩,?_⟩
  exact (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
    (fun d : PuncturedDisk n => norm_ne_zero_iff.mpr d.2)).smul
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk hm

@[simp] lemma radialSphere_boundary (x : Sphere n) : radialSphere (puncturedBoundary x) = x := by
  apply Subtype.ext
  have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  change ‖x.1‖⁻¹ • x.1 = x.1
  rw [hx,inv_one,one_smul]

/-- Radial straight-line deformation, in the full disk. -/
def radialDisk : C(unitInterval × PuncturedDisk n,Disk n) := by
  let f (p : unitInterval × PuncturedDisk n) :=
    (1-(p.1:ℝ)) • p.2.1.1 + (p.1:ℝ) • (radialSphere p.2).1
  have hm (p : unitInterval × PuncturedDisk n) : f p ∈ closedBall (0 : Fin n → ℝ) 1 :=
    (convex_closedBall (0 : Fin n → ℝ) 1) p.2.1.2
      (sphere_subset_closedBall (radialSphere p.2).2)
      (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring)
  have hc : Continuous f :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (radialSphere.continuous.comp continuous_snd)))
  exact ⟨fun p => ⟨f p,hm p⟩,hc.subtype_mk hm⟩

@[simp] lemma radialDisk_zero (d : PuncturedDisk n) : radialDisk (0,d) = d.1 := by
  apply Subtype.ext
  simp [radialDisk]
@[simp] lemma radialDisk_one (d : PuncturedDisk n) : radialDisk (1,d) = boundary n (radialSphere d) := by
  apply Subtype.ext
  simp [radialDisk,boundary]
@[simp] lemma radialDisk_boundary (t : unitInterval) (x : Sphere n) :
    radialDisk (t,puncturedBoundary x) = boundary n x := by
  apply Subtype.ext
  simp only [radialDisk,ContinuousMap.coe_mk,radialSphere_boundary]
  change (1-(t:ℝ)) • x.1 + (t:ℝ) • x.1 = x.1
  rw [← add_smul,sub_add_cancel,one_smul]

end GroupRingTopology.Attachment

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X))

def radialRetraction : C(punctured a,X) :=
  puncturedLift a (.id X) (fun i => (a i).comp radialSphere)
    (fun i x => by simp only [ContinuousMap.comp_apply,radialSphere_boundary,ContinuousMap.id_apply])

@[simp] lemma radialRetraction_base (x : X) : radialRetraction a (puncturedBase a x) = x := rfl
@[simp] lemma radialRetraction_cell (i : ι) (d : PuncturedDisk n) :
    radialRetraction a (puncturedCell a i d) = a i (radialSphere d) := by
  exact puncturedLift_cell _ _ _ _ _ _

def radialPaths : C(punctured a,C(unitInterval,Space a)) := by
  let f : C(X × unitInterval,Space a) := ⟨fun p => base a p.1,(continuous_base a).comp continuous_fst⟩
  let g (i : ι) : C(PuncturedDisk n × unitInterval,Space a) :=
    (cell a i).comp (radialDisk.comp ⟨Prod.swap,continuous_swap⟩)
  have h (i : ι) (x : Sphere n) : (g i).curry (puncturedBoundary x) = f.curry (a i x) := by
    ext t
    change cell a i (radialDisk (t,puncturedBoundary x)) = base a (a i x)
    rw [radialDisk_boundary,cell_boundary]
  exact puncturedLift a f.curry (fun i => (g i).curry) h

@[simp] lemma radialPaths_base (x : X) (t : unitInterval) :
    radialPaths a (puncturedBase a x) t = base a x := rfl
@[simp] lemma radialPaths_cell (i : ι) (d : PuncturedDisk n) (t : unitInterval) :
    radialPaths a (puncturedCell a i d) t = cell a i (radialDisk (t,d)) := by
  unfold radialPaths
  rw [puncturedLift_cell]
  rfl

def puncturedInclusion : C(punctured a,Space a) := ⟨Subtype.val,continuous_subtype_val⟩
def radialEnd : C(punctured a,Space a) := (⟨base a,continuous_base a⟩ : C(X,Space a)).comp (radialRetraction a)

/-- The punctured attachment deformation-retracts to the original space. -/
def radialHomotopy : (puncturedInclusion a).Homotopy (radialEnd a) where
  toFun p := radialPaths a p.2 p.1
  continuous_toFun := (radialPaths a).uncurry.continuous.comp continuous_swap
  map_zero_left z := by
    rcases punctured_surjective a z with ⟨x,rfl⟩ | ⟨i,d,rfl⟩
    · rfl
    · rw [radialPaths_cell,radialDisk_zero]
      rfl
  map_one_left z := by
    rcases punctured_surjective a z with ⟨x,rfl⟩ | ⟨i,d,rfl⟩
    · rfl
    · rw [radialPaths_cell,radialDisk_one,cell_boundary]
      change base a (a i (radialSphere d)) = base a (radialRetraction a (puncturedCell a i d))
      rw [radialRetraction_cell]

@[simp] lemma radialHomotopy_base (x : X) (t : unitInterval) :
    radialHomotopy a (t,puncturedBase a x) = base a x := rfl

lemma cell_eq_openCell_iff (i j : ι) (d : Disk n) (x : OpenDisk n) :
    cell a i d = openCell a j x ↔ i = j ∧ d.1 = x.1 := by
  classical
  constructor
  · intro h
    by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
    · have hi : cell a i d = Sum.inr ⟨i,⟨d.1,hd⟩⟩ :=
        cell_interior a i ⟨d.1,hd⟩
      rw [hi] at h
      have hh : (⟨i,⟨d.1,hd⟩⟩ : Σ _ : ι, OpenDisk n) = ⟨j,x⟩ := Sum.inr_injective h
      exact ⟨congrArg Sigma.fst hh,congrArg (fun p : Σ _ : ι, OpenDisk n => p.2.1) hh⟩
    · let s : Sphere n := ⟨d.1,by
        have hm := d.2
        simp only [mem_sphere,mem_ball,mem_closedBall] at *
        exact le_antisymm hm (le_of_not_gt hd)⟩
      have hi : cell a i d = base a (a i s) := cell_boundary a i s
      rw [hi] at h
      cases h
  · rintro ⟨rfl,h⟩
    have hd : d = interior n x := Subtype.ext h
    rw [hd,cell_interior]
    rfl

lemma openCell_disjoint (i j : ι) (hij : i ≠ j) :
    Disjoint (Set.range (openCell a i)) (Set.range (openCell a j)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,rfl⟩ ⟨y,h⟩
  exact hij (congrArg Sigma.fst (Sum.inr_injective h)).symm

lemma openCell_selection_closed {I : Type*} (c : I → ι) (hc : Function.Injective c)
    (x : I → OpenDisk n) (S : Set (Space a))
    (hS : S ⊆ Set.range (fun i => openCell a (c i) (x i))) : IsClosed S := by
  rw [isClosed_iff]
  constructor
  · have h : base a ⁻¹' S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨i,hi⟩ := hS hy
      cases hi
    rw [h]
    exact isClosed_empty
  · intro j
    suffices (cell a j ⁻¹' S).Subsingleton from this.finite.isClosed
    intro d hd e he
    obtain ⟨i,hi⟩ := hS hd
    obtain ⟨k,hk⟩ := hS he
    have hdi := (cell_eq_openCell_iff a j (c i) d (x i)).mp hi.symm
    have hek := (cell_eq_openCell_iff a j (c k) e (x k)).mp hk.symm
    have hik : i = k := hc (hdi.1.symm.trans hek.1)
    subst k
    exact Subtype.ext (hdi.2.trans hek.2.symm)

/-- The weak adjunction topology prevents compact sets from meeting infinitely
many of the new open cells. No local-finiteness assumption is needed. -/
lemma compact_finitely_many_openCells {K : Set (Space a)} (hK : IsCompact K) :
    {i : ι | (K ∩ Set.range (openCell a i)).Nonempty}.Finite := by
  classical
  let I := {i : ι | (K ∩ Set.range (openCell a i)).Nonempty}
  have hchoice (i : I) : ∃ x : OpenDisk n, openCell a i.1 x ∈ K := by
    obtain ⟨z,hz,⟨x,hx⟩⟩ := i.2
    exact ⟨x,hx ▸ hz⟩
  choose x hx using hchoice
  let y : I → Space a := fun i => openCell a i.1 (x i)
  have hyinj : Function.Injective y := by
    intro i j h
    apply Subtype.ext
    exact congrArg Sigma.fst (Sum.inr_injective h)
  have hclosed : ∀ S ⊆ Set.range y, IsClosed S :=
    openCell_selection_closed a Subtype.val Subtype.val_injective x
  have hcompact : IsCompact (Set.range y) := hK.of_isClosed_subset
    (hclosed _ subset_rfl) (Set.range_subset_iff.mpr hx)
  have hdisc : IsDiscrete (Set.range y) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hclosed S hS,Set.inter_eq_left.mpr hS⟩
  have hrange := hcompact.finite hdisc
  have : Finite I := (Set.finite_range_iff hyinj).mp hrange
  exact Set.toFinite I

end GroupRingTopology.Attachment

open Set Topology
namespace GroupRingTopology.Cellular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def patchFun (A : Set X) (f : C(X,Y)) (g : C(A,Y)) (x : X) : Y := by
  classical
  exact if hx : x ∈ A then g ⟨x,hx⟩ else f x

lemma patchFun_on (A : Set X) (f : C(X,Y)) (g : C(A,Y)) (x : A) :
    patchFun A f g x = g x := by simp only [patchFun,dif_pos x.2]

lemma patchFun_off (A : Set X) (f : C(X,Y)) (g : C(A,Y)) {x : X} (hx : x ∉ A) :
    patchFun A f g x = f x := by simp only [patchFun,dif_neg hx]

lemma continuous_patchFun {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) :
    Continuous (patchFun A f g) := by
  classical
  have hOn : ContinuousOn (patchFun A f g) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : A.domRestrict (patchFun A f g) = g := funext (patchFun_on A f g)
    rw [heq]
    exact g.continuous
  have h := continuous_if (p := fun x => x ∈ A) (f := patchFun A f g) (g := f)
    (fun x hx => by
      have hxa : x ∈ A := hA.closure_eq ▸ hx.1
      exact (patchFun_on A f g ⟨x,hxa⟩).trans (hboundary ⟨x,hxa⟩ hx))
    (by simpa only [Set.ofPred_mem_eq,hA.closure_eq] using hOn) f.continuous.continuousOn
  convert h using 1
  ext x
  by_cases hx : x ∈ A
  · simp only [if_pos hx]
  · simp only [if_neg hx,patchFun_off A f g hx]

def patch {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) : C(X,Y) :=
  ⟨patchFun A f g,continuous_patchFun hA f g hboundary⟩

lemma patch_on {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) (x : A) :
    patch hA f g hboundary x = g x := patchFun_on A f g x

lemma patch_off {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) {x : X} (hx : x ∉ A) :
    patch hA f g hboundary x = f x := patchFun_off A f g hx

/-- Homotopies on a closed subset glue to the stationary homotopy outside it,
provided they are stationary on the frontier. -/
def patchHomotopy {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (H : (f.restrict A).Homotopy g)
    (hboundary : ∀ (t : unitInterval) (x : A), (x:X) ∈ frontier A → H (t,x) = f x) :
    f.Homotopy (patch hA f g (fun x hx => by simpa using hboundary 1 x hx)) := by
  let B : Set (unitInterval × X) := Prod.snd ⁻¹' A
  let H' : C(B,Y) := ⟨fun z => H (z.1.1,⟨z.1.2,z.2⟩),
    H.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))⟩
  let hB : IsClosed B := hA.preimage continuous_snd
  let F : C(unitInterval × X,Y) := f.comp ⟨Prod.snd,continuous_snd⟩
  have hb : ∀ z : B, (z : unitInterval × X) ∈ frontier B → H' z = F z := by
    intro z hz
    exact hboundary z.1.1 ⟨z.1.2,z.2⟩ (continuous_snd.frontier_preimage_subset A hz)
  refine ⟨patch hB F H' hb,?_,?_⟩
  · intro x
    change patch hB F H' hb (0,x) = f x
    by_cases hx : x ∈ A
    · rw [patch_on hB F H' hb ⟨(0,x),hx⟩]
      exact H.apply_zero ⟨x,hx⟩
    · exact patch_off hB F H' hb (x := (_,x)) hx
  · intro x
    change patch hB F H' hb (1,x) = patch hA f g _ x
    by_cases hx : x ∈ A
    · rw [patch_on hB F H' hb ⟨(1,x),hx⟩,patch_on hA f g _ ⟨x,hx⟩]
      exact H.apply_one ⟨x,hx⟩
    · rw [patch_off hB F H' hb (x := (_,x)) hx,patch_off hA f g _ hx]
      rfl

end GroupRingTopology.Cellular
open Set Metric Topology
open scoped NNReal
namespace GroupRingTopology.GeneralPosition

section
variable {K : Type*} [MetricSpace K] [CompactSpace K]

lemma lipschitz_mul {f g : C(K,ℝ)} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g) :
    LipschitzWith (‖f‖₊ * M + ‖g‖₊ * L) (f * g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [ContinuousMap.mul_apply,NNReal.coe_add,NNReal.coe_mul,coe_nnnorm]
  calc
    dist (f x * g x) (f y * g y)
        = ‖f x * (g x-g y) + g y * (f x-f y)‖ := by
          rw [dist_eq_norm]; congr 1; ring
    _ ≤ ‖f x * (g x-g y)‖ + ‖g y * (f x-f y)‖ := norm_add_le _ _
    _ = ‖f x‖ * dist (g x) (g y) + ‖g y‖ * dist (f x) (f y) := by
      rw [norm_mul,norm_mul,dist_eq_norm,dist_eq_norm]
    _ ≤ ‖f‖ * ((M:ℝ) * dist x y) + ‖g‖ * ((L:ℝ) * dist x y) := by
      gcongr
      · exact f.norm_coe_le_norm x
      · exact hg.dist_le_mul x y
      · exact g.norm_coe_le_norm y
      · exact hf.dist_le_mul x y
    _ = (‖f‖ * M + ‖g‖ * L) * dist x y := by ring

def lipschitzAlgebra : Subalgebra ℝ C(K,ℝ) where
  carrier := {f | ∃ L, LipschitzWith L f}
  zero_mem' := ⟨0,LipschitzWith.const 0⟩
  one_mem' := ⟨0,LipschitzWith.const 1⟩
  add_mem' := by rintro f g ⟨L,hL⟩ ⟨M,hM⟩; exact ⟨L+M,hL.add hM⟩
  mul_mem' := by rintro f g ⟨L,hL⟩ ⟨M,hM⟩; exact ⟨_,lipschitz_mul hL hM⟩
  algebraMap_mem' r := ⟨0,LipschitzWith.const r⟩

lemma lipschitzAlgebra_separates : (lipschitzAlgebra (K := K)).SeparatesPoints := by
  intro x y hxy
  refine ⟨fun z => dist z y,⟨⟨fun z => dist z y,continuous_id.dist continuous_const⟩,
    ⟨1,LipschitzWith.dist_left y⟩,rfl⟩,?_⟩
  simpa using hxy

/-- Uniform Lipschitz approximation on an arbitrary compact metric space. -/
lemma exists_lipschitz_approximation (f : C(K,ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(K,ℝ), (∃ L, LipschitzWith L g) ∧ ∀ x, ‖g x-f x‖ < ε := by
  obtain ⟨g,hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    lipschitzAlgebra lipschitzAlgebra_separates f f.continuous ε hε
  exact ⟨g,g.2,hg⟩

end

section
open Set Metric Topology
open scoped NNReal ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K]

lemma exists_lipschitz_vector_approximation {n : ℕ} (f : C(K,Fin n → ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(K,Fin n → ℝ), (∃ L, LipschitzWith L g) ∧ ∀ x, ‖g x-f x‖ < ε := by
  classical
  have hex : ∀ i : Fin n, ∃ g : C(K,ℝ), (∃ L, LipschitzWith L g) ∧
      ∀ x, ‖g x-f x i‖ < ε := fun i =>
    exists_lipschitz_approximation ⟨fun x => f x i,(continuous_apply i).comp f.continuous⟩ hε
  choose g hg he using hex
  choose L hL using hg
  let H : C(K,Fin n → ℝ) := ⟨fun x i => g i x,continuous_pi (fun i => (g i).continuous)⟩
  refine ⟨H,⟨Finset.univ.sup L,?_⟩,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)]
    intro i
    exact (hL i).dist_le_mul x y |>.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.le_sup (f := L) (Finset.mem_univ i)) dist_nonneg)
  · intro x
    exact (pi_norm_lt_iff hε).mpr (fun i => he i x)

omit [CompactSpace K] in
/-- A Lipschitz image of smaller Hausdorff dimension misses points in every
positive-radius ball of Euclidean target space. -/
lemma exists_missing_point {n : ℕ} {g : K → Fin n → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hdim : dimH (Set.univ : Set K) < n)
    (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ a ∈ Metric.ball c r, a ∉ Set.range g := by
  by_contra! h
  have hle : dimH (Metric.ball c r) ≤ dimH (Set.range g) := dimH_mono h
  rw [Real.dimH_ball_pi_fin _ hr] at hle
  exact (not_le_of_gt hdim) (hle.trans hg.dimH_range_le)

/-- Every map from a compact metric space of dimension less than n can be
uniformly approximated by a map into punctured ℝ^n. -/
lemma exists_nonzero_approximation {n : ℕ} (f : C(K,Fin n → ℝ))
    (hdim : dimH (Set.univ : Set K) < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(K,Fin n → ℝ), (∀ x, g x ≠ 0) ∧ ∀ x, ‖g x-f x‖ < ε := by
  obtain ⟨h,⟨L,hL⟩,hh⟩ := exists_lipschitz_vector_approximation f (half_pos hε)
  obtain ⟨a,ha,ha'⟩ := exists_missing_point hL hdim 0 (half_pos hε)
  refine ⟨h - ContinuousMap.const K a,?_,?_⟩
  · intro x hx
    apply ha'
    exact ⟨x,sub_eq_zero.mp hx⟩
  · intro x
    have ha : ‖a‖ < ε/2 := by simpa only [Metric.mem_ball,dist_zero_right] using ha
    change ‖(h x-a)-f x‖ < ε
    have hhx := hh x
    calc
      ‖(h x-a)-f x‖ = ‖(h x-f x)-a‖ := by congr 1; abel
      _ ≤ ‖h x-f x‖+‖a‖ := norm_sub_le _ _
      _ < ε := by linarith

end

open Set Metric Topology
open scoped NNReal ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K]

def cutoff (δ r : ℝ) : ℝ := min 1 (max 0 (2-r/δ))
lemma cutoff_nonneg (δ r : ℝ) : 0 ≤ cutoff δ r := le_min (by norm_num) (le_max_left _ _)
lemma cutoff_le_one (δ r : ℝ) : cutoff δ r ≤ 1 := min_le_left _ _
lemma cutoff_small {δ r : ℝ} (hδ : 0 < δ) (hr : r ≤ δ) : cutoff δ r = 1 := by
  apply min_eq_left
  apply le_max_of_le_right
  have : r/δ ≤ 1 := (div_le_one hδ).mpr hr
  linarith
lemma cutoff_large {δ r : ℝ} (hδ : 0 < δ) (hr : 2*δ ≤ r) : cutoff δ r = 0 := by
  have : 2 ≤ r/δ := (le_div_iff₀ hδ).mpr hr
  simp only [cutoff,max_eq_left (by linarith : 2-r/δ ≤ 0),min_eq_right (by norm_num : (0:ℝ)≤1)]
lemma continuous_cutoff (δ : ℝ) : Continuous (cutoff δ) :=
  continuous_const.min (continuous_const.max (continuous_const.sub (continuous_id.div_const δ)))

/-- General position relative to the region already far from the origin. -/
lemma exists_relative_nonzero_approximation {n : ℕ} (f : C(K,Fin n → ℝ))
    (hdim : dimH (Set.univ : Set K) < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : C(K,Fin n → ℝ), (∀ x, g x ≠ 0) ∧
      (∀ x, 2*δ ≤ ‖f x‖ → g x = f x) ∧ ∀ x, ‖g x-f x‖ < δ/2 := by
  obtain ⟨h,hne,hh⟩ := exists_nonzero_approximation f hdim (half_pos hδ)
  let g : C(K,Fin n → ℝ) := ⟨fun x => f x + cutoff δ ‖f x‖ • (h x-f x),
    f.continuous.add (((continuous_cutoff δ).comp f.continuous.norm).smul
      (h.continuous.sub f.continuous))⟩
  have hdist (x : K) : ‖g x-f x‖ < δ/2 := by
    change ‖(f x+cutoff δ ‖f x‖ • (h x-f x))-f x‖ < δ/2
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (cutoff_nonneg _ _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)).trans_lt (hh x)
  refine ⟨g,?_,?_,hdist⟩
  · intro x hx
    by_cases hnorm : ‖f x‖ ≤ δ
    · have hg : g x = h x := by
        change f x+cutoff δ ‖f x‖ • (h x-f x)=h x
        rw [cutoff_small hδ hnorm,one_smul,add_sub_cancel]
      exact hne x (hg.symm.trans hx)
    · have hd := hdist x
      rw [hx,zero_sub,norm_neg] at hd
      linarith
  · intro x hx
    change f x+cutoff δ ‖f x‖ • (h x-f x)=f x
    rw [cutoff_large hδ hx,zero_smul,add_zero]

omit [MetricSpace K] [CompactSpace K] in
/-- The straight-line homotopy from the original to the perturbed map stays
inside any disk of radius 4δ, and is stationary outside the core of radius 2δ. -/
lemma relative_interpolation_bound {n : ℕ} {f g : K → Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfix : ∀ x, 2*δ ≤ ‖f x‖ → g x = f x)
    (hdist : ∀ x, ‖g x-f x‖ < δ/2)
    (x : K) (hx : ‖f x‖ ≤ 4*δ) (t : unitInterval) :
    ‖f x+(t:ℝ) • (g x-f x)‖ ≤ 4*δ := by
  by_cases hc : 2*δ ≤ ‖f x‖
  · rw [hfix x hc,sub_self,smul_zero,add_zero]
    exact hx
  · have ht : ‖(t:ℝ) • (g x-f x)‖ ≤ ‖g x-f x‖ := by
      rw [norm_smul,Real.norm_of_nonneg t.2.1]
      exact mul_le_of_le_one_left (norm_nonneg _) t.2.2
    have hsum := norm_add_le (f x) ((t:ℝ) • (g x-f x))
    have hd := hdist x
    linarith

end GroupRingTopology.GeneralPosition

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal

namespace GroupRingTopology.Cellular

section
open Set Metric Topology
open scoped ENNReal NNReal
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {n : ℕ}

abbrev ChartDisk (n : ℕ) := Metric.ball (0 : Fin n → ℝ) 1
abbrev ChartCore (n : ℕ) := Metric.closedBall (0 : Fin n → ℝ) (1/2)

def chartCoreInclusion (n : ℕ) : C(ChartCore n,ChartDisk n) :=
  ⟨fun x => ⟨x.1, (mem_closedBall.mp x.2).trans_lt (by norm_num)⟩,
    continuous_subtype_val.subtype_mk _⟩

def chartCore (e : C(ChartDisk n,Y)) : C(ChartCore n,Y) := e.comp (chartCoreInclusion n)

lemma chartCore_closedEmbedding (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) :
    IsClosedEmbedding (chartCore e) := by
  apply (chartCore e).continuous.isClosedEmbedding
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : ChartDisk n => z.1) (he.injective h)

variable {K : Type*} [MetricSpace K]

def chartDomain (e : C(ChartDisk n,Y)) (f : C(K,Y)) : Set K := f ⁻¹' Set.range (chartCore e)

lemma chartDomain_closed (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y)) :
    IsClosed (chartDomain e f) := (chartCore_closedEmbedding e he).isClosed_range.preimage f.continuous

def coreCoordinate (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y)) :
    C(chartDomain e f,ChartCore n) :=
  ⟨fun x => (chartCore_closedEmbedding e he).toIsEmbedding.toHomeomorph.symm ⟨f x,x.2⟩,
    (chartCore_closedEmbedding e he).toIsEmbedding.toHomeomorph.symm.continuous.comp
      ((f.continuous.comp continuous_subtype_val).subtype_mk _)⟩

lemma coreCoordinate_fac (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y))
    (x : chartDomain e f) : chartCore e (coreCoordinate e he f x) = f x :=
  congrArg Subtype.val ((chartCore_closedEmbedding e he).toIsEmbedding.toHomeomorph.apply_symm_apply _)

lemma coreCoordinate_frontier (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y))
    (x : chartDomain e f) (hx : (x:K) ∈ frontier (chartDomain e f)) :
    ‖(coreCoordinate e he f x : Fin n → ℝ)‖ = 1/2 := by
  apply le_antisymm
  · simpa only [mem_closedBall,dist_zero_right] using (coreCoordinate e he f x).2
  · by_contra! h
    let U : Set (ChartDisk n) := {z | ‖(z : Fin n → ℝ)‖ < 1/2}
    have hU : IsOpen U := isOpen_lt (continuous_subtype_val.norm) continuous_const
    have hsub : f ⁻¹' (e '' U) ⊆ chartDomain e f := by
      intro y hy
      obtain ⟨z,hz,hzy⟩ := hy
      exact ⟨⟨z.1,by simpa only [mem_closedBall,dist_zero_right] using le_of_lt hz⟩,hzy⟩
    have hxU : (x:K) ∈ f ⁻¹' (e '' U) := by
      refine ⟨chartCoreInclusion n (coreCoordinate e he f x),h,?_⟩
      exact coreCoordinate_fac e he f x
    exact hx.2 (mem_interior.mpr ⟨f ⁻¹' (e '' U),hsub,
      (he.isOpenMap U hU).preimage f.continuous,hxU⟩)

omit [T2Space Y] in
lemma chartDomain_dimH_le (e : C(ChartDisk n,Y)) (f : C(K,Y)) :
    dimH (Set.univ : Set (chartDomain e f)) ≤ dimH (Set.univ : Set K) := by
  rw [← isometry_subtype_coe.dimH_image]
  exact dimH_mono (Set.subset_univ _)

end

section
open Set Metric Topology
open scoped ENNReal NNReal
variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}
variable {K : Type*} [MetricSpace K]

def chartCenter (e : C(ChartDisk n,Y)) : Y := e ⟨0,by simp⟩

/-- A map of smaller dimension can be homotoped off one cell centre,
without changing it outside the cell. This works for merely continuous maps,
not just piecewise linear maps. -/
lemma exists_chart_avoidance [T2Space Y] [CompactSpace K] (e : C(ChartDisk n,Y)) (he : IsOpenEmbedding e) (f : C(K,Y))
    (hdim : dimH (Set.univ : Set K) < n) :
    ∃ (g : C(K,Y)) (H : f.Homotopy g),
      (∀ x, g x ≠ chartCenter e) ∧
      (∀ (t : unitInterval) (x : K), f x ∉ Set.range e → H (t,x) = f x) ∧
      (∀ (t : unitInterval) (x : K), H (t,x) = f x ∨ H (t,x) ∈ Set.range e) := by
  let A := chartDomain e f
  have hA : IsClosed A := chartDomain_closed e he f
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  let u : C(A,Fin n → ℝ) := ⟨fun x => (coreCoordinate e he f x).1,
    continuous_subtype_val.comp (coreCoordinate e he f).continuous⟩
  obtain ⟨v,hv0,hvfix,hvdist⟩ := GeneralPosition.exists_relative_nonzero_approximation u
    ((chartDomain_dimH_le e f).trans_lt hdim) (δ := 1/8) (by norm_num)
  have hi (t : unitInterval) (x : A) : ‖u x+(t:ℝ) • (v x-u x)‖ ≤ 1/2 := by
    have hu : ‖u x‖ ≤ 4*(1/8:ℝ) := by
      simpa only [u,ContinuousMap.coe_mk,show (4:ℝ)*(1/8)=1/2 by norm_num,mem_closedBall,dist_zero_right]
        using (coreCoordinate e he f x).2
    simpa only [show (4:ℝ)*(1/8)=1/2 by norm_num] using
      GeneralPosition.relative_interpolation_bound (by norm_num : (0:ℝ)<1/8)
        hvfix hvdist x hu t
  have hvc (x : A) : v x ∈ ChartCore n := by
    have h := hi 1 x
    simpa only [Set.Icc.coe_one,one_smul,add_sub_cancel,mem_closedBall,dist_zero_right] using h
  let vcore : C(A,ChartCore n) := ⟨fun x => ⟨v x,hvc x⟩,
    v.continuous.subtype_mk hvc⟩
  let gA : C(A,Y) := (chartCore e).comp vcore
  let HA : (f.restrict A).Homotopy gA :=
    { toFun := fun tx => chartCore e ⟨u tx.2+(tx.1:ℝ) • (v tx.2-u tx.2),by
        simpa only [mem_closedBall,dist_zero_right] using hi tx.1 tx.2⟩
      continuous_toFun := (chartCore e).continuous.comp
        (((u.continuous.comp continuous_snd).add
          ((continuous_subtype_val.comp continuous_fst).smul
            ((v.continuous.comp continuous_snd).sub (u.continuous.comp continuous_snd)))).subtype_mk
            (fun tx => by
              simpa only [ChartCore,mem_closedBall,dist_zero_right,Pi.add_apply,
                Pi.smul_apply',Pi.sub_apply,Function.comp_apply] using hi tx.1 tx.2))
      map_zero_left := fun x => by
        simp only [Set.Icc.coe_zero,zero_smul,add_zero]
        exact coreCoordinate_fac e he f x
      map_one_left := fun x => by
        simp only [Set.Icc.coe_one,one_smul,add_sub_cancel]
        rfl }
  have hboundary (t : unitInterval) (x : A) (hx : (x:K) ∈ frontier A) :
      HA (t,x) = f x := by
    have hfix : v x = u x := hvfix x (by
      change 2*(1/8:ℝ) ≤ ‖(coreCoordinate e he f x).1‖
      rw [coreCoordinate_frontier e he f x hx]
      norm_num)
    change chartCore e ⟨u x+(t:ℝ) • (v x-u x),_⟩ = f x
    simp only [hfix,sub_self,smul_zero,add_zero]
    exact coreCoordinate_fac e he f x
  let hg : ∀ x : A, (x:K) ∈ frontier A → gA x = f x :=
    fun x hx => by simpa using hboundary 1 x hx
  let g := patch hA f gA hg
  let H : f.Homotopy g := patchHomotopy hA f gA HA hboundary
  have hOn (t : unitInterval) (x : A) : H (t,(x:K)) = HA (t,x) := by
    change patchFun (Prod.snd ⁻¹' A) _ _ (t,(x:K)) = _
    rw [patchFun,dif_pos (show (t,(x:K)) ∈ Prod.snd ⁻¹' A from x.2)]
    rfl
  have hOff (t : unitInterval) (x : K) (hx : x ∉ A) : H (t,x) = f x := by
    change patchFun (Prod.snd ⁻¹' A) _ _ (t,x) = _
    rw [patchFun,dif_neg (show (t,x) ∉ Prod.snd ⁻¹' A from hx)]
    rfl
  refine ⟨g,H,?_,?_,?_⟩
  · intro x hzero
    by_cases hx : x ∈ A
    · have hv : chartCore e (vcore ⟨x,hx⟩) = chartCenter e := by
        exact (patch_on hA f gA hg ⟨x,hx⟩).symm.trans hzero
      have hu := congrArg (fun z : ChartDisk n => z.1) (he.injective hv)
      exact hv0 ⟨x,hx⟩ hu
    · have hfx : f x = chartCenter e := (patch_off hA f gA hg hx).symm.trans hzero
      apply hx
      exact ⟨⟨0,by simp⟩,hfx.symm⟩
  · intro t x hx
    apply hOff
    rintro ⟨z,hz⟩
    exact hx ⟨chartCoreInclusion n z,hz⟩
  · intro t x
    by_cases hx : x ∈ A
    · right
      rw [hOn t ⟨x,hx⟩]
      exact ⟨_,rfl⟩
    · exact Or.inl (hOff t x hx)

end

open Set Metric Topology
open scoped ENNReal NNReal
section
variable {Y : Type*} [TopologicalSpace Y] {K : Type*} [TopologicalSpace K]

lemma homotopy_trans_pointwise {f g h : C(K,Y)} (H : f.Homotopy g) (J : g.Homotopy h)
    (P : K → Y → Prop) (hH : ∀ t x, P x (H (t,x))) (hJ : ∀ t x, P x (J (t,x))) :
    ∀ t x, P x (H.trans J (t,x)) := by
  intro t x
  erw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _ x
  · exact hJ _ x

end
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {n : ℕ}
variable {K : Type*} [MetricSpace K] [CompactSpace K] {ι : Type*}
variable (e : ι → C(ChartDisk n,Y)) (he : ∀ i, IsOpenEmbedding (e i))
variable (hd : Pairwise (fun i j => Disjoint (Set.range (e i)) (Set.range (e j))))

omit [T2Space Y] in
lemma chartCenter_mem_range (i : ι) : chartCenter (e i) ∈ Set.range (e i) := ⟨_,rfl⟩

include he hd in
lemma exists_finite_chart_avoidance (f : C(K,Y)) (hdim : dimH (Set.univ : Set K) < n)
    (S : Finset ι) :
    ∃ (g : C(K,Y)) (H : f.Homotopy g),
      (∀ i ∈ S, ∀ x, g x ≠ chartCenter (e i)) ∧
      (∀ t x, H (t,x) = f x ∨ ∃ i ∈ S, H (t,x) ∈ Set.range (e i)) ∧
      (∀ t x, (∀ i ∈ S, f x ∉ Set.range (e i)) → H (t,x) = f x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨f,.refl f,by simp,(fun _ _ => Or.inl rfl),fun _ _ _ => rfl⟩
  | @insert a S ha ih =>
    obtain ⟨g,H,hg,hH,hstat⟩ := ih
    obtain ⟨g',J,hg',hJstat,hJ⟩ := exists_chart_avoidance (e a) (he a) g hdim
    refine ⟨g',H.trans J,?_,?_,?_⟩
    · intro i hi x
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hg' x
      · intro hzero
        rcases hJ 1 x with hj | hj
        · have hh : g' x = g x := by simpa using hj
          exact hg i hi x (hh.symm.trans hzero)
        · have hj : g' x ∈ Set.range (e a) := by simpa using hj
          rw [hzero] at hj
          exact (hd (by intro heq; subst i; exact ha hi)).notMem_of_mem_left hj
            (chartCenter_mem_range e i)
    · apply homotopy_trans_pointwise H J
        (fun x y => y = f x ∨ ∃ i ∈ insert a S, y ∈ Set.range (e i))
      · intro t x
        rcases hH t x with h | ⟨i,hi,h⟩
        · exact Or.inl h
        · exact Or.inr ⟨i,Finset.mem_insert_of_mem hi,h⟩
      · intro t x
        rcases hJ t x with h | h
        · rw [h]
          have hh : g x = f x ∨ ∃ i ∈ S, g x ∈ Set.range (e i) := by simpa using hH 1 x
          rcases hh with h | ⟨i,hi,h⟩
          · exact Or.inl h
          · exact Or.inr ⟨i,Finset.mem_insert_of_mem hi,h⟩
        · exact Or.inr ⟨a,Finset.mem_insert_self _ _,h⟩
    · intro t x hx
      have hfixed : ∀ t, H (t,x) = f x := fun t =>
        hstat t x (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      have hgx : g x = f x := by simpa using hfixed 1
      have hjfixed : ∀ t, J (t,x) = f x := fun t =>
        (hJstat t x (by rw [hgx]; exact hx a (Finset.mem_insert_self _ _))).trans hgx
      erw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact hfixed _
      · exact hjfixed _

include he hd in
lemma exists_all_chart_avoidance (f : C(K,Y)) (hdim : dimH (Set.univ : Set K) < n)
    (S : Finset ι) (hs : ∀ i, i ∉ S → ∀ x, f x ∉ Set.range (e i)) :
    ∃ (g : C(K,Y)) (H : f.Homotopy g),
      (∀ i x, g x ≠ chartCenter (e i)) ∧
      (∀ t x, (∀ i, f x ∉ Set.range (e i)) → H (t,x) = f x) := by
  classical
  obtain ⟨g,H,hg,hH,hstat⟩ := exists_finite_chart_avoidance e he hd f hdim S
  refine ⟨g,H,?_,?_⟩
  · intro i x
    by_cases hi : i ∈ S
    · exact hg i hi x
    · intro hzero
      have hh : g x = f x ∨ ∃ j ∈ S, g x ∈ Set.range (e j) := by simpa using hH 1 x
      rcases hh with h | ⟨j,hj,h⟩
      · apply hs i hi x
        rw [← h,hzero]
        exact chartCenter_mem_range e i
      · rw [hzero] at h
        exact (hd (by intro heq; subst j; exact hi hj)).notMem_of_mem_left h
          (chartCenter_mem_range e i)
  · intro t x hx
    exact hstat t x (fun i _ => hx i)

end GroupRingTopology.Cellular

namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X)) [T2Space (Space a)]
variable {K : Type*} [MetricSpace K] [CompactSpace K]

def chart (i : ι) : C(Cellular.ChartDisk n,Space a) :=
  ⟨openCell a i,(openCell_openEmbedding a i).continuous⟩

/-- Maps of dimension below the newly attached cells can be deformed into the
old space. The deformation is stationary on the original preimage of it. -/
lemma exists_deformation_into_base (f : C(K,Space a))
    (hdim : dimH (Set.univ : Set K) < n) :
    ∃ (g : C(K,X)) (H : f.Homotopy ((⟨base a,continuous_base a⟩ : C(X,Space a)).comp g)),
      ∀ t x, f x ∈ Set.range (base a) → H (t,x) = f x := by
  classical
  let I := {i : ι | (Set.range f ∩ Set.range (openCell a i)).Nonempty}
  have hI : I.Finite := compact_finitely_many_openCells a (isCompact_range f.continuous)
  have hs : ∀ i, i ∉ hI.toFinset → ∀ x, f x ∉ Set.range (chart a i) := by
    intro i hi x hx
    apply hi
    rw [Set.Finite.mem_toFinset]
    exact ⟨f x,Set.mem_range_self x,hx⟩
  obtain ⟨g,H,hg,hstat⟩ := Cellular.exists_all_chart_avoidance (chart a)
    (fun i => openCell_openEmbedding a i) (fun i j hij => openCell_disjoint a i j hij)
    f hdim hI.toFinset hs
  have hgp (x : K) : g x ∈ punctured a := by
    rintro ⟨i,hi⟩
    exact hg i x hi.symm
  let gp : C(K,punctured a) := ⟨fun x => ⟨g x,hgp x⟩,g.continuous.subtype_mk hgp⟩
  let J := (radialHomotopy a).compContinuousMap gp
  have hJ0 : (puncturedInclusion a).comp gp = g := rfl
  let J' : g.Homotopy ((radialEnd a).comp gp) := hJ0 ▸ J
  refine ⟨(radialRetraction a).comp gp,H.trans J',?_⟩
  intro t x hx
  obtain ⟨y,hy⟩ := hx
  have hfixed (s : unitInterval) : H (s,x) = f x := by
    apply hstat s x
    intro i
    rintro ⟨d,hd⟩
    rw [← hy] at hd
    cases hd
  have hgx : g x = base a y := by simpa only [ContinuousMap.Homotopy.apply_one,← hy] using hfixed 1
  have hgp' : gp x = puncturedBase a y := Subtype.ext hgx
  have hjfixed (s : unitInterval) : J' (s,x) = f x := by
    change radialHomotopy a (s,gp x) = f x
    rw [hgp',radialHomotopy_base,hy]
  erw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hfixed _
  · exact hjfixed _

end GroupRingTopology.Attachment
open Set Metric Topology
open scoped NNReal ENNReal
namespace GroupRingTopology.GeneralPosition

lemma lipschitz_insertNth {n : ℕ} (i : Fin (n+1)) (c : ℝ) :
    LipschitzWith 1 (Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i c : (Fin n → ℝ) → (Fin (n+1) → ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  rw [dist_pi_le_iff dist_nonneg]
  intro j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp only [Fin.insertNth_apply_same,dist_self,dist_nonneg]
  · simp only [Fin.insertNth_apply_succAbove]
    exact dist_le_pi_dist x y k

lemma sphere_subset_faces (n : ℕ) :
    Metric.sphere (0 : Fin (n+1) → ℝ) 1 ⊆
      ⋃ i : Fin (n+1), ⋃ c ∈ ({1,-1}:Set ℝ), Set.range (Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i c : (Fin n → ℝ) → _) := by
  intro x hx
  have hxnorm : ‖x‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
  have hi : ∃ i, 1 ≤ ‖x i‖ := by
    by_contra! hh
    have := (pi_norm_lt_iff (by norm_num : (0:ℝ)<1)).mpr hh
    linarith
  obtain ⟨i,hi⟩ := hi
  have heq : |x i| = 1 := le_antisymm ((norm_le_pi_norm x i).trans_eq hxnorm) hi
  have hc : x i ∈ ({1,-1}:Set ℝ) := by
    rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp heq with h | h <;> simp [h]
  refine Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨x i,Set.mem_iUnion.mpr ⟨hc,?_⟩⟩⟩
  exact ⟨fun j => x (i.succAbove j),Fin.insertNth_self_removeNth _ _⟩

lemma dimH_cube_boundary_le (n : ℕ) :
    dimH (Metric.sphere (0 : Fin (n+1) → ℝ) 1) ≤ n := by
  apply (dimH_mono (sphere_subset_faces n)).trans
  rw [dimH_iUnion]
  apply iSup_le
  intro i
  rw [dimH_bUnion (Set.toFinite ({1,-1}:Set ℝ)).countable]
  apply iSup_le
  intro c
  apply iSup_le
  intro _
  exact (lipschitz_insertNth i c).dimH_range_le.trans_eq (Real.dimH_univ_pi_fin n)

lemma dimH_cube_boundary_subtype_le (n : ℕ) :
    dimH (Set.univ : Set (Metric.sphere (0 : Fin (n+1) → ℝ) 1)) ≤ n := by
  rw [← isometry_subtype_coe.dimH_image]
  simpa only [Subtype.range_coe_subtype,Set.image_univ,Set.ofPred_mem_eq] using dimH_cube_boundary_le n

end GroupRingTopology.GeneralPosition

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal

namespace GroupRingTopology.Attachment

section
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X)) [T2Space (Space a)]

lemma sphere_filling_preserved {m : ℕ} (hm : m < n)
    (hX : ∀ f : C(Sphere (m+1),X), SphereTopology.Extends f)
    (f : C(Sphere (m+1),Space a)) : SphereTopology.Extends f := by
  let := SphereTopology.sphere_nonempty m
  have hdim : dimH (Set.univ : Set (Sphere (m+1))) < n :=
    (GeneralPosition.dimH_cube_boundary_subtype_le m).trans_lt (by exact_mod_cast hm)
  obtain ⟨g,H,_⟩ := exists_deformation_into_base a f hdim
  apply SphereTopology.extends_of_homotopy H
  obtain ⟨F,hF⟩ := hX g
  refine ⟨(⟨base a,continuous_base a⟩ : C(X,Space a)).comp F,?_⟩
  ext x
  exact congrArg (base a) (ContinuousMap.congr_fun hF x)

lemma dimH_disk_subtype_le (m : ℕ) : dimH (Set.univ : Set (Disk m)) ≤ m := by
  rw [← isometry_subtype_coe.dimH_image]
  have hm := dimH_mono (Set.subset_univ (closedBall (0 : Fin m → ℝ) 1))
  simpa only [Set.image_univ,Subtype.range_coe_subtype,Set.ofPred_mem_eq,Real.dimH_univ_pi_fin] using hm

/-- Relative cellular approximation implies that a low-dimensional sphere that
bounds after a high-dimensional attachment already bounded beforehand. -/
lemma filling_reflected {m : ℕ} (hm : m < n) (b : C(Sphere m,X))
    (hb : SphereTopology.Extends ((⟨base a,continuous_base a⟩ : C(X,Space a)).comp b)) :
    SphereTopology.Extends b := by
  obtain ⟨F,hF⟩ := hb
  have hdim : dimH (Set.univ : Set (Disk m)) < n :=
    (dimH_disk_subtype_le m).trans_lt (by exact_mod_cast hm)
  obtain ⟨g,H,hstat⟩ := exists_deformation_into_base a F hdim
  refine ⟨g,?_⟩
  ext x
  apply (base_closedEmbedding a).injective
  have hb' : F (SphereTopology.boundary m x) = base a (b x) := ContinuousMap.congr_fun hF x
  have hh := hstat 1 (SphereTopology.boundary m x) ⟨b x,hb'.symm⟩
  simpa only [ContinuousMap.Homotopy.apply_one,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hb'] using hh

end
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
variable {ι : Type*} {n : ℕ} (a : ι → C(Sphere n,X)) [Nonempty (Sphere n)]
lemma pathConnectedSpace : PathConnectedSpace (Space a) := by
  let x₀ : X := Classical.choice inferInstance
  let s₀ : Sphere n := Classical.choice inferInstance
  have hj : ∀ z : Space a, Joined (base a x₀) z := by
    intro z
    cases z with
    | inl x => exact (PathConnectedSpace.joined x₀ x).map (continuous_base a)
    | inr p =>
      have h : Joined (boundary n s₀) (interior n p.2) := PathConnectedSpace.joined _ _
      have hh := h.map (cell a p.1).continuous
      rw [cell_interior,cell_boundary] at hh
      exact ((PathConnectedSpace.joined x₀ (a p.1 s₀)).map (continuous_base a)).trans hh
  exact ⟨⟨base a x₀⟩,fun x y => (hj x).symm.trans (hj y)⟩
end GroupRingTopology.Attachment

namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G) (rels : Set (FreeGroup S))
variable (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
variable (hs : Function.Surjective (FreeGroup.lift s))
variable (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels)

instance presentationCoverT2 : T2Space (PresentationCover s rels hrel) :=
  t2Space _ (realSeparated _ (realSeparated_of_tychonoff (Y := G)))

instance presentationCoverCW : CWComplex (Set.univ : Set (PresentationCover s rels hrel)) :=
  layerCW _ (graph_dimension s)

include hs in
lemma presentationCover_pathConnected : PathConnectedSpace (PresentationCover s rels hrel) := by
  have hgen : Subgroup.closure (Set.range s) = ⊤ := by
    rw [←FreeGroup.range_lift_eq_closure,MonoidHom.range_eq_top]
    exact hs
  let := graph_pathConnected s hgen
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _

include hs hker in
lemma presentationCover_sphereFill (b : C(Sphere 2,PresentationCover s rels hrel)) : SphereTopology.Extends b := by
  let := SphereTopology.sphere_nonempty 1
  have hdim : dimH (Set.univ : Set (Sphere 2)) < 2 :=
    (GeneralPosition.dimH_cube_boundary_subtype_le 1).trans_lt (by norm_num)
  obtain ⟨g,H,_⟩ := exists_deformation_into_base _ b hdim
  apply SphereTopology.extends_of_homotopy H
  exact SphereTopology.extends_of_nullhomotopic
    (((presentationGraphNullhomotopy s rels hrel hs hker).compContinuousMap g).symm)

include hs hker in
lemma presentationCover_simplyConnected : SimplyConnectedSpace (PresentationCover s rels hrel) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨presentationCover_pathConnected s rels hrel hs,?_⟩
  intro x p
  obtain ⟨F,hF⟩ := presentationCover_sphereFill s rels hrel hs hker (LoopSphere.map p)
  apply LoopSphere.homotopic_of_fill p F
  intro z
  exact ContinuousMap.congr_fun hF z
end GroupRingTopology.Cayley

namespace GroupRingTopology
variable {G : Type u} [Group G] {A : Type v} [MulAction G A]

abbrev Orbits := Quotient (MulAction.orbitRel G A)

lemma orbit_mk_smul (g : G) (a : A) : (Quotient.mk'' (g • a) : Orbits (G := G) (A := A)) = Quotient.mk'' a := by
  apply Quotient.sound
  exact ⟨g,rfl⟩

lemma orbit_out_translate (a : A) : ∃ g : G, a = g • (Quotient.mk'' a : Orbits (G := G)).out := by
  have h := Quotient.exact (Quotient.out_eq' (q := (Quotient.mk'' a : Orbits (G := G))))
  obtain ⟨g,hg⟩ := h
  refine ⟨g⁻¹,?_⟩
  rw [←hg,inv_smul_smul]

variable (hfree : ∀ (g : G) (a : A), g • a = a → g = 1)

include hfree in
lemma orbitCoordinates_bijective : Function.Bijective (fun p : G × Orbits (G := G) (A := A) => p.1 • p.2.out) := by
  constructor
  · rintro ⟨g,q⟩ ⟨h,r⟩ he
    have hqr : q = r := by
      have hh := congrArg (fun a : A => (Quotient.mk'' a : Orbits (G := G))) he
      simpa only [orbit_mk_smul,Quotient.out_eq'] using hh
    subst r
    change g • q.out = h • q.out at he
    have hh : (h⁻¹*g) • q.out = q.out := by rw [mul_smul,he,inv_smul_smul]
    have hh := hfree (h⁻¹*g) q.out hh
    have hgh : g = h := (inv_mul_eq_one.mp hh).symm
    exact Prod.ext hgh rfl
  · intro a
    obtain ⟨g,hg⟩ := orbit_out_translate (G := G) a
    exact ⟨(g,Quotient.mk'' a),hg.symm⟩

def orbitCoordinates : (G × Orbits (G := G) (A := A)) ≃ A :=
  Equiv.ofBijective _ (orbitCoordinates_bijective hfree)

lemma orbitCoordinates_apply (g : G) (q : Orbits (G := G) (A := A)) :
    orbitCoordinates hfree (g,q) = g • q.out := rfl

end GroupRingTopology

open Set Metric Topology
namespace GroupRingTopology.Cellular
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]
variable [CWComplex (univ : Set X)] {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)

def actionChart (n : ℕ) (i : G × ι n) : PartialEquiv (Fin n → ℝ) X :=
  (RelCWComplex.map n (σ n (1,i.2))).trans (Homeomorph.smul i.1).toEquiv.toPartialEquiv

lemma actionChart_apply (n : ℕ) (i : G × ι n) (x : Fin n → ℝ) :
    actionChart σ n i x = i.1 • RelCWComplex.map n (σ n (1,i.2)) x := rfl

lemma actionChart_image (n : ℕ) (i : G × ι n) (A : Set (Fin n → ℝ)) :
    actionChart σ n i '' A = (fun x : X => i.1 • x) '' (RelCWComplex.map n (σ n (1,i.2)) '' A) :=
  Set.image_comp (fun x : X => i.1 • x) (RelCWComplex.map n (σ n (1,i.2))) A

lemma actionChart_source (n : ℕ) (i : G × ι n) :
    (actionChart σ n i).source = ball 0 1 := by
  simp [actionChart,PartialEquiv.trans_source,RelCWComplex.source_eq]

lemma actionChart_continuousOn (n : ℕ) (i : G × ι n) :
    ContinuousOn (actionChart σ n i) (closedBall 0 1) :=
  (continuous_const_smul i.1).comp_continuousOn (RelCWComplex.continuousOn _ _)

lemma actionChart_continuousOn_symm (n : ℕ) (i : G × ι n) :
    ContinuousOn (actionChart σ n i).symm (actionChart σ n i).target := by
  change ContinuousOn (fun y => (RelCWComplex.map n (σ n (1,i.2))).symm (i.1⁻¹ • y))
    (univ ∩ (fun y : X => i.1⁻¹ • y) ⁻¹' (RelCWComplex.map n (σ n (1,i.2))).target)
  exact (RelCWComplex.continuousOn_symm _ _).comp (continuous_const_smul _).continuousOn
    (fun _ h => h.2)

variable
  (ho : ∀ n (g : G) (i : ι n),
    (fun x : X => g • x) '' RelCWComplex.openCell n (σ n (1,i)) = RelCWComplex.openCell n (σ n (g,i)))
  (hc : ∀ n (g : G) (i : ι n),
    (fun x : X => g • x) '' RelCWComplex.closedCell n (σ n (1,i)) = RelCWComplex.closedCell n (σ n (g,i)))

include ho in
lemma actionChart_open (n : ℕ) (i : G × ι n) :
    actionChart σ n i '' ball 0 1 = RelCWComplex.openCell n (σ n i) := by
  rw [actionChart_image]
  exact ho n i.1 i.2

include hc in
lemma actionChart_closed (n : ℕ) (i : G × ι n) :
    actionChart σ n i '' closedBall 0 1 = RelCWComplex.closedCell n (σ n i) := by
  rw [actionChart_image]
  exact hc n i.1 i.2

omit [ContinuousConstSMul G X] in
include hc in
lemma closedCell_smul (n : ℕ) (g h : G) (i : ι n) :
    (fun x : X => g • x) '' RelCWComplex.closedCell n (σ n (h,i)) =
      RelCWComplex.closedCell n (σ n (g*h,i)) := by
  rw [←hc n h i,←Set.image_comp]
  simpa only [Function.comp_def,mul_smul] using hc n (g*h) i

variable [T2Space X]

/-- A free permutation of cell orbits can be made strictly equivariant at the
level of characteristic maps. This changes neither the space nor the cells. -/
@[instance_reducible]
def actionCW : CWComplex (univ : Set X) where
  cell n := G × ι n
  map := actionChart σ
  source_eq := actionChart_source σ
  continuousOn := actionChart_continuousOn σ
  continuousOn_symm := actionChart_continuousOn_symm σ
  pairwiseDisjoint' := by
    intro p _ q _ hpq
    change Disjoint (actionChart σ p.1 p.2 '' ball 0 1) (actionChart σ q.1 q.2 '' ball 0 1)
    rw [actionChart_open σ ho,actionChart_open σ ho]
    apply CWComplex.disjoint_openCell_of_ne
    intro he
    apply hpq
    cases p with | mk n i =>
      cases q with | mk m j =>
        have hnm : n = m := congrArg Sigma.fst he
        subst m
        have hij : σ n i = σ n j := (Sigma.mk.inj he).2 |> eq_of_heq
        exact congrArg (Sigma.mk n) ((σ n).injective hij)
  mapsTo' := by
    classical
    intro n i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n (σ n (1,i.2))
    let f (m : ℕ) (j : RelCWComplex.cell (univ : Set X) m) : G × ι m :=
      (i.1 * ((σ m).symm j).1,((σ m).symm j).2)
    refine ⟨fun m => (I m).image (f m),?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map n (σ n (1,i.2)) x ∈ RelCWComplex.cellFrontier n (σ n (1,i.2)) from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨m,hm,j,hj,hxj⟩ := h
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
      ⟨f m j,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
    rw [actionChart_closed σ hc]
    change i.1 • RelCWComplex.map n (σ n (1,i.2)) x ∈ RelCWComplex.closedCell m
      (σ m (i.1 * ((σ m).symm j).1,((σ m).symm j).2))
    rw [←closedCell_smul σ hc]
    refine ⟨_,?_,rfl⟩
    simpa only [Prod.eta,Equiv.apply_symm_apply] using hxj
  closed' := by
    intro A hA hclosed
    apply (CWComplex.closed (univ : Set X) A hA).mpr
    intro n j
    obtain ⟨i,rfl⟩ := (σ n).surjective j
    simpa only [actionChart_closed σ hc] using hclosed n i
  union' := by
    simp only [actionChart_closed σ hc]
    have he (n : ℕ) : (⋃ j : G × ι n, RelCWComplex.closedCell n (σ n j)) =
        ⋃ j : RelCWComplex.cell (univ : Set X) n, RelCWComplex.closedCell n j := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨j,hj⟩; exact ⟨σ n j,hj⟩
      · rintro ⟨j,hj⟩; exact ⟨(σ n).symm j,by simpa only [Equiv.apply_symm_apply] using hj⟩
    simp_rw [he]
    exact CWComplex.union

omit [T2Space X] in
lemma actionChart_smul (n : ℕ) (g : G) (i : G × ι n) (x : Fin n → ℝ) :
    actionChart σ n (g*i.1,i.2) x = g • actionChart σ n i x := by
  exact mul_smul _ _ _
end GroupRingTopology.Cellular

namespace GroupRingTopology.Milnor
open Set Metric Topology GroupRingTopology.Simplicial
variable (G : Type u) [Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

lemma vertexTranslate_injective (g : G) : Function.Injective (fun v : ℕ × G => (v.1,g*v.2)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change (i,g*a) = (j,g*b) at h
  apply Prod.ext
  · simpa only using congrArg (fun v : ℕ × G => v.1) h
  · exact mul_left_cancel (congrArg Prod.snd h)

lemma translate_card (g : G) (s : Finset (ℕ × G)) : (translate g s).card = s.card :=
  Finset.card_image_of_injective _ (vertexTranslate_injective G g)

abbrev StageCell (S : Shapes G) (n : ℕ) := Simplicial.Cell (stage G S) n

def cellTranslate (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) : StageCell G S n :=
  ⟨⟨translate g c.1.1,orbitSpan_invariant _ g c.1.2⟩,by rw [translate_card]; exact c.2⟩

instance cellAction (S : Shapes G) (n : ℕ) : MulAction G (StageCell G S n) where
  smul := cellTranslate G S n
  one_smul c := by apply Subtype.ext; apply Subtype.ext; exact translate_one _
  mul_smul g h c := by apply Subtype.ext; apply Subtype.ext; exact (translate_mul _ _ _).symm

lemma cell_smul_val (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (g • c).1.1 = translate g c.1.1 := rfl

lemma cellAction_free (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n)
    (h : g • c = c) : g = 1 := by
  have he : translate g c.1.1 = c.1.1 := congrArg (fun c : StageCell G S n => c.1.1) h
  obtain ⟨v,hv⟩ := c.1.2.1.1
  have ht : (v.1,g*v.2) ∈ c.1.1 := he ▸ Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have heq := c.1.2.1.2 ht hv rfl
  have hg : g * v.2 = v.2 := congrArg Prod.snd heq
  exact mul_right_cancel (hg.trans (one_mul _).symm)

abbrev CellOrbits (S : Shapes G) (n : ℕ) := Orbits (G := G) (A := StageCell G S n)

def cellCoordinates (S : Shapes G) (n : ℕ) : (G × CellOrbits G S n) ≃ StageCell G S n :=
  orbitCoordinates (cellAction_free G S n)

lemma cellCoordinates_apply (S : Shapes G) (n : ℕ) (g : G) (c : CellOrbits G S n) :
    cellCoordinates G S n (g,c) = g • c.out := rfl

instance cellOrbits_finite (S : Shapes G) (n : ℕ) : Finite (CellOrbits G S n) := by
  classical
  obtain ⟨T,hT⟩ := orbitSpan_finite_representatives (basedShapes G S)
  let R : Set (StageCell G S n) := {c | c.1.1 ∈ T}
  have hinj : Function.Injective (fun c : StageCell G S n => c.1.1) := by
    intro c d h; exact Subtype.ext (Subtype.ext h)
  have hR : R.Finite := T.finite_toSet.preimage hinj.injOn
  let := hR.fintype
  apply Finite.of_surjective (fun c : R => (Quotient.mk'' c.1 : CellOrbits G S n))
  intro q
  obtain ⟨s,hs,g,hg⟩ := hT q.out.1.1 q.out.1.2
  let c : StageCell G S n := g⁻¹ • q.out
  have hc : c ∈ R := by
    change translate g⁻¹ q.out.1.1 ∈ T
    rw [hg,translate_mul,inv_mul_cancel,translate_one]
    exact hs
  refine ⟨⟨c,hc⟩,?_⟩
  exact (orbit_mk_smul g⁻¹ q.out).trans (Quotient.out_eq' _)

lemma stage_smul_support (S : Shapes G) (g : G) (x : Stage G S) :
    (g • x).1.support = translate g x.1.support :=
  Finsupp.mapDomain_support_of_injective (vertexTranslate_injective G g) _

lemma stage_openCell (S : Shapes G) (n : ℕ) (c : StageCell G S n) :
    RelCWComplex.openCell (C := (univ : Set (Stage G S))) n c = {x : Stage G S | x.1.support = c.1.1} :=
  Simplicial.characteristicPE_open _ _

lemma stage_closedCell (S : Shapes G) (n : ℕ) (c : StageCell G S n) :
    RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n c = {x : Stage G S | x.1.support ⊆ c.1.1} := by
  change Simplicial.characteristicPE _ c '' closedBall 0 1 = _
  rw [Simplicial.characteristicPE_closed,Simplicial.range_faceMap]

lemma stage_openCell_smul (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (fun x : Stage G S => g • x) '' RelCWComplex.openCell (C := (univ : Set (Stage G S))) n c = RelCWComplex.openCell (C := (univ : Set (Stage G S))) n (g • c) := by
  rw [stage_openCell,stage_openCell]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (g • y).1.support = (g • c).1.1
    rw [stage_smul_support,cell_smul_val,hy]
  · intro hx
    refine ⟨g⁻¹ • x,?_,smul_inv_smul _ _⟩
    change (g⁻¹ • x).1.support = c.1.1
    change x.1.support = translate g c.1.1 at hx
    rw [stage_smul_support,hx,translate_mul,inv_mul_cancel,translate_one]

lemma stage_closedCell_smul (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (fun x : Stage G S => g • x) '' RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n c = RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n (g • c) := by
  rw [stage_closedCell,stage_closedCell]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (g • y).1.support ⊆ (g • c).1.1
    rw [stage_smul_support,cell_smul_val]
    exact translate_mono _ hy
  · intro hx
    refine ⟨g⁻¹ • x,?_,smul_inv_smul _ _⟩
    change (g⁻¹ • x).1.support ⊆ c.1.1
    rw [stage_smul_support]
    have h := translate_mono g⁻¹ hx
    simpa only [cell_smul_val,translate_mul,inv_mul_cancel,translate_one] using h

@[instance_reducible]
def stageEquivariantCW (S : Shapes G) : CWComplex (univ : Set (Stage G S)) :=
  Cellular.actionCW (cellCoordinates G S)
    (fun n g i => by
      change (fun x : Stage G S => g • x) '' RelCWComplex.openCell (C := (univ : Set (Stage G S))) n ((1:G) • i.out) = RelCWComplex.openCell (C := (univ : Set (Stage G S))) n (g • i.out)
      rw [one_smul]
      exact stage_openCell_smul G S n g i.out)
    (fun n g i => by
      change (fun x : Stage G S => g • x) '' RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n ((1:G) • i.out) = RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n (g • i.out)
      rw [one_smul]
      exact stage_closedCell_smul G S n g i.out)

end GroupRingTopology.Milnor

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology

namespace GroupRingTopology.Cellular

section
open Set Metric Topology
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

/-- The actual attaching maps of a classical CW skeleton. -/
def skeletonBoundary (n : ℕ) (i : RelCWComplex.cell C n) :
    C(Attachment.Sphere n,Skeleton C n) :=
  ⟨fun x => ⟨characteristic n i (boundary n x),sphere_mem_skeleton n i x⟩,
    ((characteristic n i).continuous.comp (continuous_boundary n)).subtype_mk _⟩

def skeletonBase (n : ℕ) : C(Skeleton C n,Skeleton C (n+1)) :=
  ⟨fun x => ⟨x.1,skeleton_mono (Nat.le_succ n) x.2⟩,continuous_subtype_val.subtype_mk _⟩

def skeletonCell (n : ℕ) (i : RelCWComplex.cell C n) :
    C(Attachment.Disk n,Skeleton C (n+1)) :=
  ⟨fun x => ⟨characteristic n i x,characteristic_mem_skeleton (Nat.lt_succ_self n) i x⟩,
    (characteristic n i).continuous.subtype_mk _⟩

def skeletonAssembly (n : ℕ) : C(Attachment.Space (skeletonBoundary (C := C) n),Skeleton C (n+1)) :=
  Attachment.lift _ (skeletonBase n) (skeletonCell n) (fun _ _ => rfl)

lemma skeletonAssembly_base (n : ℕ) (x : Skeleton C n) :
    skeletonAssembly n (Attachment.base _ x) = skeletonBase n x :=
  Attachment.lift_base _ _ _ _ x

lemma skeletonAssembly_cell (n : ℕ) (i : RelCWComplex.cell C n) (x : Disk n) :
    skeletonAssembly n (Attachment.cell _ i x) = skeletonCell n i x :=
  Attachment.lift_cell _ _ _ _ i x

lemma skeletonAssembly_interior (n : ℕ) (i : RelCWComplex.cell C n) (x : Attachment.OpenDisk n) :
    skeletonAssembly n (Sum.inr ⟨i,x⟩) = skeletonCell n i (Attachment.interior n x) := by
  rw [← Attachment.cell_interior (skeletonBoundary n) i x,skeletonAssembly_cell]

lemma skeletonAssembly_injective (n : ℕ) : Function.Injective (skeletonAssembly (C := C) n) := by
  intro a b hab
  rcases a with a|⟨i,a⟩ <;> rcases b with b|⟨j,b⟩
  · change skeletonAssembly n (Attachment.base _ a) = skeletonAssembly n (Attachment.base _ b) at hab
    rw [skeletonAssembly_base,skeletonAssembly_base] at hab
    exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : Skeleton C (n+1) => z.1) hab))
  · have hh := congrArg Subtype.val hab
    rw [← show Attachment.base (skeletonBoundary n) a = Sum.inl a from rfl,
      skeletonAssembly_base,skeletonAssembly_interior] at hh
    have hm : a.1 ∈ CWComplex.openCell n j := ⟨b.1,b.2,hh.symm⟩
    exact False.elim (openCell_not_skeleton n j hm a.2)
  · have hh := congrArg Subtype.val hab
    rw [skeletonAssembly_interior,
      ← show Attachment.base (skeletonBoundary n) b = Sum.inl b from rfl,
      skeletonAssembly_base] at hh
    have hm : b.1 ∈ CWComplex.openCell n i := ⟨a.1,a.2,hh⟩
    exact False.elim (openCell_not_skeleton n i hm b.2)
  · have hh := congrArg Subtype.val hab
    rw [skeletonAssembly_interior,skeletonAssembly_interior] at hh
    have hij : i = j := by
      by_contra hne
      have hd := CWComplex.disjoint_openCell_of_ne (C := C) (i := i) (j := j)
        (fun h => hne (sigma_mk_injective h))
      exact Set.disjoint_left.mp hd ⟨a.1,a.2,rfl⟩ ⟨b.1,b.2,hh.symm⟩
    subst j
    have he : a = b := Subtype.ext ((RelCWComplex.map n i).injOn
      (by simpa only [RelCWComplex.source_eq] using a.2)
      (by simpa only [RelCWComplex.source_eq] using b.2) hh)
    subst b; rfl

lemma skeletonAssembly_surjective (n : ℕ) : Function.Surjective (skeletonAssembly (C := C) n) := by
  intro x
  have hx := x.2
  have heq : Skeleton C (n+1) = Skeleton C n ∪
      ⋃ i : RelCWComplex.cell C n,CWComplex.closedCell n i := by
    simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
      (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
  have hx' := (congrArg (fun S : Set X => x.1 ∈ S) heq).mp hx
  rcases hx' with hx|hx
  · exact ⟨Attachment.base _ ⟨x.1,hx⟩,skeletonAssembly_base n _⟩
  · obtain ⟨i,y,hy,he⟩ := Set.mem_iUnion.mp hx
    refine ⟨Attachment.cell _ i ⟨y,hy⟩,?_⟩
    rw [skeletonAssembly_cell]
    exact Subtype.ext he

lemma skeletonAssembly_closed (n : ℕ) : IsClosedMap (skeletonAssembly (C := C) n) := by
  intro S hS
  let e : Attachment.Space (skeletonBoundary (C := C) n) → X :=
    fun x => (skeletonAssembly n x).1
  have hei : Function.Injective e := Subtype.val_injective.comp (skeletonAssembly_injective n)
  have hclosed : IsClosed (e '' S) := by
    apply (CWComplex.closed (Skeleton C (n+1)) _ ?_).mpr
    · intro m j
      have hm : m < n+1 := by
        have hh : (m : ℕ∞) < ((n+1 : ℕ) : ℕ∞) := by
          simpa only [RelCWComplex.skeletonLT_I,Set.mem_ofPred_eq] using j.2
        exact_mod_cast hh
      have hu : ∃ u : C(Disk m,Attachment.Space (skeletonBoundary (C := C) n)),
          ∀ x, e (u x) = characteristic m j.1 x := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm|hm
        · refine ⟨⟨fun x => Attachment.base _
            ⟨characteristic m j.1 x,characteristic_mem_skeleton hm j.1 x⟩,
            (Attachment.continuous_base _).comp ((characteristic m j.1).continuous.subtype_mk _)⟩,?_⟩
          intro x; exact congrArg Subtype.val (skeletonAssembly_base n _)
        · subst m
          exact ⟨Attachment.cell _ j.1,fun x => congrArg Subtype.val (skeletonAssembly_cell n j.1 x)⟩
      obtain ⟨u,hu⟩ := hu
      have heq : (e '' S) ∩ CWComplex.closedCell m j =
          characteristic m j.1 '' (u ⁻¹' S) := by
        ext x
        constructor
        · rintro ⟨⟨y,hy,rfl⟩,z,hz,he⟩
          refine ⟨⟨z,hz⟩,?_,he⟩
          change u ⟨z,hz⟩ ∈ S
          have hh : u ⟨z,hz⟩ = y := hei ((hu _).trans he)
          rwa [hh]
        · rintro ⟨z,hz,rfl⟩
          exact ⟨⟨u z,hz,hu z⟩,z.1,z.2,rfl⟩
      rw [heq]
      exact ((hS.preimage u.continuous).isCompact.image (characteristic m j.1).continuous).isClosed
    · rintro x ⟨y,hy,rfl⟩
      exact (skeletonAssembly n y).2
  have h : IsClosed ((Subtype.val : Skeleton C (n+1) → X) ⁻¹' (e '' S)) :=
    hclosed.preimage continuous_subtype_val
  convert h using 1
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact ⟨y,hy,rfl⟩
  · rintro ⟨y,hy,he⟩; exact ⟨y,hy,Subtype.ext he⟩

/-- A classical CW skeleton is literally the topological adjunction of the
previous skeleton and its disks, including arbitrary infinite cell families. -/
def skeletonHomeomorph (n : ℕ) :
    Attachment.Space (skeletonBoundary (C := C) n) ≃ₜ Skeleton C (n+1) :=
  (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨(skeletonAssembly n).continuous,skeletonAssembly_closed n,
      skeletonAssembly_injective n,skeletonAssembly_surjective n⟩).homeomorph _
end

section
open Set Metric Topology
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

omit [ContinuousConstSMul G X] in
include hσ in
lemma skeleton_smul_mem (n : ℕ) (g : G) {x : X} (hx : x ∈ Skeleton (univ : Set X) n) :
    g • x ∈ Skeleton (univ : Set X) n := by
  obtain ⟨m,hm,j,y,hy,rfl⟩ := (CWComplex.mem_skeletonLT_iff (C := (univ : Set X))).mp hx
  let i := (σ m).symm j
  have hj : σ m i = j := (σ m).apply_symm_apply j
  apply (CWComplex.mem_skeletonLT_iff (C := (univ : Set X))).mpr
  refine ⟨m,hm,σ m (g*i.1,i.2),y,hy,?_⟩
  rw [hσ]
  exact congrArg (fun j => g • RelCWComplex.map m j y) hj

def skeletonTranslate (n : ℕ) (g : G) : C(Skeleton (univ : Set X) n,Skeleton (univ : Set X) n) :=
  ⟨fun x => ⟨g • x.1,skeleton_smul_mem σ hσ n g x.2⟩,
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

lemma skeletonTranslate_base (n : ℕ) (g : G) (x : Skeleton (univ : Set X) n) :
    skeletonTranslate σ hσ (n+1) g (skeletonBase n x) =
      skeletonBase n (skeletonTranslate σ hσ n g x) := rfl

lemma skeletonTranslate_cell (n : ℕ) (g h : G) (i : ι n) (x : Disk n) :
    skeletonTranslate σ hσ (n+1) g (skeletonCell n (σ n (h,i)) x) =
      skeletonCell n (σ n (g*h,i)) x := by
  apply Subtype.ext
  exact (hσ n g h i x.1).symm

variable {E : Type u} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]

lemma exists_equivariant_skeleton_extension (n : ℕ)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hfill : ∀ a : C(Sphere n,E), ∃ d : C(Disk n,E), ∀ x, d (boundary n x) = a x) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  let a (i : ι n) := b.comp (skeletonBoundary n (σ n (1,i)))
  choose d hd using fun i => hfill (a i)
  let D (j : RelCWComplex.cell (univ : Set X) n) : C(Disk n,E) :=
    ⟨fun x => ((σ n).symm j).1 • d ((σ n).symm j).2 x,
      (continuous_const_smul _).comp (d _).continuous⟩
  have hD (j : RelCWComplex.cell (univ : Set X) n) (x : Sphere n) :
      D j (boundary n x) = b (skeletonBoundary n j x) := by
    obtain ⟨⟨g,i⟩,rfl⟩ := (σ n).surjective j
    change ((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 (boundary n x) = _
    rw [Equiv.symm_apply_apply,hd]
    change g • b (skeletonBoundary n (σ n (1,i)) x) = _
    rw [←hb]
    congr 1
    apply Subtype.ext
    exact (hσ n g 1 i x.1).symm.trans (by rw [mul_one]; rfl)
  let f := Attachment.lift (skeletonBoundary (C := (univ : Set X)) n) b D hD
  let e : C(Skeleton (univ : Set X) (n+1),E) := f.comp ⟨(skeletonHomeomorph n).symm,(skeletonHomeomorph n).symm.continuous⟩
  have he_base (x : Skeleton (univ : Set X) n) : e (skeletonBase n x) = b x := by
    change f ((skeletonHomeomorph n).symm (skeletonBase n x)) = _
    rw [←skeletonAssembly_base]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.base _ x))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have he_cell (j : RelCWComplex.cell (univ : Set X) n) (x : Disk n) :
      e (skeletonCell n j x) = D j x := by
    change f ((skeletonHomeomorph n).symm (skeletonCell n j x)) = _
    rw [←skeletonAssembly_cell]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.cell _ j x))) = _
    rw [Homeomorph.symm_apply_apply]
    exact Attachment.lift_cell _ _ _ _ _ _
  refine ⟨e,he_base,?_⟩
  intro g x
  obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
  cases y with
  | inl x =>
    change e (skeletonTranslate σ hσ (n+1) g (skeletonBase n x)) = g • e (skeletonBase n x)
    rw [skeletonTranslate_base,he_base,he_base,hb]
  | inr p =>
    obtain ⟨⟨h,i⟩,hj⟩ := (σ n).surjective p.1
    have heq : skeletonAssembly n (Sum.inr p) = skeletonCell n p.1 (Attachment.interior n p.2) := by
      exact skeletonAssembly_interior n p.1 p.2
    rw [heq,←hj,skeletonTranslate_cell,he_cell,he_cell]
    change ((σ n).symm (σ n (g*h,i))).1 • d ((σ n).symm (σ n (g*h,i))).2 _ =
      g • (((σ n).symm (σ n (h,i))).1 • d ((σ n).symm (σ n (h,i))).2 _)
    simp only [Equiv.symm_apply_apply,mul_smul]
end

section
open Set Metric Topology
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]

lemma exists_equivariant_skeleton_lift (n : ℕ) (p : C(E,B))
    (hp : ∀ (g : G) e, p (g • e) = g • p e) (hRLP : DiskRLP p)
    (F : C(Skeleton (univ : Set X) (n+1),B))
    (hF : ∀ (g : G) x, F (skeletonTranslate σ hσ (n+1) g x) = g • F x)
    (b : C(Skeleton (univ : Set X) n,E))
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ n g x) = g • b x)
    (hbF : ∀ x, p (b x) = F (skeletonBase n x)) :
    ∃ e : C(Skeleton (univ : Set X) (n+1),E),
      (∀ x, e (skeletonBase n x) = b x) ∧ (∀ x, p (e x) = F x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
  let a (i : ι n) := b.comp (skeletonBoundary n (σ n (1,i)))
  let c (i : ι n) := F.comp (skeletonCell n (σ n (1,i)))
  have hsq (i : ι n) (x : Sphere n) : p (a i x) = c i (boundary n x) := by
    change p (b (skeletonBoundary n (σ n (1,i)) x)) = F (skeletonCell n (σ n (1,i)) (boundary n x))
    rw [hbF]
    rfl
  choose d hd hf using fun i => hRLP n (a i) (c i) (hsq i)
  let D (j : RelCWComplex.cell (univ : Set X) n) : C(Disk n,E) :=
    ⟨fun x => ((σ n).symm j).1 • d ((σ n).symm j).2 x,
      (continuous_const_smul _).comp (d _).continuous⟩
  have hD (j : RelCWComplex.cell (univ : Set X) n) (x : Sphere n) :
      D j (boundary n x) = b (skeletonBoundary n j x) := by
    obtain ⟨⟨g,i⟩,rfl⟩ := (σ n).surjective j
    change ((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 (boundary n x) = _
    rw [Equiv.symm_apply_apply,hd]
    change g • b (skeletonBoundary n (σ n (1,i)) x) = _
    rw [←hb]
    congr 1
    apply Subtype.ext
    exact (hσ n g 1 i x.1).symm.trans (by rw [mul_one]; rfl)
  let f := Attachment.lift (skeletonBoundary (C := (univ : Set X)) n) b D hD
  let e : C(Skeleton (univ : Set X) (n+1),E) := f.comp ⟨(skeletonHomeomorph n).symm,(skeletonHomeomorph n).symm.continuous⟩
  have he_base (x : Skeleton (univ : Set X) n) : e (skeletonBase n x) = b x := by
    change f ((skeletonHomeomorph n).symm (skeletonBase n x)) = _
    rw [←skeletonAssembly_base]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.base _ x))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have he_cell (j : RelCWComplex.cell (univ : Set X) n) (x : Disk n) :
      e (skeletonCell n j x) = D j x := by
    change f ((skeletonHomeomorph n).symm (skeletonCell n j x)) = _
    rw [←skeletonAssembly_cell]
    change f ((skeletonHomeomorph n).symm ((skeletonHomeomorph n) (Attachment.cell _ j x))) = _
    rw [Homeomorph.symm_apply_apply]
    exact Attachment.lift_cell _ _ _ _ _ _
  have he (g : G) (x : Skeleton (univ : Set X) (n+1)) :
      e (skeletonTranslate σ hσ (n+1) g x) = g • e x := by
    obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
    cases y with
    | inl x =>
      change e (skeletonTranslate σ hσ (n+1) g (skeletonBase n x)) = g • e (skeletonBase n x)
      rw [skeletonTranslate_base,he_base,he_base,hb]
    | inr q =>
      obtain ⟨⟨h,i⟩,hj⟩ := (σ n).surjective q.1
      have heq : skeletonAssembly n (Sum.inr q) = skeletonCell n q.1 (Attachment.interior n q.2) :=
        skeletonAssembly_interior n q.1 q.2
      rw [heq,←hj,skeletonTranslate_cell,he_cell,he_cell]
      change ((σ n).symm (σ n (g*h,i))).1 • d ((σ n).symm (σ n (g*h,i))).2 _ =
        g • (((σ n).symm (σ n (h,i))).1 • d ((σ n).symm (σ n (h,i))).2 _)
      simp only [Equiv.symm_apply_apply,mul_smul]
  refine ⟨e,he_base,?_,he⟩
  intro x
  obtain ⟨y,rfl⟩ := skeletonAssembly_surjective n x
  cases y with
  | inl x =>
    change p (e (skeletonBase n x)) = F (skeletonBase n x)
    rw [he_base,hbF]
  | inr q =>
    rw [skeletonAssembly_interior,he_cell]
    obtain ⟨⟨g,i⟩,hj⟩ := (σ n).surjective q.1
    rw [←hj]
    change p (((σ n).symm (σ n (g,i))).1 • d ((σ n).symm (σ n (g,i))).2 _) = _
    rw [Equiv.symm_apply_apply,hp,hf]
    change g • F (skeletonCell n (σ n (1,i)) _) = _
    rw [←hF,skeletonTranslate_cell,mul_one]
end

open Set Metric Topology
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)
omit [MulAction G X] [ContinuousConstSMul G X] in
lemma isEmpty_skeleton_zero : IsEmpty (Skeleton (univ : Set X) 0) := by
  refine ⟨fun x => ?_⟩
  have hx := x.2
  change x.1 ∈ (CWComplex.skeletonLT (univ : Set X) 0 : Set X) at hx
  rw [CWComplex.skeletonLT_zero_eq_empty] at hx
  exact hx

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]

lemma exists_equivariant_lift_on_skeleton (d : ℕ) (p : C(E,B))
    (hp : ∀ (g : G) e, p (g • e) = g • p e) (hRLP : DiskRLP p)
    (F : C(Skeleton (univ : Set X) d,B))
    (hF : ∀ (g : G) x, F (skeletonTranslate σ hσ d g x) = g • F x) :
    ∃ e : C(Skeleton (univ : Set X) d,E), (∀ x, p (e x) = F x) ∧
      ∀ (g : G) x, e (skeletonTranslate σ hσ d g x) = g • e x := by
  induction d with
  | zero =>
    let := isEmpty_skeleton_zero (X := X)
    exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun x => isEmptyElim x,fun _ x => isEmptyElim x⟩
  | succ d ih =>
    obtain ⟨b,hbF,hb⟩ := ih (F.comp (skeletonBase d)) (fun g x => by
      change F (skeletonBase d (skeletonTranslate σ hσ d g x)) = g • F (skeletonBase d x)
      rw [←skeletonTranslate_base,hF])
    obtain ⟨e,_,heF,he⟩ := exists_equivariant_skeleton_lift σ hσ d p hp hRLP F hF b hb hbF
    exact ⟨e,heF,he⟩

lemma exists_equivariant_map_on_skeleton (d : ℕ)
    (hfill : ∀ n < d, ∀ a : C(Sphere n,E), ∃ e : C(Disk n,E), ∀ x, e (boundary n x) = a x) :
    ∃ e : C(Skeleton (univ : Set X) d,E),
      ∀ (g : G) x, e (skeletonTranslate σ hσ d g x) = g • e x := by
  induction d with
  | zero =>
    let := isEmpty_skeleton_zero (X := X)
    exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun _ x => isEmptyElim x⟩
  | succ d ih =>
    obtain ⟨b,hb⟩ := ih (fun n hn => hfill n (Nat.lt_succ_of_lt hn))
    obtain ⟨e,_,he⟩ := exists_equivariant_skeleton_extension σ hσ d b hb (hfill d (Nat.lt_succ_self d))
    exact ⟨e,he⟩

variable {Y : Type u} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
lemma exists_equivariant_homotopy_on_skeleton (d : ℕ) (hY : SphereFillable Y)
    (a b : C(Skeleton (univ : Set X) d,Y))
    (ha : ∀ (g : G) x, a (skeletonTranslate σ hσ d g x) = g • a x)
    (hb : ∀ (g : G) x, b (skeletonTranslate σ hσ d g x) = g • b x) :
    ∃ H : a.Homotopy b, ∀ (g : G) t x,
      H (t,skeletonTranslate σ hσ d g x) = g • H (t,x) := by
  let F : C(Skeleton (univ : Set X) d,Y × Y) := a.prodMk b
  have hF (g : G) x : F (skeletonTranslate σ hσ d g x) = g • F x := by
    exact Prod.ext (ha g x) (hb g x)
  obtain ⟨e,heF,he⟩ := exists_equivariant_lift_on_skeleton σ hσ d pathEndpoint
    (fun _ _ => rfl) (pathEndpoint_RLP hY) F hF
  let H : a.Homotopy b :=
    { toFun := fun z => e z.2 z.1
      continuous_toFun := e.continuous.comp continuous_snd |>.eval continuous_fst
      map_zero_left := fun x => congrArg Prod.fst (heF x)
      map_one_left := fun x => congrArg Prod.snd (heF x) }
  refine ⟨H,?_⟩
  intro g t x
  exact ContinuousMap.congr_fun (he g x) t

omit [MulAction G X] [ContinuousConstSMul G X] in
def skeletonChart (n m : ℕ) (hm : m < n) (i : RelCWComplex.cell (univ : Set X) m) :
    C(Disk m,Skeleton (univ : Set X) n) :=
  ⟨fun z => ⟨characteristic m i z,characteristic_mem_skeleton hm i z⟩,
    (characteristic m i).continuous.subtype_mk _⟩

lemma skeleton_compact_representatives (n : ℕ) [∀ m,Finite (ι m)] :
    ∃ K : Set (Skeleton (univ : Set X) n), IsCompact K ∧
      ∀ x, ∃ g : G, ∃ y ∈ K, x = skeletonTranslate σ hσ n g y := by
  let K := ⋃ m : Fin n, ⋃ i : ι m, Set.range (skeletonChart n m m.2 (σ m (1,i)))
  have hK : IsCompact K := isCompact_iUnion fun m => isCompact_iUnion fun i =>
    isCompact_range (skeletonChart n m m.2 (σ m (1,i))).continuous
  refine ⟨K,hK,?_⟩
  intro x
  obtain ⟨m,hm,j,z,hz,hj⟩ := (CWComplex.mem_skeletonLT_iff (C := (univ : Set X))).mp x.2
  obtain ⟨⟨g,i⟩,rfl⟩ := (σ m).surjective j
  have hmn : m < n := by exact_mod_cast hm
  let y := skeletonChart n m hmn (σ m (1,i)) ⟨z,ball_subset_closedBall hz⟩
  refine ⟨g,y,Set.mem_iUnion.mpr ⟨⟨m,hmn⟩,Set.mem_iUnion.mpr ⟨i,Set.mem_range_self _⟩⟩,?_⟩
  apply Subtype.ext
  change x.1 = g • RelCWComplex.map m (σ m (1,i)) z
  rw [←hσ,mul_one]
  exact hj.symm
end GroupRingTopology.Cellular

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology

namespace GroupRingTopology.Cellular
open Set Metric Topology
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]
variable {K : Type v} [MetricSpace K] [CompactSpace K]

def skeletonInclusion (n : ℕ) : C(Skeleton C n,X) := ⟨Subtype.val,continuous_subtype_val⟩

/-- One step of the classical cellular approximation theorem, without any
local finiteness assumption on the target CW complex. -/
lemma deform_skeleton_succ (n : ℕ) (f : C(K,Skeleton C (n+1)))
    (hdim : dimH (Set.univ : Set K) < n) :
    ∃ (g : C(K,Skeleton C n))
      (H : f.Homotopy ((skeletonBase n).comp g)),
      ∀ t x, (f x).1 ∈ Skeleton C n → H (t,x) = f x := by
  let e := skeletonHomeomorph (C := C) n
  let : T2Space (Attachment.Space (skeletonBoundary (C := C) n)) := e.symm.t2Space
  let f' : C(K,Attachment.Space (skeletonBoundary (C := C) n)) := (⟨e.symm,e.symm.continuous⟩ : C(_, _)).comp f
  obtain ⟨g,H,hH⟩ := Attachment.exists_deformation_into_base (skeletonBoundary (C := C) n) f' hdim
  have h0 : (⟨e,e.continuous⟩ : C(_, _)).comp f' = f := by apply ContinuousMap.ext; intro x; exact e.apply_symm_apply (f x)
  have h1 : (⟨e,e.continuous⟩ : C(_, _)).comp
      ((⟨Attachment.base _,Attachment.continuous_base _⟩ : C(_, _)).comp g) =
      (skeletonBase n).comp g := by apply ContinuousMap.ext; intro x; exact skeletonAssembly_base n (g x)
  let J := (ContinuousMap.Homotopy.refl (⟨e,e.continuous⟩ : C(_, _))).comp H
  refine ⟨g,J.cast h0 h1,?_⟩
  intro t x hx
  change e (H (t,x)) = f x
  have hr : f' x ∈ Set.range (Attachment.base (skeletonBoundary (C := C) n)) := by
    refine ⟨⟨(f x).1,hx⟩,?_⟩
    apply e.injective
    change skeletonAssembly n (Attachment.base _ _) = e (e.symm (f x))
    rw [skeletonAssembly_base,e.apply_symm_apply]
    rfl
  rw [hH t x hr]
  exact e.apply_symm_apply (f x)

/-- Bounded-skeleton cellular approximation with a stationary relative set:
all points initially in the target skeleton remain fixed. -/
lemma deform_bounded_skeleton (d m : ℕ) (f : C(K,Skeleton C m))
    (hdim : dimH (Set.univ : Set K) < d) :
    ∃ (g : C(K,Skeleton C d))
      (H : ((skeletonInclusion m).comp f).Homotopy ((skeletonInclusion d).comp g)),
      ∀ t x, (f x).1 ∈ Skeleton C d → H (t,x) = (f x).1 := by
  induction m with
  | zero =>
    let g : C(K,Skeleton C d) := ⟨fun x => ⟨(f x).1,skeleton_mono (Nat.zero_le d) (f x).2⟩,
      f.continuous.subtype_val.subtype_mk _⟩
    exact ⟨g,.refl _,fun _ _ _ => rfl⟩
  | succ m ih =>
    by_cases hmd : m+1 ≤ d
    · let g : C(K,Skeleton C d) := ⟨fun x => ⟨(f x).1,skeleton_mono hmd (f x).2⟩,
        f.continuous.subtype_val.subtype_mk _⟩
      exact ⟨g,.refl _,fun _ _ _ => rfl⟩
    · have hdm : d ≤ m := by omega
      obtain ⟨g,H,hH⟩ := deform_skeleton_succ m f (hdim.trans_le (by exact_mod_cast hdm))
      obtain ⟨g',J,hJ⟩ := ih g
      let H' := (ContinuousMap.Homotopy.refl (skeletonInclusion (C := C) (m+1))).comp H
      refine ⟨g',H'.trans J,?_⟩
      intro t x hx
      have hh (s : unitInterval) : H' (s,x) = (f x).1 := by
        exact congrArg Subtype.val (hH s x (skeleton_mono hdm hx))
      have hg : (g x).1 = (f x).1 := by
        have he := hh 1
        rw [ContinuousMap.Homotopy.apply_one] at he
        exact he
      have hj (s : unitInterval) : J (s,x) = (f x).1 := by
        rw [hJ s x (hg.symm ▸ hx),hg]
      erw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact hh _
      · exact hj _

/-- Cellular approximation for arbitrary compact finite-Hausdorff-dimensional
sources. Compactness bounds the traversed dimensions, not the number of cells
of the whole CW complex. -/
theorem exists_cellular_approximation (d : ℕ) (f : C(K,X)) (hf : ∀ x,f x ∈ C)
    (hdim : dimH (Set.univ : Set K) < d) :
    ∃ (g : C(K,Skeleton C d)) (H : f.Homotopy ((skeletonInclusion d).comp g)),
      ∀ t x, f x ∈ Skeleton C d → H (t,x) = f x := by
  obtain ⟨m,hm⟩ := compactMap_bounded_skeleton f hf
  let f' : C(K,Skeleton C m) := ⟨fun x => ⟨f x,hm x⟩,f.continuous.subtype_mk _⟩
  exact deform_bounded_skeleton d m f' hdim
end GroupRingTopology.Cellular
namespace GroupRingTopology.SphereTopology
open Set Metric Topology
variable {Y : Type u} [TopologicalSpace Y]
lemma fill_zero [Nonempty Y] (a : C(Cellular.Sphere 0,Y)) :
    ∃ e : C(Cellular.Disk 0,Y), ∀ x, e (Cellular.boundary 0 x) = a x := by
  refine ⟨.const _ (Classical.choice ‹Nonempty Y›),?_⟩
  intro x
  have hx := x.2
  have hz : x.1 = 0 := Subsingleton.elim _ _
  simp only [hz,mem_sphere,dist_self] at hx
  exact False.elim (zero_ne_one hx)
lemma fill_one [PathConnectedSpace Y] (a : C(Cellular.Sphere 1,Y)) :
    ∃ e : C(Cellular.Disk 1,Y), ∀ x, e (Cellular.boundary 1 x) = a x := by
  let p := (PathConnectedSpace.joined (a Cayley.minus) (a Cayley.plus)).somePath
  let e : C(Cellular.Disk 1,Y) := p.toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩
  refine ⟨e,?_⟩
  intro x
  obtain rfl|rfl := Cayley.sphere_one_eq x
  · change p (Cayley.edgeTime (Attachment.boundary 1 Cayley.minus)) = _
    rw [Cayley.edgeTime_minus,p.source]
  · change p (Cayley.edgeTime (Attachment.boundary 1 Cayley.plus)) = _
    rw [Cayley.edgeTime_plus,p.target]
end GroupRingTopology.SphereTopology
namespace GroupRingTopology.Cellular
open Set Metric Topology
variable {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]

/-- A ghost map in one geometric degree, including unbased spheres. -/
def KillsSpheres (q : C(Y,Z)) (n : ℕ) : Prop :=
  ∀ a : C(Sphere n,Y), ∃ F : C(Disk n,Z), ∀ x, F (boundary n x) = q (a x)

lemma cylinder_filling_after {n : ℕ} (q : C(Y,Z)) (hq : KillsSpheres q (n+1))
    (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x, pathEndpoint (a x) = b (boundary n x)) :
    ∃ e : C(Disk n,C(unitInterval,Z)),
      (∀ x t, e (boundary n x) t = q (a x t)) ∧
      ∀ x, pathEndpoint (e x) = (q (b x).1,q (b x).2) := by
  obtain ⟨F,hF⟩ := hq (cylinderBoundaryMap a b h)
  let e : C(Disk n,C(unitInterval,Z)) :=
    (F.comp ⟨fun p : Disk n × unitInterval => diskCons p.1 p.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = q (a x t)
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change q (a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t))) = q (a x t)
    rw [diskTime_cons]
    congr 2
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = q (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 0))).1 = q (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = q (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 1))).2 = q (b x).2
      rw [diskTail_cons]

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

structure PartialHomotopy (f g : C(X,Y)) (n : ℕ) where
  val : X → C(unitInterval,Y)
  continuousOn : ContinuousOn val (Skeleton C n)
  zero : ∀ x ∈ Skeleton C n, val x 0 = f x
  one : ∀ x ∈ Skeleton C n, val x 1 = g x

namespace PartialHomotopy
variable {f g : C(X,Y)} {n : ℕ}

def onSphere (a : PartialHomotopy (C := C) f g n) (i : RelCWComplex.cell C n) :
    C(Sphere n,C(unitInterval,Y)) :=
  ⟨fun x => a.val (characteristic n i (boundary n x)),
    a.continuousOn.comp_continuous ((characteristic n i).continuous.comp (continuous_boundary n))
      (sphere_mem_skeleton n i)⟩

def endpoints (i : RelCWComplex.cell C n) : C(Disk n,Y × Y) :=
  ⟨fun x => (f (characteristic n i x),g (characteristic n i x)),
    (f.continuous.comp (characteristic n i).continuous).prodMk
      (g.continuous.comp (characteristic n i).continuous)⟩

lemma endpoints_compatible (a : PartialHomotopy (C := C) f g n)
    (i : RelCWComplex.cell C n) (x : Sphere n) :
    pathEndpoint (a.onSphere i x) = endpoints (f := f) (g := g) i (boundary n x) :=
  Prod.ext (a.zero _ (sphere_mem_skeleton n i x)) (a.one _ (sphere_mem_skeleton n i x))

lemma cell_extension_after (a : PartialHomotopy (C := C) f g n)
    (q : C(Y,Z)) (hq : KillsSpheres q (n+1)) (i : RelCWComplex.cell C n) :
    ∃ e : C(Disk n,C(unitInterval,Z)),
      (∀ x, e (boundary n x) = q.comp (a.val (characteristic n i (boundary n x)))) ∧
      (∀ x, e x 0 = q (f (characteristic n i x))) ∧
      (∀ x, e x 1 = q (g (characteristic n i x))) := by
  obtain ⟨e,he,hp⟩ := cylinder_filling_after q hq (a.onSphere i) (endpoints i)
    (a.endpoints_compatible i)
  exact ⟨e,fun x => ContinuousMap.ext (he x),fun x => congrArg Prod.fst (hp x),
    fun x => congrArg Prod.snd (hp x)⟩

/-- A single uniform ghost extends every partially constructed homotopy by a
whole CW dimension, even if there are infinitely many cells in that dimension. -/
def next (a : PartialHomotopy (C := C) f g n)
    (q : C(Y,Z)) (hq : KillsSpheres q (n+1)) :
    PartialHomotopy (C := C) (q.comp f) (q.comp g) (n+1) := by
  let e := fun i => (a.cell_extension_after q hq i).choose
  have hb : ∀ i x, e i (boundary n x) =
      q.comp (a.val (characteristic n i (boundary n x))) :=
    fun i => (a.cell_extension_after q hq i).choose_spec.1
  have hz := fun i => (a.cell_extension_after q hq i).choose_spec.2.1
  have ho := fun i => (a.cell_extension_after q hq i).choose_spec.2.2
  let v : X → C(unitInterval,Z) := fun x => q.comp (a.val x)
  have hv : ContinuousOn v (Skeleton C n) :=
    (ContinuousMap.continuous_postcomp q).comp_continuousOn a.continuousOn
  refine ⟨attachValue v e,attachValue_continuous v hv e hb,?_,?_⟩
  all_goals
    intro x hx
    have heq : Skeleton C (n+1) = Skeleton C n ∪
        ⋃ i : RelCWComplex.cell C n, CWComplex.closedCell n i := by
      simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
        (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
    rw [heq] at hx
    rcases hx with hx | hx
    · rw [attachValue_old v e hx]
      first
      | exact congrArg q (a.zero x hx)
      | exact congrArg q (a.one x hx)
    · obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
      rw [show RelCWComplex.map n i y = characteristic n i ⟨y,hy⟩ from rfl,
        attachValue_characteristic v e hb]
      first | exact hz i ⟨y,hy⟩ | exact ho i ⟨y,hy⟩

def start (f g : C(X,Y)) : PartialHomotopy (C := C) f g 0 where
  val := fun x => ContinuousMap.const _ (f x)
  continuousOn := by
    rw [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty]
    exact continuousOn_empty _
  zero := by intro x _; rfl
  one := by
    intro x hx
    simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx

/-- On a whole finite-dimensional complex the final partial homotopy is an
ordinary continuous homotopy, not merely cellwise data. -/
def toHomotopy [CWComplex (Set.univ : Set X)] (a : PartialHomotopy (C := (Set.univ : Set X)) f g n)
    (hdim : Skeleton (Set.univ : Set X) n = Set.univ) : f.Homotopy g where
  toFun p := a.val p.2 p.1
  continuous_toFun := by
    have hv : Continuous a.val := by
      have hh := a.continuousOn
      rw [hdim] at hh
      exact continuousOn_univ.mp hh
    exact continuous_eval.comp ((hv.comp continuous_snd).prodMk continuous_fst)
  map_zero_left x := a.zero x (hdim.symm ▸ Set.mem_univ x)
  map_one_left x := a.one x (hdim.symm ▸ Set.mem_univ x)

end PartialHomotopy
end GroupRingTopology.Cellular

namespace TorsionFreeZeroDivisors.FiniteDimensionalCW
open Set Metric Topology GroupRingTopology GroupRingTopology.Cellular
variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]
/-- No higher cells really means that the indicated finite skeleton is the
whole space; no replacement by homology or a resolution is involved. -/
lemma skeleton_eq_univ (N : ℕ)
    (hdim : ∀ m : ℕ, N ≤ m → IsEmpty (RelCWComplex.cell (Set.univ : Set X) m)) :
    Skeleton (Set.univ : Set X) N=Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hx : x ∈ ⋃m,⋃i : RelCWComplex.cell (Set.univ : Set X) m,CWComplex.openCell m i := by
    rw [CWComplex.iUnion_openCell_eq_complex]
    trivial
  obtain ⟨m,hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  have hm : m<N := by
    by_contra h
    exact (hdim m (by omega)).false i
  exact CWComplex.mem_skeletonLT_iff.mpr ⟨m,by exact_mod_cast hm,i,hi⟩

/-- A two-dimensional CW contraction uses only fillings of circles and
2-spheres: extend the contraction over actual 0-, 1-, and 2-cells. This is the
needed special case of Whitehead, proved directly using cellular homotopy
extension from the supplied checked support. -/
theorem contractible_of_two_dimensional_fills [PathConnectedSpace X]
    (hdim : ∀ m : ℕ, 2 < m → IsEmpty (RelCWComplex.cell (Set.univ : Set X) m))
    (hcircle : ∀ a : C(SphereTopology.Sphere 2,X),SphereTopology.Extends a)
    (hsphere : ∀ a : C(SphereTopology.Sphere 3,X),SphereTopology.Extends a) :
    ContractibleSpace X := by
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let f : C(X,X) := ContinuousMap.id X
  let g : C(X,X) := ContinuousMap.const X x₀
  have h1 : KillsSpheres (ContinuousMap.id X) 1 := fun a=>SphereTopology.fill_one a
  have h2 : KillsSpheres (ContinuousMap.id X) 2 := by
    intro a
    obtain ⟨F,hF⟩ := hcircle a
    exact ⟨F,fun x=>ContinuousMap.congr_fun hF x⟩
  have h3 : KillsSpheres (ContinuousMap.id X) 3 := by
    intro a
    obtain ⟨F,hF⟩ := hsphere a
    exact ⟨F,fun x=>ContinuousMap.congr_fun hF x⟩
  let A := PartialHomotopy.start (C:=Set.univ) f g
  let B := A.next (ContinuousMap.id X) h1
  let C := B.next (ContinuousMap.id X) h2
  let D := C.next (ContinuousMap.id X) h3
  have hsk : Skeleton (Set.univ : Set X) 3=Set.univ :=
    skeleton_eq_univ 3 (fun m hm=>hdim m (by omega))
  have H : f.Homotopy g := D.toHomotopy hsk
  exact (contractible_iff_id_nullhomotopic X).mpr ⟨x₀,⟨H⟩⟩
end TorsionFreeZeroDivisors.FiniteDimensionalCW

namespace TorsionFreeZeroDivisors.PresentationTopology
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
variable {G S : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]

def pointCover : C(G,PUnit) := .const _ PUnit.unit
lemma pointCover_quotient : IsQuotientCoveringMap (pointCover (G := G)) G where
  __ := show IsQuotientMap (pointCover (G := G)) from
    (show IsOpenMap (pointCover (G := G)) from fun _ _ => isOpen_discrete _).isQuotientMap
      (by fun_prop) (fun _ => ⟨1,rfl⟩)
  __ := (inferInstance : ContinuousConstSMul G G)
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro _; exact ⟨x*y⁻¹,by simp [smul_eq_mul]⟩
    · intro _; rfl
  disjoint x := by
    refine ⟨{x},(isOpen_discrete _).mem_nhds (Set.mem_singleton x),?_⟩
    rintro g ⟨z,⟨y,hy,rfl⟩,h⟩
    simp only [Set.mem_singleton_iff] at hy h
    rw [hy] at h
    exact mul_right_cancel (show g*x=1*x by simpa only [smul_eq_mul,one_mul] using h)

variable (s : S → G)
def roseAttaching : S → C(Sphere 1,PUnit) := fun i=>(pointCover (G:=G)).comp (Cayley.attaching s i)
abbrev Rose := Space (roseAttaching s)
def graphProjection : C(Cayley.Graph s,Rose s) :=
  coverMap (Cayley.attaching s) pointCover pointCover_quotient (roseAttaching s) (fun _ _=>rfl)
lemma graphProjection_quotient : IsQuotientCoveringMap (graphProjection s) G :=
  coverMap_isQuotientCovering _ _ _ _ _
instance roseT2 : T2Space (Rose s) := t2Space _ realSeparated_of_tychonoff
instance roseCW : CWComplex (Set.univ : Set (Rose s)) :=
  layerCW _ Cayley.discrete_dimension
omit [DiscreteTopology G] in
lemma rose_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Rose s)) m) : m<2 :=
  layerCW_dimensions _ Cayley.discrete_dimension m i
omit [DiscreteTopology G] in
lemma rose_finite [Finite S] (m : ℕ) : Finite (RelCWComplex.cell (Set.univ : Set (Rose s)) m) := by
  apply layerCW_finite_cells
  intro n
  cases n with
  | zero => change Finite (Set.univ : Set PUnit); infer_instance
  | succ n => change Finite PEmpty; infer_instance
instance rosePathConnected : PathConnectedSpace (Rose s) := by
  let := SphereTopology.sphere_nonempty 0
  exact Attachment.pathConnectedSpace _

variable (rels : Set (FreeGroup S)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r=1)
def diskAttaching : rels → C(Sphere 2,Rose s) := fun r=>
  (graphProjection s).comp (Cayley.relatorAttaching s rels hrel r)
abbrev Base := Space (diskAttaching s rels hrel)
def projection : C(Cayley.PresentationCover s rels hrel,Base s rels hrel) :=
  coverMap (Cayley.relatorAttaching s rels hrel) (graphProjection s)
    (graphProjection_quotient s) (diskAttaching s rels hrel) (fun _ _=>rfl)
lemma projection_quotient : IsQuotientCoveringMap (projection s rels hrel) G :=
  coverMap_isQuotientCovering _ _ _ _ _
instance baseT2 : T2Space (Base s rels hrel) :=
  t2Space _ (realSeparated _ realSeparated_of_tychonoff)
instance baseCW : CWComplex (Set.univ : Set (Base s rels hrel)) :=
  layerCW _ (rose_dimension s)
lemma base_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Base s rels hrel)) m) : m<3 :=
  layerCW_dimensions _ (rose_dimension s) m i
lemma base_no_higher (m : ℕ) (hm : 2 < m) :
    IsEmpty (RelCWComplex.cell (Set.univ : Set (Base s rels hrel)) m) :=
  ⟨fun i=>by have := base_dimension s rels hrel m i; omega⟩
lemma base_finite [Finite S] [Finite rels] : CWComplex.Finite (Set.univ : Set (Base s rels hrel)) where
  eventually_isEmpty_cell := Filter.eventually_atTop.mpr ⟨3,fun m hm=>base_no_higher s rels hrel m (by omega)⟩
  finite_cell m := layerCW_finite_cells _ (rose_finite s) (rose_dimension s) m
lemma base_two_cell (hr : rels.Nonempty) :
    Nonempty (RelCWComplex.cell (Set.univ : Set (Base s rels hrel)) 2) := by
  obtain ⟨r,hr⟩ := hr
  exact ⟨Sum.inr ⟨⟨⟨rfl⟩,⟨r,hr⟩⟩⟩⟩
instance basePathConnected : PathConnectedSpace (Base s rels hrel) := by
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _
def coverPoint : Cayley.PresentationCover s rels hrel :=
  Cayley.presentationBase s rels hrel (Cayley.vertex s 1)
def basePoint : Base s rels hrel := projection s rels hrel (coverPoint s rels hrel)
lemma cover_no_higher (m : ℕ) (hm : 2 < m) :
    IsEmpty (RelCWComplex.cell (Set.univ : Set (Cayley.PresentationCover s rels hrel)) m) := by
  refine ⟨fun i=>?_⟩
  have := layerCW_dimensions (equivariantFamily (G:=G) (Cayley.relatorAttaching s rels hrel))
    (Cayley.graph_dimension s) m i
  omega

variable (hs : Function.Surjective (FreeGroup.lift s))
  (hker : (FreeGroup.lift s).ker=Subgroup.normalClosure rels)
def fundamentalEquiv : G ≃* FundamentalGroup (Base s rels hrel) (basePoint s rels hrel) := by
  let := Cayley.presentationCover_simplyConnected s rels hrel hs hker
  exact (MulEquiv.inv' G).trans
    ((projection_quotient s rels hrel).fundamentalGroupEquiv
      ⟨coverPoint s rels hrel,rfl⟩).symm

include hs hker in
lemma contractible_cover
    (hfill : ∀ a : C(Sphere 3,Cayley.PresentationCover s rels hrel),SphereTopology.Extends a) :
    ContractibleSpace (Cayley.PresentationCover s rels hrel) := by
  let := Cayley.presentationCover_pathConnected s rels hrel hs
  exact FiniteDimensionalCW.contractible_of_two_dimensional_fills
    (cover_no_higher s rels hrel) (Cayley.presentationCover_sphereFill s rels hrel hs hker) hfill

end TorsionFreeZeroDivisors.PresentationTopology

end

end OAI
end


