-- Prove2me | solution 1 for AlgebraicGeometry.exists_isFinite_to_proj_of_completeOrthogonalIdempotents
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/77c4cb0b-79f4-5e23-8c7a-94f807c19c60

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isFinite_to_proj_of_completeOrthogonalIdempotents

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry DirectSum HomogeneousIdeal

namespace PiGradedAux

variable {ι' : Type} [Fintype ι'] [DecidableEq ι']
  (A : ι' → Type u) [∀ i, CommRing (A i)] (σ : ι' → Type u) [∀ i, SetLike (σ i) (A i)]
  [∀ i, AddSubgroupClass (σ i) (A i)] (𝒜 : ∀ i, ℕ → σ i) [∀ i, GradedRing (𝒜 i)]

def grading (n : ℕ) : AddSubgroup (Π i, A i) where
  carrier := {a | ∀ i, a i ∈ 𝒜 i n}
  add_mem' ha hb i := add_mem (ha i) (hb i)
  zero_mem' i := zero_mem _
  neg_mem' ha i := neg_mem (ha i)

variable {A σ 𝒜} in
lemma mem_grading {n : ℕ} {a : Π i, A i} : a ∈ grading A σ 𝒜 n ↔ ∀ i, a i ∈ 𝒜 i n := Iff.rfl

lemma single_mem_grading {n : ℕ} (i : ι') {x : A i} (hx : x ∈ 𝒜 i n) :
    Pi.single i x ∈ grading A σ 𝒜 n := by
  intro k
  by_cases h : k = i
  · subst h; simpa using hx
  · simp [Pi.single_eq_of_ne h, zero_mem]

scoped instance : SetLike.GradedMonoid (grading A σ 𝒜) where
  one_mem i := SetLike.one_mem_graded _
  mul_mem _ _ _ _ ha hb k := SetLike.mul_mem_graded (ha k) (hb k)

def singlePiece (i : ι') (n : ℕ) : 𝒜 i n →+ grading A σ 𝒜 n where
  toFun x := ⟨Pi.single i (x : A i), single_mem_grading A σ 𝒜 i x.2⟩
  map_zero' := by ext : 1; simp
  map_add' x y := by ext : 1; simp [Pi.single_add]

@[scoped simp] lemma coe_singlePiece (i : ι') (n : ℕ) (x : 𝒜 i n) :
    (singlePiece A σ 𝒜 i n x : Π i, A i) = Pi.single i (x : A i) := rfl

noncomputable def decomposeAux : (Π i, A i) →+ ⨁ n, grading A σ 𝒜 n :=
  ∑ i, (DirectSum.map (singlePiece A σ 𝒜 i)).comp
    ((decomposeAddEquiv (𝒜 i)).toAddMonoidHom.comp (Pi.evalAddMonoidHom A i))

lemma coe_comp_map_singlePiece (i : ι') :
    (DirectSum.coeAddMonoidHom (grading A σ 𝒜)).comp (DirectSum.map (singlePiece A σ 𝒜 i)) =
      (AddMonoidHom.single A i).comp (DirectSum.coeAddMonoidHom (𝒜 i)) := by
  refine DirectSum.addHom_ext fun n x => ?_
  simp

lemma decomposeAux_apply (a : Π i, A i) :
    decomposeAux A σ 𝒜 a = ∑ i, DirectSum.map (singlePiece A σ 𝒜 i) (decompose (𝒜 i) (a i)) := by
  simp [decomposeAux]

noncomputable scoped instance : GradedRing (grading A σ 𝒜) where
  decompose' := decomposeAux A σ 𝒜
  left_inv a := by
    rw [decomposeAux_apply, map_sum]
    conv_rhs => rw [← Finset.univ_sum_single a]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrArg (fun φ => φ (decompose (𝒜 i) (a i))) (coe_comp_map_singlePiece A σ 𝒜 i)
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.single_apply] at this
    rw [this]
    congr 1
    exact (decompose (𝒜 i)).symm_apply_apply (a i)
  right_inv y := by
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add, hy, hz]
    | of n b =>
      rw [DirectSum.coeAddMonoidHom_of, decomposeAux_apply]
      have : ∀ i, decompose (𝒜 i) ((b : Π i, A i) i) = DirectSum.of _ n ⟨(b : Π i, A i) i, b.2 i⟩ :=
        fun i => decompose_of_mem _ (b.2 i)
      simp_rw [this, DirectSum.map_of, ← map_sum]
      congr 1
      ext : 1
      simp only [AddSubgroup.val_finsetSum, coe_singlePiece]
      exact Finset.univ_sum_single _

def π (k : ι') : grading A σ 𝒜 →+*ᵍ 𝒜 k where
  __ := Pi.evalRingHom A k
  map_mem hx := hx k

@[scoped simp] lemma π_apply (k : ι') (a : Π i, A i) : π A σ 𝒜 k a = a k := rfl

lemma irrelevant_le_map_π (k : ι') :
    HomogeneousIdeal.irrelevant (𝒜 k) ≤
      (HomogeneousIdeal.irrelevant (grading A σ 𝒜)).map (π A σ 𝒜 k) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn x hx
  have hx' : x ∈ 𝒜 k n := by exact hx
  have : x = π A σ 𝒜 k (Pi.single k x) := by simp
  change x ∈ ((HomogeneousIdeal.irrelevant (grading A σ 𝒜)).map (π A σ 𝒜 k)).toIdeal
  rw [HomogeneousIdeal.toIdeal_map, this]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn (single_mem_grading A σ 𝒜 k hx'))

lemma awayMap_π_single_bijective (k : ι') {d : ℕ} (t : A k) (ht : t ∈ 𝒜 k d) :
    Function.Bijective (HomogeneousLocalization.Away.map (π A σ 𝒜 k) (Pi.single k t)) := by
  have hs : Pi.single k t ∈ grading A σ 𝒜 d := single_mem_grading A σ 𝒜 k ht
  have hπs : π A σ 𝒜 k (Pi.single k t) = t := by simp
  constructor
  · intro x y hxy
    rw [← sub_eq_zero] at hxy ⊢
    rw [← map_sub] at hxy
    generalize x - y = z at hxy ⊢
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hs z
    rw [HomogeneousLocalization.Away.map_mk] at hxy
    have hval := congrArg HomogeneousLocalization.val hxy
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hval
    obtain ⟨⟨c, ⟨N, rfl⟩⟩, hc⟩ := hval
    simp only [π_apply] at hc
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨Pi.single k t ^ (N + 1), N + 1, rfl⟩, ?_⟩
    funext j
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    by_cases hj : j = k
    · subst hj
      simp only [Pi.single_eq_same] at hc ⊢
      rw [pow_succ', mul_assoc, hc, mul_zero]
    · simp [Pi.single_eq_of_ne hj]
  · intro y
    obtain ⟨n, b, hb, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective _ ((π A σ 𝒜 k).map_mem hs) y
    refine ⟨HomogeneousLocalization.Away.mk _ hs n (Pi.single k b)
      (single_mem_grading A σ 𝒜 k hb), ?_⟩
    rw [HomogeneousLocalization.Away.map_mk]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
    congr 1
    simp

end PiGradedAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isFinite_to_proj_of_completeOrthogonalIdempotents.PiGradedAux"

namespace PiGradedAux

variable {ι' : Type} [Fintype ι'] [DecidableEq ι']
  (A : ι' → Type u) [∀ i, CommRing (A i)] (σ : ι' → Type u) [∀ i, SetLike (σ i) (A i)]
  [∀ i, AddSubgroupClass (σ i) (A i)] (𝒜 : ∀ i, ℕ → σ i) [∀ i, GradedRing (𝒜 i)]

def ChartIdx : Type u := Σ (j : ι') (d : ℕ+), 𝒜 j (d : ℕ)

def chartFn : ChartIdx A σ 𝒜 → Π i, A i := fun c => Pi.single c.1 (c.2.2 : A c.1)

lemma chartFn_deg (c : ChartIdx A σ 𝒜) : chartFn A σ 𝒜 c ∈ grading A σ 𝒜 (c.2.1 : ℕ) :=
  single_mem_grading A σ 𝒜 c.1 c.2.2.2

lemma irrelevant_le_span_chartFn :
    (HomogeneousIdeal.irrelevant (grading A σ 𝒜)).toIdeal ≤
      Ideal.span (Set.range (chartFn A σ 𝒜)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn a ha
  have ha' : a ∈ grading A σ 𝒜 n := by exact ha
  rw [← Finset.univ_sum_single a]
  refine Submodule.sum_mem _ fun j _ => Ideal.subset_span ⟨⟨j, ⟨n, hn⟩, ⟨a j, ha' j⟩⟩, rfl⟩

noncomputable def chartCover : (Proj (grading A σ 𝒜)).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grading A σ 𝒜) (chartFn A σ 𝒜)
    (m := fun c => (c.2.1 : ℕ)) (chartFn_deg A σ 𝒜) (fun c => c.2.1.pos)
    (irrelevant_le_span_chartFn A σ 𝒜)

noncomputable abbrev incl (k : ι') : Proj (𝒜 k) ⟶ Proj (grading A σ 𝒜) :=
  Proj.map (π A σ 𝒜 k) (irrelevant_le_map_π A σ 𝒜 k)

lemma mem_basicOpen_incl_iff {k : ι'} (q : Proj (𝒜 k)) (a : Π i, A i) :
    incl A σ 𝒜 k q ∈ Proj.basicOpen (grading A σ 𝒜) a ↔ q ∈ Proj.basicOpen (𝒜 k) (a k) := by
  change q ∈ Proj.map (π A σ 𝒜 k) (irrelevant_le_map_π A σ 𝒜 k) ⁻¹ᵁ
    Proj.basicOpen (grading A σ 𝒜) a ↔ _
  rw [Proj.map_preimage_basicOpen]
  rfl

lemma chart_same (k : ι') {d : ℕ} (hd : 0 < d) (t : A k) (ht : t ∈ 𝒜 k d) :
    IsOpenImmersion (pullback.snd (incl A σ 𝒜 k)
      (Proj.awayι (grading A σ 𝒜) (Pi.single k t) (single_mem_grading A σ 𝒜 k ht) hd)) ∧
    Set.range (Proj.awayι (grading A σ 𝒜) (Pi.single k t) (single_mem_grading A σ 𝒜 k ht) hd) ⊆
      Set.range (incl A σ 𝒜 k) := by
  set s : Π i, A i := Pi.single k t with hs_def
  have hs : s ∈ grading A σ 𝒜 d := single_mem_grading A σ 𝒜 k ht
  set F := incl A σ 𝒜 k
  set G := Proj.awayι (grading A σ 𝒜) s hs hd
  have hsq := Proj.awayι_comp_map (π A σ 𝒜 k) (irrelevant_le_map_π A σ 𝒜 k) hd s hs

  set u := pullback.lift (f := F) (g := G) _ _ hsq with hu_def
  have hrange : Set.range (Proj.awayι (𝒜 k) (π A σ 𝒜 k s) ((π A σ 𝒜 k).map_mem hs) hd) =
      Set.range (pullback.fst F G) := by
    rw [IsOpenImmersion.range_pullbackFst, Proj.opensRange_awayι, Proj.map_preimage_basicOpen,
      ← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
  have hu : u = (IsOpenImmersion.isoOfRangeEq _ _ hrange).hom := by
    rw [← cancel_mono (pullback.fst F G), hu_def, pullback.lift_fst,
      IsOpenImmersion.isoOfRangeEq_hom_fac]
  have : IsIso u := hu ▸ inferInstance
  have hbij := awayMap_π_single_bijective A σ 𝒜 k t ht
  have hiso : IsIso (CommRingCat.ofHom (HomogeneousLocalization.Away.map (π A σ 𝒜 k) s)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hsnd : pullback.snd F G =
      inv u ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map (π A σ 𝒜 k) s)) := by
    rw [IsIso.eq_inv_comp, hu_def, pullback.lift_snd]
  refine ⟨by rw [hsnd]; infer_instance, ?_⟩
  rintro _ ⟨y, rfl⟩
  have : IsIso (pullback.snd F G) := by rw [hsnd]; infer_instance
  obtain ⟨z, rfl⟩ := (pullback.snd F G).surjective y
  exact ⟨pullback.fst F G z, by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]⟩

lemma chart_ne {k j : ι'} (hjk : j ≠ k) {d : ℕ} (hd : 0 < d) (t : A j) (ht : t ∈ 𝒜 j d) :
    IsEmpty ↑(pullback (incl A σ 𝒜 k)
      (Proj.awayι (grading A σ 𝒜) (Pi.single j t) (single_mem_grading A σ 𝒜 j ht) hd)) := by
  refine ⟨fun z => ?_⟩
  have hz := Set.mem_range_self (f := ⇑(pullback.fst (incl A σ 𝒜 k)
    (Proj.awayι (grading A σ 𝒜) (Pi.single j t) (single_mem_grading A σ 𝒜 j ht) hd))) z
  rw [IsOpenImmersion.range_pullbackFst, Proj.opensRange_awayι] at hz
  dsimp only [incl] at hz
  rw [Proj.map_preimage_basicOpen] at hz
  simp [Pi.single_eq_of_ne (Ne.symm hjk)] at hz

scoped instance isOpenImmersion_incl (k : ι') : IsOpenImmersion (incl A σ 𝒜 k) := by
  refine IsZariskiLocalAtTarget.of_openCover (chartCover A σ 𝒜).openCover fun c => ?_
  obtain ⟨j, d, t⟩ := c
  change IsOpenImmersion (pullback.snd (incl A σ 𝒜 k)
    (Proj.awayι (grading A σ 𝒜) (Pi.single j (t : A j)) (single_mem_grading A σ 𝒜 j t.2) d.pos))
  by_cases hjk : j = k
  · subst hjk
    exact (chart_same A σ 𝒜 j d.pos t t.2).1
  · have := chart_ne A σ 𝒜 hjk d.pos (t : A j) t.2
    infer_instance

lemma exists_incl_eq (p : Proj (grading A σ 𝒜)) : ∃ k q, incl A σ 𝒜 k q = p := by
  obtain ⟨⟨j, d, t⟩, y, hy⟩ := (chartCover A σ 𝒜).openCover.exists_eq p
  obtain ⟨q, hq⟩ := (chart_same A σ 𝒜 j d.pos t t.2).2 ⟨y, rfl⟩
  exact ⟨j, q, hq.trans hy⟩

lemma eq_of_incl_eq {k l : ι'} (q : Proj (𝒜 k)) (q' : Proj (𝒜 l))
    (h : incl A σ 𝒜 k q = incl A σ 𝒜 l q') : k = l := by
  by_contra hkl
  have hmem : ∀ j, Pi.single j (1 : A j) ∈ (incl A σ 𝒜 k q).asHomogeneousIdeal := by
    intro j
    by_cases hj : j = k
    · subst hj
      have := (mem_basicOpen_incl_iff A σ 𝒜 q' (Pi.single j 1)).not
      rw [← h, Proj.mem_basicOpen, Proj.mem_basicOpen, not_not, not_not] at this
      exact this.mpr (by simp [Pi.single_eq_of_ne (Ne.symm hkl)])
    · have := (mem_basicOpen_incl_iff A σ 𝒜 q (Pi.single j 1)).not
      rw [Proj.mem_basicOpen, Proj.mem_basicOpen, not_not, not_not] at this
      exact this.mpr (by simp [Pi.single_eq_of_ne (Ne.symm hj)])
  have h1 : (incl A σ 𝒜 k q) ∈ Proj.basicOpen (grading A σ 𝒜) 1 := by
    rw [Proj.basicOpen_one]; trivial
  rw [Proj.mem_basicOpen] at h1
  apply h1
  rw [← Finset.univ_sum_single (1 : Π i, A i)]
  exact sum_mem fun j _ => by simpa using hmem j

end PiGradedAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isFinite_to_proj_of_completeOrthogonalIdempotents.PiGradedAux"

open PiGradedAux in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {m : ℕ} (e : Fin m → R)
    (he : CompleteOrthogonalIdempotents e)
    (hfin : ∀ i : Fin m, ∃ (A σ : Type u) (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ)
      (_ : GradedRing 𝒜)
      (ι : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e i))))) ⟶ Proj 𝒜),
      IsFinite ι) :
    ∃ (A σ : Type u) (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ)
      (_ : GradedRing 𝒜) (ι : X ⟶ Proj 𝒜), IsFinite ι := by
  classical
  choose A σ instCR instSL instASG 𝒜 instGR ι hι using hfin
  letI : ∀ i, CommRing (A i) := instCR
  letI : ∀ i, SetLike (σ i) (A i) := instSL
  haveI : ∀ i, AddSubgroupClass (σ i) (A i) := instASG
  letI : ∀ i, GradedRing (𝒜 i) := instGR

  let g : ∀ k : Fin m, Spec (.of (Localization.Away (e k))) ⟶ Spec (.of R) :=
    fun k => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e k))))
  have hrg : ∀ k, Set.range (g k) = (PrimeSpectrum.basicOpen (e k) : Set (PrimeSpectrum R)) :=
    fun k => PrimeSpectrum.localization_away_comap_range (Localization.Away (e k)) (e k)
  have hrU : ∀ k, Set.range (pullback.fst f (g k)) =
      f ⁻¹' (PrimeSpectrum.basicOpen (e k) : Set (PrimeSpectrum R)) := by
    intro k
    rw [IsOpenImmersion.range_pullbackFst, Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange, hrg]
  have hmemU : ∀ k (x : X), x ∈ Set.range (pullback.fst f (g k)) ↔ e k ∉ (f x).asIdeal := by
    intro k x
    rw [hrU]
    rfl
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers (Fin m)
    (fun k => pullback f (g k)) (fun k => pullback.fst f (g k)) (by
      intro x
      have : ∃ k, e k ∉ (f x).asIdeal := by
        by_contra! h
        apply (f x).isPrime.ne_top
        rw [Ideal.eq_top_iff_one, ← he.complete]
        exact Ideal.sum_mem _ fun k _ => h k
      obtain ⟨k, hk⟩ := this
      obtain ⟨y, hy⟩ := (hmemU k x).mpr hk
      exact ⟨k, y, hy⟩)

  let F : ∀ k, pullback f (g k) ⟶ Proj (grading A σ 𝒜) := fun k => ι k ≫ incl A σ 𝒜 k
  have hcompat : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ F k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ F l := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      have : pullback.fst (𝒰.f k) (𝒰.f k) = pullback.snd (𝒰.f k) (𝒰.f k) := by
        rw [← cancel_mono (𝒰.f k)]; exact pullback.condition
      rw [this]
    · have : IsEmpty ↑(pullback (𝒰.f k) (𝒰.f l)) := by
        refine ⟨fun z => ?_⟩
        have h1 : (pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k) z ∈ Set.range (pullback.fst f (g k)) :=
          ⟨pullback.fst (𝒰.f k) (𝒰.f l) z, by rw [Scheme.Hom.comp_apply]; rfl⟩
        have h2 : (pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k) z ∈ Set.range (pullback.fst f (g l)) := by
          rw [pullback.condition]
          exact ⟨pullback.snd (𝒰.f k) (𝒰.f l) z, by rw [Scheme.Hom.comp_apply]; rfl⟩
        rw [hmemU] at h1 h2
        have h0' : e k * e l = 0 := he.ortho hkl
        have h0 : e k * e l ∈ (f ((pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k) z)).asIdeal := by
          rw [h0']; exact Ideal.zero_mem _
        exact h2 (((f _).isPrime.mem_or_mem h0).resolve_left h1)
      exact (isInitialOfIsEmpty).hom_ext _ _
  let γ : X ⟶ Proj (grading A σ 𝒜) := 𝒰.glueMorphisms F hcompat
  have hγ : ∀ k, pullback.fst f (g k) ≫ γ = ι k ≫ incl A σ 𝒜 k :=
    fun k => 𝒰.ι_glueMorphisms F hcompat k

  let 𝒱 : (Proj (grading A σ 𝒜)).OpenCover := Scheme.Cover.mkOfCovers (Fin m)
    (fun k => Proj (𝒜 k)) (fun k => incl A σ 𝒜 k) (exists_incl_eq A σ 𝒜)
  refine ⟨Π i, A i, AddSubgroup (Π i, A i), inferInstance, inferInstance, inferInstance,
    grading A σ 𝒜, inferInstance, γ, ?_⟩
  refine IsZariskiLocalAtTarget.of_openCover 𝒱 fun k => ?_
  change IsFinite (pullback.snd γ (incl A σ 𝒜 k))
  have hrange : Set.range (pullback.fst f (g k)) = Set.range (pullback.fst γ (incl A σ 𝒜 k)) := by
    conv_rhs => rw [IsOpenImmersion.range_pullbackFst, Scheme.Hom.coe_preimage,
      Scheme.Hom.coe_opensRange]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨ι k y, ?_⟩
      change (ι k ≫ incl A σ 𝒜 k) y = (pullback.fst f (g k) ≫ γ) y
      rw [hγ]
    · rintro ⟨q, hq⟩
      obtain ⟨l, y, rfl⟩ := 𝒰.exists_eq x
      have hq' : incl A σ 𝒜 k q = incl A σ 𝒜 l (ι l y) := by
        rw [hq]
        change (pullback.fst f (g l) ≫ γ) y = (ι l ≫ incl A σ 𝒜 l) y
        rw [hγ]
      obtain rfl := eq_of_incl_eq A σ 𝒜 q (ι l y) hq'
      exact ⟨y, rfl⟩
  let eiso := IsOpenImmersion.isoOfRangeEq (pullback.fst f (g k)) (pullback.fst γ (incl A σ 𝒜 k))
    hrange
  have hsnd : eiso.hom ≫ pullback.snd γ (incl A σ 𝒜 k) = ι k := by
    rw [← cancel_mono (incl A σ 𝒜 k), Category.assoc, ← pullback.condition, ← Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac, hγ]
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite eiso.hom, hsnd]
  exact hι k

end S_AlgebraicGeometry_exists_isFinite_to_proj_of_completeOrthogonalIdempotents
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isFinite_to_proj_of_completeOrthogonalIdempotents (solution)
