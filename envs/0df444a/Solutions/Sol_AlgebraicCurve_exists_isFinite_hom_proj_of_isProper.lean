-- Prove2me | solution 1 for AlgebraicCurve.exists_isFinite_hom_proj_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1bd873c3-c7dc-588a-ac40-484220a05fdc

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_isFinite_hom_proj_of_isProper

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "exists_place_range_stalk_eq baseToFunctionField finite_compl_of_isOpen isClosed_singleton_of_ne_genericPoint"
namespace FiniteMapToP1
p2m_open "AlgebraicCurve"

attribute [local instance] MvPolynomial.gradedAlgebra

section target
variable (K : Type u) [Field K]

private abbrev A : Type u := MvPolynomial (Fin 2) K

private abbrev 𝒜 : ℕ → Submodule K (A K) := MvPolynomial.homogeneousSubmodule (Fin 2) K

private abbrev P1 : Scheme.{u} := Proj (𝒜 K)

private lemma X_mem (i : Fin 2) : (MvPolynomial.X i : A K) ∈ 𝒜 K 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X K i)

private scoped instance finiteType_gradeZero : Algebra.FiniteType (𝒜 K 0) (A K) := by
  classical
  refine ⟨⟨{MvPolynomial.X 0, MvPolynomial.X 1}, ?_⟩⟩
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r =>
    have hC : (MvPolynomial.C r : A K) ∈ 𝒜 K 0 :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ r)
    have : (MvPolynomial.C r : A K) = algebraMap (𝒜 K 0) (A K) ⟨_, hC⟩ := rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
    refine Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ?_)
    fin_cases i <;> simp

private def ev0 : 𝒜 K 0 →+* K := MvPolynomial.constantCoeff.comp (algebraMap (𝒜 K 0) (A K))

private lemma ev0_algebraMap (r : K) : ev0 K (algebraMap K (𝒜 K 0) r) = r := by
  simp [ev0, MvPolynomial.algebraMap_eq]

private lemma ev0_surjective : Function.Surjective (ev0 K) := fun r => ⟨_, ev0_algebraMap K r⟩

private def sK : Spec (.of K) ⟶ Spec (.of (𝒜 K 0)) := Spec.map (CommRingCat.ofHom (ev0 K))

private scoped instance : IsClosedImmersion (sK K) := .spec_of_surjective _ (ev0_surjective K)

end target

section curve
variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
  [IsIntegral C] [SmoothOfRelativeDimension 1 c]

private def κ : K →+* C.functionField := (Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ c)).hom

omit [SmoothOfRelativeDimension 1 c] in
private lemma Spec_map_κ : Spec.map (CommRingCat.ofHom (κ c)) = C.fromSpecStalk (genericPoint C) ≫ c := by
  simp [κ]

private def g (f : C.functionField) : A K →+* C.functionField := MvPolynomial.eval₂Hom (κ c) ![1, f]

omit [SmoothOfRelativeDimension 1 c] in
private lemma isUnit_g_X0 (f : C.functionField) : IsUnit (g c f (MvPolynomial.X 0)) := by
  simp [g]

private def ψ (f : C.functionField) : HomogeneousLocalization.Away (𝒜 K) (MvPolynomial.X 0 : A K) →+*
    C.functionField :=
  (IsLocalization.Away.lift (MvPolynomial.X 0 : A K) (isUnit_g_X0 c f)
      (S := Localization.Away (MvPolynomial.X 0 : A K))).comp
    (algebraMap _ (Localization.Away (MvPolynomial.X 0 : A K)))

private def p (f : C.functionField) : Spec C.functionField ⟶ P1 K :=
  Spec.map (CommRingCat.ofHom (ψ c f)) ≫ Proj.awayι (𝒜 K) (MvPolynomial.X 0) (X_mem K 0) Nat.one_pos

omit [SmoothOfRelativeDimension 1 c] in

private lemma p_toSpecZero (f : C.functionField) :
    p c f ≫ Proj.toSpecZero (𝒜 K) = C.fromSpecStalk (genericPoint C) ≫ c ≫ sK K := by

  have key : (ψ c f).comp (HomogeneousLocalization.fromZeroRingHom (𝒜 K) _) =
      (κ c).comp (ev0 K) := by
    ext a
    have hh : MvPolynomial.IsHomogeneous (a : A K) 0 :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mp a.2
    have htd : (a : A K).totalDegree = 0 := by
      by_cases h0 : (a : A K) = 0
      · simp [h0]
      · exact hh.totalDegree h0
    have ha : (a : A K) = MvPolynomial.C (MvPolynomial.coeff 0 (a : A K)) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
    have hval : (HomogeneousLocalization.fromZeroRingHom (𝒜 K) (Submonoid.powers (MvPolynomial.X 0))
        a).val = algebraMap (A K) (Localization.Away (MvPolynomial.X 0 : A K)) (a : A K) := by
      simp only [HomogeneousLocalization.fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, HomogeneousLocalization.val_mk]
      exact Localization.mk_one_eq_algebraMap _
    simp only [RingHom.comp_apply]
    change (IsLocalization.Away.lift (MvPolynomial.X 0 : A K) (isUnit_g_X0 c f))
        ((HomogeneousLocalization.fromZeroRingHom (𝒜 K) _ a).val) = κ c (ev0 K a)
    rw [hval, IsLocalization.Away.lift_eq]
    change g c f (a : A K) = κ c (MvPolynomial.constantCoeff (a : A K))
    rw [ha]
    simp [g]
  have hR : C.fromSpecStalk (genericPoint C) ≫ c ≫ sK K =
      Spec.map (CommRingCat.ofHom ((κ c).comp (ev0 K))) := by
    rw [← Category.assoc, ← Spec_map_κ c, sK, ← Spec.map_comp, CommRingCat.ofHom_comp]
  rw [hR, p, Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  simp at key ⊢
  exact key

private def R (f : C.functionField) : C ⤏ P1 K :=
  Scheme.RationalMap.ofFunctionField (c ≫ sK K) (Proj.toSpecZero (𝒜 K)) (p c f)
    (by simpa only [Category.assoc] using p_toSpecZero c f)

include c in

private lemma valuationRing_stalk (x : C) (hx : IsClosed ({x} : Set C)) :
    ValuationRing (C.presheaf.stalk x) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  obtain ⟨v, hv⟩ := AlgebraicCurve.exists_place_range_stalk_eq c x hx
  refine (ValuationRing.iff_isInteger_or_isInteger (R := C.presheaf.stalk x)
    (K := C.functionField)).mpr fun y => ?_
  have key : ∀ z : C.functionField, z ∈ v.toValuationSubring →
      IsLocalization.IsInteger (C.presheaf.stalk x) z := by
    intro z hz
    have hz' : z ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range := by
      rw [hv]; exact hz
    obtain ⟨r, hr⟩ := hz'
    exact RingHom.mem_rangeS.mpr ⟨r, hr⟩
  rcases v.toValuationSubring.mem_or_inv_mem y with h | h
  · exact Or.inl (key y h)
  · exact Or.inr (key _ h)

private lemma mem_domain (f : C.functionField) (x : C) (hx : IsClosed ({x} : Set C)) :
    x ∈ (R c f).domain := by
  haveI := valuationRing_stalk c x hx

  have hspec : Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
      C.fromSpecStalk x = C.fromSpecStalk (genericPoint C) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)

  have hsq := Proj.valuativeCriterion_existence (𝒜 K)
    { R := C.presheaf.stalk x
      commRing := inferInstance
      domain := inferInstance
      valuationRing := inferInstance
      K := C.functionField
      field := inferInstance
      algebra := inferInstance
      isFractionRing := inferInstance
      i₁ := p c f
      i₂ := C.fromSpecStalk x ≫ c ≫ sK K
      commSq := ⟨by rw [p_toSpecZero, ← hspec]; simp only [Category.assoc]; try rfl⟩ }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := hsq.exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫ l =
      p c f := hl₁
  have hl₂' : l ≫ Proj.toSpecZero (𝒜 K) = C.fromSpecStalk x ≫ c ≫ sK K := hl₂

  let gx := Scheme.PartialMap.ofFromSpecStalk (x := x) (c ≫ sK K) (Proj.toSpecZero (𝒜 K))
    (l : Spec (C.presheaf.stalk x) ⟶ P1 K) (by simpa only [Category.assoc] using hl₂')
  have hmem : x ∈ gx.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _

  have hgx : gx.toRationalMap = R c f := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [R, Scheme.RationalMap.fromFunctionField_ofFunctionField,
      Scheme.RationalMap.fromFunctionField_toRationalMap]

    have h1 : gx.fromSpecStalkOfMem hmem = l :=
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
    have h2 : gx.domain.fromSpecStalkOfMem (genericPoint C)
        ((genericPoint_specializes _).mem_open gx.domain.2 gx.dense_domain.nonempty.choose_spec) =
        Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
          gx.domain.fromSpecStalkOfMem x hmem := by
      rw [← cancel_mono gx.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι, hspec]
    change gx.domain.fromSpecStalkOfMem (genericPoint C) _ ≫ gx.hom = p c f
    rw [h2, Category.assoc]
    change Spec.map _ ≫ gx.fromSpecStalkOfMem hmem = p c f
    rw [h1, hl₁']
  rw [← hgx]
  exact gx.le_domain_toRationalMap hmem

private lemma domain_eq_top (f : C.functionField) : (R c f).domain = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  by_cases hx : IsClosed ({x} : Set C)
  · exact mem_domain c f x hx
  · have hgen : x = genericPoint C := by
      by_contra h
      exact hx (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c x h)
    subst hgen
    obtain ⟨y, hy⟩ := (R c f).dense_domain.nonempty
    exact ((genericPoint_spec C).mem_open_set_iff (R c f).domain.isOpen).mpr ⟨y, trivial, hy⟩

private def φ (f : C.functionField) : C ⟶ P1 K :=
  (C.topIso).inv ≫ (C.isoOfEq (domain_eq_top c f)).inv ≫ (R c f).toPartialMap.hom

private lemma ι_φ (f : C.functionField) :
    (R c f).toPartialMap.domain.ι ≫ φ c f = (R c f).toPartialMap.hom := by
  have h2 : ((R c f).toPartialMap.domain.ι ≫ C.topIso.inv) ≫ (C.isoOfEq (domain_eq_top c f)).inv =
      𝟙 _ := by
    rw [← cancel_mono (R c f).domain.ι]
    simp only [Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι, Category.comp_id]
    try rfl
  rw [φ, ← Category.assoc, ← Category.assoc, h2]
  exact Category.id_comp _

private lemma fromSpecStalk_φ (f : C.functionField) :
    C.fromSpecStalk (genericPoint C) ≫ φ c f = p c f := by
  have hη : genericPoint C ∈ (R c f).toPartialMap.domain := by
    rw [show (R c f).toPartialMap.domain = ⊤ from domain_eq_top c f]; trivial
  rw [← Scheme.Opens.fromSpecStalkOfMem_ι _ _ hη, Category.assoc, ι_φ]
  have : (R c f).toPartialMap.fromFunctionField = p c f := by
    rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.toRationalMap_toPartialMap, R,
      Scheme.RationalMap.fromFunctionField_ofFunctionField]
  exact this

private lemma φ_toSpecZero (f : C.functionField) : φ c f ≫ Proj.toSpecZero (𝒜 K) = c ≫ sK K := by
  have : IsDominant (C.fromSpecStalk (genericPoint C)) := ⟨by
    rw [DenseRange, Scheme.range_fromSpecStalk]
    refine Dense.mono (Set.singleton_subset_iff.mpr (specializes_refl (genericPoint C))) ?_
    exact dense_iff_closure_eq.mpr (genericPoint_spec C)⟩
  apply ext_of_isDominant (C.fromSpecStalk (genericPoint C))
  rw [← Category.assoc, fromSpecStalk_φ, p_toSpecZero]

private scoped instance isProper_φ [IsProper c] (f : C.functionField) : IsProper (φ c f) := by
  have : IsProper (φ c f ≫ Proj.toSpecZero (𝒜 K)) := by rw [φ_toSpecZero]; infer_instance
  exact IsProper.of_comp (φ c f) (Proj.toSpecZero (𝒜 K))

include c in

private lemma exists_pole [IsProper c] : ∃ (f : C.functionField) (x : C), IsClosed ({x} : Set C) ∧
    f ∉ (algebraMap (C.presheaf.stalk x) C.functionField).range := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := C))
    isClosed_univ.isLocallyClosed
  rw [mem_closedPoints_iff] at hx
  obtain ⟨v, hv⟩ := AlgebraicCurve.exists_place_range_stalk_eq c x hx
  obtain ⟨f, hf⟩ : ∃ f : C.functionField, f ∉ v.toValuationSubring := by
    by_contra! h
    exact v.ne_top' (eq_top_iff.mpr fun f _ => h f)
  refine ⟨f, x, hx, fun h => hf ?_⟩
  rw [hv] at h
  exact h

private def tX : HomogeneousLocalization.Away (𝒜 K) (MvPolynomial.X 0 : A K) :=
  HomogeneousLocalization.mk ⟨1, ⟨MvPolynomial.X 1, X_mem K 1⟩, ⟨MvPolynomial.X 0, X_mem K 0⟩,
    ⟨1, pow_one _⟩⟩

omit [SmoothOfRelativeDimension 1 c] in
private lemma ψ_tX (f : C.functionField) : ψ c f tX = f := by
  change IsLocalization.Away.lift (MvPolynomial.X 0 : A K) (isUnit_g_X0 c f) (HomogeneousLocalization.val tX) = f
  rw [tX, HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec]
  simp [g]

private lemma φ_genericPoint_mem (f : C.functionField) :
    φ c f (genericPoint C) ∈ Proj.basicOpen (𝒜 K) (MvPolynomial.X 0 : A K) := by
  rw [← Proj.opensRange_awayι (𝒜 K) (MvPolynomial.X 0) (X_mem K 0) Nat.one_pos]
  have : φ c f (genericPoint C) = p c f (IsLocalRing.closedPoint C.functionField) := by
    rw [← fromSpecStalk_φ c f, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  rw [this, p, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

private lemma φ_pole_not_mem (f : C.functionField) (x₀ : C)
    (hf : f ∉ (algebraMap (C.presheaf.stalk x₀) C.functionField).range) :
    φ c f x₀ ∉ Proj.basicOpen (𝒜 K) (MvPolynomial.X 0 : A K) := by
  intro hmem
  set ι₀ := Proj.awayι (𝒜 K) (MvPolynomial.X 0) (X_mem K 0) Nat.one_pos with hι₀
  set lx := C.fromSpecStalk x₀ ≫ φ c f with hlx

  have hrange : Set.range lx ⊆ Set.range ι₀ := by
    rintro _ ⟨z, rfl⟩
    have hz : lx z ⤳ lx (IsLocalRing.closedPoint _) :=
      (IsLocalRing.specializes_closedPoint z).map lx.continuous
    have hcl : lx (IsLocalRing.closedPoint _) = φ c f x₀ := by
      rw [hlx, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
    have hopen : IsOpen (Set.range ι₀) := ι₀.isOpenEmbedding.isOpen_range
    have hmem' : lx (IsLocalRing.closedPoint _) ∈ Set.range ι₀ := by
      rw [hcl, ← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]; exact hmem
    exact hz.mem_open hopen hmem'

  set L := IsOpenImmersion.lift ι₀ lx hrange with hL
  have hLfac : L ≫ ι₀ = lx := IsOpenImmersion.lift_fac _ _ _
  set χ := Spec.preimage L with hχdef
  have hχ : Spec.map χ = L := Spec.map_preimage L

  have hspec : Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x₀) C.functionField)) ≫
      C.fromSpecStalk x₀ = C.fromSpecStalk (genericPoint C) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x₀)
  have hgen : Spec.map (χ ≫ C.presheaf.stalkSpecializes (genericPoint_specializes x₀)) ≫ ι₀ =
      Spec.map (CommRingCat.ofHom (ψ c f)) ≫ ι₀ := by
    rw [Spec.map_comp, Category.assoc, hχ, hLfac, hlx,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, fromSpecStalk_φ, p, hι₀]
    try rfl
  have hring : χ ≫ C.presheaf.stalkSpecializes (genericPoint_specializes x₀) =
      CommRingCat.ofHom (ψ c f) :=
    Spec.map_injective ((cancel_mono ι₀).mp hgen)
  apply hf
  refine ⟨χ.hom tX, ?_⟩
  change (C.presheaf.stalkSpecializes (genericPoint_specializes x₀)).hom (χ.hom tX) = f
  have := congrArg (fun m => CommRingCat.Hom.hom m tX) hring
  simpa [ψ_tX] using this

private lemma finite_fibre [IsProper c] (f : C.functionField) (x₀ : C) (hx₀ : IsClosed ({x₀} : Set C))
    (hf : f ∉ (algebraMap (C.presheaf.stalk x₀) C.functionField).range) (y : P1 K) :
    ((φ c f) ⁻¹' {y}).Finite := by
  by_cases hy : IsClosed ({y} : Set (P1 K))
  ·
    have hcl : IsClosed ((φ c f) ⁻¹' {y}) := hy.preimage (φ c f).continuous
    have hne : ((φ c f) ⁻¹' {y})ᶜ.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
      have h1 : φ c f (genericPoint C) = y := by
        have : genericPoint C ∈ (φ c f) ⁻¹' {y} := h ▸ Set.mem_univ _
        exact this
      have h2 : φ c f x₀ = y := by
        have : x₀ ∈ (φ c f) ⁻¹' {y} := h ▸ Set.mem_univ _
        exact this
      exact φ_pole_not_mem c f x₀ hf (h2 ▸ h1 ▸ φ_genericPoint_mem c f)
    have := AlgebraicCurve.finite_compl_of_isOpen c ⟨((φ c f) ⁻¹' {y})ᶜ, hcl.isOpen_compl⟩ hne
    simpa using this
  ·
    have hx₀' := hx₀
    apply Set.Finite.subset (Set.finite_singleton (genericPoint C))
    intro z hz
    by_contra hzg
    have hzc : IsClosed ({z} : Set C) := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c z hzg
    apply hy
    have : ({y} : Set (P1 K)) = (φ c f) '' {z} := by
      rw [Set.image_singleton]; exact congrArg _ hz.symm
    rw [this]
    exact (φ c f).isClosedMap _ hzc

end curve

end AlgebraicCurve.FiniteMapToP1
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_isFinite_hom_proj_of_isProper.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_isFinite_hom_proj_of_isProper.AlgebraicCurve.FiniteMapToP1"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_isFinite_hom_proj_of_isProper.AlgebraicCurve"

open AlgebraicCurve.FiniteMapToP1 in
theorem solution {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := MvPolynomial.gradedAlgebra (σ := Fin 2) (R := K)
    ∃ φ : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K), IsFinite φ := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin 2) (R := K)
  obtain ⟨f, x₀, hx₀, hf⟩ := exists_pole c
  have : LocallyQuasiFinite (φ c f) := .of_finite_preimage_singleton _ (finite_fibre c f x₀ hx₀ hf)
  exact ⟨φ c f, IsFinite.of_isProper_of_locallyQuasiFinite _⟩

end
end S_AlgebraicCurve_exists_isFinite_hom_proj_of_isProper
end P2MW
export P2MW.S_AlgebraicCurve_exists_isFinite_hom_proj_of_isProper (solution)
