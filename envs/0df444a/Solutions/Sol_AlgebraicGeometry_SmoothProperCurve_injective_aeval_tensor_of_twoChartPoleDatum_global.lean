-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.injective_aeval_tensor_of_twoChartPoleDatum_global
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2ad05023-304d-5e70-b5b2-c3aba08b956f

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_injective_aeval_tensor_of_twoChartPoleDatum_global

set_option autoImplicit false

universe u

open scoped TensorProduct
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace TRANSCK

theorem zero_or_isUnit_of_not_injective {K D : Type u} [Field K] [CommRing D] [IsDomain D] [Algebra K D]
    (a : D) (h : ¬ Function.Injective (Polynomial.aeval a : K[X] →ₐ[K] D)) : a = 0 ∨ IsUnit a := by
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have : ∃ P : K[X], P ≠ 0 ∧ Polynomial.aeval a P = 0 := by
    by_contra hcon
    push_neg at hcon
    apply h
    rw [injective_iff_map_eq_zero]
    intro P hP
    by_contra hP0
    exact hcon P hP0 hP
  obtain ⟨P, hP0, hP⟩ := this
  have hint : IsIntegral K a := (isAlgebraic_iff_isIntegral.mp ⟨P, hP0, hP⟩)
  exact hint.isUnit ha

section Transport

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
  (K : Type u) [Field K] [Algebra R K]

noncomputable abbrev sK := Scheme.TwoAffineOpenCover.specMap R K
noncomputable abbrev CK := pullback c (sK (R := R) K)
noncomputable abbrev π : CK c K ⟶ C := pullback.fst c (sK (R := R) K)
noncomputable abbrev σ : CK c K ⟶ Spec (CommRingCat.of K) := pullback.snd c (sK (R := R) K)
noncomputable abbrev UK : (CK c K).Opens := (π c K) ⁻¹ᵁ U

noncomputable def iK : K →+* Γ(CK c K, UK c U K) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (σ c K).appLE ⊤ (UK c U K) le_top).hom

noncomputable def iU : Γ(C, U) →+* Γ(CK c K, UK c U K) := ((π c K).app U).hom

theorem compat (r : R) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    iK c U K (algebraMap R K r) = iU c U K (algebraMap R Γ(C, U) r) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have key : CommRingCat.ofHom (algebraMap R K) ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (σ c K).appLE ⊤ (UK c U K) le_top =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ U le_top) ≫ (π c K).app U := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc, Category.assoc]
    congr 1
    have h1 : (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop ≫ (σ c K).appLE ⊤ (UK c U K) le_top =
        (σ c K ≫ sK (R := R) K).appLE ⊤ (UK c U K) le_top := by
      rw [Scheme.Hom.comp_appLE]; rfl
    rw [h1, ← pullback.condition, Scheme.Hom.comp_appLE]
    conv_rhs => rw [Scheme.Hom.appLE, Category.assoc, Scheme.Hom.app_eq_appLE (π c K), Scheme.Hom.map_appLE]
  have := congrArg (fun φ => φ.hom r) key
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  show ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (σ c K).appLE ⊤ (UK c U K) le_top).hom (algebraMap R K r) =
    ((π c K).app U).hom (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ U le_top).hom r)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply]
  exact this

noncomputable def Φ :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    K ⊗[R] Γ(C, U) →+* Γ(CK c K, UK c U K) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI algT : Algebra R Γ(CK c K, UK c U K) := ((iU c U K).comp (algebraMap R Γ(C, U))).toAlgebra
  let iUₐ : Γ(C, U) →ₐ[R] Γ(CK c K, UK c U K) := { iU c U K with commutes' := fun _ => rfl }
  let iKₐ : K →ₐ[R] Γ(CK c K, UK c U K) := { iK c U K with commutes' := fun r => compat c U K r }
  exact (Algebra.TensorProduct.lift iKₐ iUₐ (fun _ _ => Commute.all _ _)).toRingHom

theorem Φ_tmul (k : K) (a : Γ(C, U)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Φ c U K (k ⊗ₜ[R] a) = iK c U K k * iU c U K a := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  simp [Φ, Algebra.TensorProduct.lift_tmul]
  try rfl

theorem Φ_one_tmul (a : Γ(C, U)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Φ c U K ((1 : K) ⊗ₜ[R] a) = ((π c K).app U).hom a := by
  rw [Φ_tmul, map_one, one_mul]; rfl

end Transport

end TRANSCK

namespace TRANSCK

section Points

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (K : Type u) [Field K] [Algebra R K]

theorem sK_apply (t : Spec (CommRingCat.of K)) :
    ((sK (R := R) K).base t).asIdeal = RingHom.ker (algebraMap R K) := by
  have ht : t.asIdeal = ⊥ := by
    haveI : t.asIdeal.IsPrime := t.isPrime
    exact (Ideal.eq_bot_of_prime t.asIdeal)
  show (PrimeSpectrum.comap (algebraMap R K) t).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal, ht, ← RingHom.ker_eq_comap_bot]

theorem exists_mem_over {U : C.Opens} (hU : IsAffineOpen U)
    (hne : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Nontrivial (K ⊗[R] Γ(C, U))) :
    ∃ u : C, u ∈ U ∧ (c.base u).asIdeal = RingHom.ker (algebraMap R K) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  haveI := hne
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal (K ⊗[R] Γ(C, U))
  let L := K ⊗[R] Γ(C, U) ⧸ Q
  letI : Field L := Ideal.Quotient.field Q
  let φK : K →+* L := (Ideal.Quotient.mk Q).comp Algebra.TensorProduct.includeLeftRingHom
  let φU : Γ(C, U) →+* L := (Ideal.Quotient.mk Q).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := Γ(C, U))).toRingHom
  have hφ : φK.comp (algebraMap R K) = φU.comp (algebraMap R Γ(C, U)) := by
    ext r
    show Ideal.Quotient.mk Q (algebraMap R K r ⊗ₜ[R] (1 : Γ(C, U))) =
      Ideal.Quotient.mk Q ((1 : K) ⊗ₜ[R] algebraMap R Γ(C, U) r)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

  haveI : (RingHom.ker φU).IsPrime := RingHom.ker_isPrime _
  let q : Spec Γ(C, U) := ⟨RingHom.ker φU, inferInstance⟩
  let u : C := hU.fromSpec.base q
  have hu : u ∈ U := by
    have : u ∈ Set.range hU.fromSpec.base := ⟨q, rfl⟩
    rwa [IsAffineOpen.range_fromSpec] at this
  refine ⟨u, hu, ?_⟩

  have hcomp : hU.fromSpec ≫ c =
      Spec.map (c.appLE ⊤ U le_top) ≫ (isAffineOpen_top (Spec (CommRingCat.of R))).fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top _) hU le_top).symm
  have hcu : c.base u = ((Spec.map (c.appLE ⊤ U le_top) ≫
      (isAffineOpen_top (Spec (CommRingCat.of R))).fromSpec)).base q := by
    show (hU.fromSpec ≫ c).base q = _
    rw [hcomp]
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at hcu
  rw [hcu]

  show (PrimeSpectrum.comap ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ U le_top).hom q).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal]
  show Ideal.comap ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ U le_top).hom (RingHom.ker φU) = _
  have halg : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ U le_top).hom = algebraMap R Γ(C, U) := rfl
  rw [halg, RingHom.comap_ker, ← hφ, RingHom.ker_comp_of_injective _ φK.injective]

end Points

end TRANSCK

namespace TRANSCK

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (K : Type u) [Field K] [Algebra R K]
    (hne : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      Nontrivial (K ⊗[R] Γ(C, U))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Function.Injective
      (Polynomial.aeval ((1 : K) ⊗ₜ[R] f) :
        Polynomial K →ₐ[K] K ⊗[R] Γ(C, U)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  haveI := hne
  haveI : IsDomain (K ⊗[R] Γ(C, U)) :=
    AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral c U hU K hne
  by_contra hinj

  let t : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hst : ((sK (R := R) K).base t).asIdeal = RingHom.ker (algebraMap R K) := sK_apply (R := R) K t
  haveI : IsIntegral (CK c K) :=
    pullback_of_geometrically (GeometricallyIntegral.geometrically_isIntegral (f := c)) K (sK (R := R) K)
  have hUVK : (UK c U K) ⊓ ((π c K) ⁻¹ᵁ V) = (CK c K).basicOpen (((π c K).app U).hom f) := by
    rw [← Scheme.preimage_basicOpen, ← hf]
    rfl
  have hcov : (UK c U K) ⊔ ((π c K) ⁻¹ᵁ V) = ⊤ := by
    show (π c K) ⁻¹ᵁ U ⊔ (π c K) ⁻¹ᵁ V = ⊤
    rw [← Scheme.Hom.preimage_sup, hUV]
    rfl

  obtain ⟨u, huU, hcu⟩ := exists_mem_over c K hU hne
  obtain ⟨zU, hzU, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := c) (g := sK (R := R) K) u t
    (PrimeSpectrum.ext (by rw [hst]; exact hcu))
  have hzU' : zU ∈ UK c U K := by
    show (π c K).base zU ∈ U
    change (pullback.fst c (sK (R := R) K)).base zU = u at hzU
    rw [hzU]; exact huU

  let y : Spec (CommRingCat.of R) := (sK (R := R) K).base t
  have hcε : ∀ z, c.base (ε.1.base z) = z := fun z => by
    have := Scheme.Hom.comp_apply ε.1 c z
    rw [ε.2] at this
    exact this.symm
  obtain ⟨zV, hzV, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := c) (g := sK (R := R) K)
    (ε.1.base y) t (hcε y)
  have hεV : ε.1.base y ∈ V := by
    have hmem : ε.1.base y ∈ (⊤ : C.Opens) := trivial
    rw [← hUV, TopologicalSpace.Opens.mem_sup] at hmem
    rcases hmem with h | h
    · exact absurd ⟨y, rfl⟩ ((hUε _).mp h)
    · exact h
  have hzV' : zV ∈ (π c K) ⁻¹ᵁ V := by
    show (π c K).base zV ∈ V
    change (pullback.fst c (sK (R := R) K)).base zV = ε.1.base y at hzV
    rw [hzV]; exact hεV

  rcases zero_or_isUnit_of_not_injective _ hinj with h0 | hunit
  ·
    have hb : (CK c K).basicOpen (((π c K).app U).hom f) = ⊥ := by
      rw [← Φ_one_tmul c U K f, h0, map_zero]
      exact Scheme.basicOpen_zero _ _
    have hirr := (IrreducibleSpace.isIrreducible_univ (CK c K)).isPreirreducible
    obtain ⟨w, -, hwU, hwV⟩ := hirr _ _ (UK c U K).isOpen ((π c K) ⁻¹ᵁ V).isOpen
      ⟨zU, trivial, hzU'⟩ ⟨zV, trivial, hzV'⟩
    have hw : w ∈ (UK c U K) ⊓ ((π c K) ⁻¹ᵁ V) := ⟨hwU, hwV⟩
    rw [hUVK, hb] at hw
    exact hw
  ·
    have hb : (CK c K).basicOpen (((π c K).app U).hom f) = UK c U K := by
      apply Scheme.basicOpen_of_isUnit
      rw [← Φ_one_tmul c U K f]
      exact hunit.map _
    have hle : UK c U K ≤ (π c K) ⁻¹ᵁ V := by
      intro w hw
      have : w ∈ (UK c U K) ⊓ ((π c K) ⁻¹ᵁ V) := by rw [hUVK, hb]; exact hw
      exact this.2
    have htop : (π c K) ⁻¹ᵁ V = ⊤ := by
      apply top_le_iff.mp
      rw [← hcov]
      exact sup_le hle le_rfl

    haveI := Scheme.TwoAffineOpenCover.isAffineHom_fst c K
    have hVK : IsAffineOpen ((π c K) ⁻¹ᵁ V) := hV.preimage _
    rw [htop] at hVK
    haveI : IsAffine (⊤ : (CK c K).Opens) := hVK
    haveI : IsAffine (CK c K) := IsAffine.of_isIso (Scheme.topIso (CK c K)).inv

    haveI : IsFinite (σ c K) := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
    have hfin : RingHom.Finite ((σ c K).appTop).hom :=
      ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp inferInstance).2
    letI algKΓ : Algebra K Γ(CK c K, ⊤) :=
      (((σ c K).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    haveI : Module.Finite K Γ(CK c K, ⊤) := by
      have : (((σ c K).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Finite :=
        RingHom.Finite.comp hfin
          (RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective)
      exact this
    haveI : IsArtinianRing Γ(CK c K, ⊤) := IsArtinianRing.of_finite K _

    let εK : Spec (CommRingCat.of K) ⟶ CK c K :=
      pullback.lift (sK (R := R) K ≫ ε.1) (𝟙 _) (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])
    have hp : εK ≫ σ c K = 𝟙 _ := pullback.lift_snd _ _ _
    let x₀ : CK c K := εK.base (IsLocalRing.closedPoint K)
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    haveI hsrd : SmoothOfRelativeDimension 1 (σ c K) := MorphismProperty.pullback_snd _ _ inferInstance
    haveI hdvr : IsDiscreteValuationRing ((CK c K).presheaf.stalk x₀) :=
      @AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_section K _ (CK c K) (σ c K)
        inferInstance hsrd εK hp
    let S := (CK c K).presheaf.stalk x₀
    let η : Spec ((CK c K).presheaf.stalk x₀) := ⟨⊥, Ideal.isPrime_bot⟩
    have hη : η ≠ IsLocalRing.closedPoint S := by
      intro h
      have := congrArg PrimeSpectrum.asIdeal h
      exact IsDiscreteValuationRing.not_a_field S this.symm
    let u' : CK c K := ((CK c K).fromSpecStalk x₀).base η
    have hu'ne : u' ≠ x₀ := by
      intro h
      apply hη
      apply ((CK c K).fromSpecStalk x₀).isEmbedding.injective
      change ((CK c K).fromSpecStalk x₀).base η = ((CK c K).fromSpecStalk x₀).base (IsLocalRing.closedPoint S)
      erw [Scheme.fromSpecStalk_closedPoint]
      exact h
    have hu'sp : u' ⤳ x₀ := by
      have h1 : η ⤳ IsLocalRing.closedPoint S := IsLocalRing.specializes_closedPoint η
      have h2 := h1.map (TopCat.Hom.hom ((CK c K).fromSpecStalk x₀).base).continuous
      have h3 : (TopCat.Hom.hom ((CK c K).fromSpecStalk x₀).base) (IsLocalRing.closedPoint S) = x₀ := by
        erw [Scheme.fromSpecStalk_closedPoint]
      rw [h3] at h2
      exact h2

    let e := (CK c K).isoSpec.hom
    have hsp' : e.base u' ⤳ e.base x₀ := hu'sp.map (TopCat.Hom.hom e.base).continuous
    have heq : e.base u' = e.base x₀ := hsp'.eq
    exact hu'ne ((Scheme.homeoOfIso (CK c K).isoSpec).injective heq)

end TRANSCK

open scoped TensorProduct in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (K : Type u) [Field K] [Algebra R K]
    (hne : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      Nontrivial (K ⊗[R] Γ(C, U))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Function.Injective
      (Polynomial.aeval ((1 : K) ⊗ₜ[R] f) :
        Polynomial K →ₐ[K] K ⊗[R] Γ(C, U)) :=
  TRANSCK.main R c ε U V hU hV hUV hUε f g hf hg hfg K hne

end S_AlgebraicGeometry_SmoothProperCurve_injective_aeval_tensor_of_twoChartPoleDatum_global
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_injective_aeval_tensor_of_twoChartPoleDatum_global (solution)
