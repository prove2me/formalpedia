-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_hom_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/53b9a20b-0cb6-5b3b-b8a5-ac66b4f71d37

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_hom_of_algHom

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

namespace HG1A

section Spread

variable {X Y S : Scheme.{u}}

private theorem fromSpecStalkOfMem_eq_of_specializes (U : X.Opens) {ξ x : X} (h : ξ ⤳ x)
    (hx : x ∈ U) (hξ : ξ ∈ U) :
    U.fromSpecStalkOfMem ξ hξ =
      Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

private theorem partialMap_fromSpecStalkOfMem_eq_of_specializes (f : X.PartialMap Y) {ξ x : X}
    (h : ξ ⤳ x) (hx : x ∈ f.domain) (hξ : ξ ∈ f.domain) :
    f.fromSpecStalkOfMem hξ =
      Spec.map (X.presheaf.stalkSpecializes h) ≫ f.fromSpecStalkOfMem hx := by
  change f.domain.fromSpecStalkOfMem ξ hξ ≫ f.hom =
    Spec.map (X.presheaf.stalkSpecializes h) ≫ f.domain.fromSpecStalkOfMem x hx ≫ f.hom
  rw [fromSpecStalkOfMem_eq_of_specializes f.domain h hx hξ, Category.assoc]

private theorem partialMap_fromFunctionField_eq_of_mem [IrreducibleSpace X] (f : X.PartialMap Y)
    {x : X} (hx : x ∈ f.domain) :
    f.fromFunctionField =
      Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
        f.fromSpecStalkOfMem hx :=
  partialMap_fromSpecStalkOfMem_eq_of_specializes f (genericPoint_specializes x) hx
    ((genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec)

private theorem ofHom_algebraMap_stalk_functionField [IrreducibleSpace X] (x : X) :
    CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
  simp_rw [RingHom.algebraMap_toAlgebra]
  exact CommRingCat.ofHom_hom _

private theorem mem_domain_of_valuationRing (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X]
    [LocallyOfFiniteType sY] (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y)
    (hf : f.hom ≫ sY = f.domain.ι ≫ sX) (x : X) (hx : ValuationRing (X.presheaf.stalk x)) :
    x ∈ f.toRationalMap.domain := by
  haveI := hx
  have hcomm : f.fromFunctionField ≫ sY =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        (X.fromSpecStalk x ≫ sX) := by
    rw [ofHom_algebraMap_stalk_functionField]
    change (f.domain.fromSpecStalkOfMem (genericPoint X) _ ≫ f.hom) ≫ sY = _
    rw [Category.assoc, hf, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
  obtain ⟨l, hl₁, hl₂⟩ := (hY
    { R := X.presheaf.stalk x
      commRing := inferInstance
      domain := (inferInstance : IsDomain (X.presheaf.stalk x))
      valuationRing := hx
      K := X.functionField
      field := inferInstance
      algebra := (inferInstance : Algebra (X.presheaf.stalk x) X.functionField)
      isFractionRing := (inferInstance : IsFractionRing (X.presheaf.stalk x) X.functionField)
      i₁ := f.fromFunctionField
      i₂ := X.fromSpecStalk x ≫ sX
      commSq := ⟨hcomm⟩ }).exists_lift
  have hl₂' : l ≫ sY = X.fromSpecStalk x ≫ sX := hl₂
  have hl₁' : Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) ≫ l = f.fromFunctionField := by
    rw [← ofHom_algebraMap_stalk_functionField]
    exact hl₁
  refine Scheme.RationalMap.mem_domain.mpr
    ⟨Scheme.PartialMap.ofFromSpecStalk sX sY l hl₂',
     Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂', ?_⟩
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq_of_mem _
      (Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂'),
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY l hl₂']
  exact hl₁'

end Spread

section LocalRings

private theorem valuationRing_of_surjective {A B : Type*} [CommRing A] [IsDomain A]
    [ValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Surjective f) : ValuationRing B := by
  have : PreValuationRing B := ⟨fun a b => by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    obtain ⟨c, h | h⟩ := ValuationRing.cond a b
    · exact ⟨f c, Or.inl (by rw [← map_mul, h])⟩
    · exact ⟨f c, Or.inr (by rw [← map_mul, h])⟩⟩
  exact ⟨⟩

private theorem valuationRing_localization_atPrime {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [IsDomain B] [IsNoetherianRing B] [Algebra.EssFiniteType R B]
    (q : Ideal B) [q.IsPrime] [Algebra.IsUnramifiedAt R q] (hp : (q.under R).IsPrincipal) :
    ValuationRing (Localization.AtPrime q) := by
  letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q).mp inferInstance).2
  have hprinc : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).IsPrincipal := by
    rw [← hmap]
    obtain ⟨π, hπ⟩ := hp
    refine ⟨⟨algebraMap R _ π, ?_⟩⟩
    rw [hπ, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton,
      Ideal.submodule_span_eq]
  haveI : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (Localization.AtPrime q)).out 4 1).mp hprinc

private theorem isPrincipalIdealRing_mvPolynomial_fin_one (K : Type*) [Field K] :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) K) :=
  let e : MvPolynomial (Fin 1) K ≃ₐ[K] Polynomial K := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective

private theorem valuationRing_stalk {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [SmoothOfRelativeDimension 1 c] (x : C) :
    ValuationRing (C.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c) x
  have hU' : U = ⊤ := top_unique fun y _ => by
    haveI : Subsingleton ↥(Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rw [Subsingleton.elim y (c x)]
    exact e hxV
  subst hU'
  let ι : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  have hφ : ((c.appLE ⊤ V e).hom.comp ι.toRingHom).IsStandardSmoothOfRelativeDimension 1 := by
    simpa using hstd.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv ι)
  obtain ⟨g, -, hg⟩ := hφ.exists_etale_mvPolynomial
  algebraize [g]
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI : IsDomain Γ(C, V) := IsIntegral.component_integral V
  haveI : IsNoetherianRing Γ(C, V) :=
    Algebra.FiniteType.isNoetherianRing (MvPolynomial (Fin 1) K) Γ(C, V)
  haveI := isPrincipalIdealRing_mvPolynomial_fin_one K
  let q : Ideal Γ(C, V) := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hq : ValuationRing (Localization.AtPrime q) :=
    valuationRing_localization_atPrime (R := MvPolynomial (Fin 1) K) q
      (IsPrincipalIdealRing.principal _)
  show ValuationRing (C.presheaf.stalk ((⟨x, hxV⟩ : V) : C))
  letI := C.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  let eqv := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
    (C.presheaf.stalk ((⟨x, hxV⟩ : V) : C))
  exact valuationRing_of_surjective eqv.toRingEquiv.toRingHom eqv.surjective

end LocalRings

section Generic

variable {K : Type u} [Field K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']

private abbrev ffHom (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F') :
    M.C.functionField →+* M'.C.functionField :=
  M'.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)

private abbrev genericHom (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F') :
    Spec M'.C.functionField ⟶ M.C :=
  Spec.map (CommRingCat.ofHom (ffHom M M' φ)) ≫ M.C.fromSpecStalk (genericPoint M.C)

private theorem fromSpecStalk_genericPoint_comp_eq {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) :
    C.fromSpecStalk (genericPoint C) ≫ c =
      Spec.map (CommRingCat.ofHom (baseToFunctionField c)) := by
  refine ext_of_isAffine ?_
  have h1 : (Spec.map (CommRingCat.ofHom (baseToFunctionField c))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom (baseToFunctionField c) ≫
        (Scheme.ΓSpecIso (C.presheaf.stalk (genericPoint C))).inv := by
    rw [← Iso.inv_comp_eq]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  have h2 : CommRingCat.ofHom (baseToFunctionField c) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫
        C.presheaf.germ ⊤ (genericPoint C) trivial := by
    ext a
    rfl
  have h3 : (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)).op =
        𝟙 _ := by
    rw [show (homOfLE _).op = 𝟙 (Opposite.op ⊤) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, h3, Category.comp_id, h1, h2]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem ffHom_comp_baseToFunctionField (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') :
    (ffHom M M' φ).comp (baseToFunctionField M.toBase) = baseToFunctionField M'.toBase := by
  ext a
  change M'.ffEquiv (φ (M.ffEquiv.symm (baseToFunctionField M.toBase a))) =
    baseToFunctionField M'.toBase a
  rw [← M.ffEquiv_algebraMap a, RingEquiv.symm_apply_apply, φ.commutes, M'.ffEquiv_algebraMap]

private theorem genericHom_comp_toBase (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') :
    genericHom M M' φ ≫ M.toBase = M'.C.fromSpecStalk (genericPoint M'.C) ≫ M'.toBase := by
  dsimp only [genericHom]
  rw [Category.assoc, fromSpecStalk_genericPoint_comp_eq, fromSpecStalk_genericPoint_comp_eq,
    ← Spec.map_comp]
  congr 1
  ext a
  have h__af := RingHom.congr_fun (ffHom_comp_baseToFunctionField M M' φ) a
  simp at h__af
  exact h__af

private theorem isSeparated_of_over {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K))
    [IsSeparated g] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

private theorem existence_of_isProper {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] :
    ValuativeCriterion.Existence g := by
  have h : IsProper g := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1.existence

private theorem exists_hom_comp_toBase_eq (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') :
    ∃ π : M'.C ⟶ M.C, π ≫ M.toBase = M'.toBase ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ := by
  haveI : M.C.IsSeparated := isSeparated_of_over M.toBase
  have hψ := genericHom_comp_toBase M M' φ

  let f₀ : M'.C.PartialMap M.C :=
    Scheme.PartialMap.ofFromSpecStalk M'.toBase M.toBase (genericHom M M' φ) hψ
  have hf₀ : f₀.hom ≫ M.toBase = f₀.domain.ι ≫ M'.toBase :=
    Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _
  have hη : genericPoint M'.C ∈ f₀.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hf₀η : f₀.fromSpecStalkOfMem hη = genericHom M M' φ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _

  have hdom : f₀.toRationalMap.domain = ⊤ := top_unique fun x _ =>
    mem_domain_of_valuationRing M'.toBase M.toBase (existence_of_isProper M.toBase) f₀ hf₀ x
      (valuationRing_stalk M'.toBase x)
  let g := f₀.toRationalMap.toPartialMap
  let π : M'.C ⟶ M.C := M'.C.topIso.inv ≫ M'.C.homOfLE hdom.ge ≫ g.hom

  have hι : f₀.domain.ι ≫ π = f₀.hom := by
    have key := f₀.toPartialMap_toRationalMap_restrict
    rw [Scheme.PartialMap.restrict_hom] at key
    rw [← key]
    change f₀.domain.ι ≫ M'.C.topIso.inv ≫ M'.C.homOfLE hdom.ge ≫ g.hom =
      M'.C.homOfLE f₀.le_domain_toRationalMap ≫ g.hom
    simp only [← Category.assoc]
    congr 1
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.toIso_inv_ι, Category.comp_id]
  refine ⟨π, ?_, ?_⟩
  ·
    haveI : IsDominant f₀.domain.ι :=
      ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact f₀.dense_domain⟩
    refine ext_of_isDominant f₀.domain.ι ?_
    rw [reassoc_of% hι, hf₀]
  · rw [← Scheme.Opens.fromSpecStalkOfMem_ι f₀.domain (genericPoint M'.C) hη, Category.assoc, hι]
    exact hf₀η

private theorem isDominant_fromSpecStalk_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  refine ⟨?_⟩
  have hη : genericPoint X ∈ Set.range (X.fromSpecStalk (genericPoint X)) :=
    ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  have hd : Dense ({genericPoint X} : Set X) :=
    dense_iff_closure_eq.mpr (genericPoint_spec X).def
  exact hd.mono (Set.singleton_subset_iff.mpr hη)

private theorem apply_genericPoint_eq (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    π.base (genericPoint M'.C) = genericPoint M.C := by
  have h1 : (M'.C.fromSpecStalk (genericPoint M'.C))
      (IsLocalRing.closedPoint (M'.C.presheaf.stalk (genericPoint M'.C))) = genericPoint M'.C :=
    Scheme.fromSpecStalk_closedPoint
  have h2 : π ((M'.C.fromSpecStalk (genericPoint M'.C))
      (IsLocalRing.closedPoint (M'.C.presheaf.stalk (genericPoint M'.C)))) =
      (genericHom M M' φ) (IsLocalRing.closedPoint (M'.C.presheaf.stalk (genericPoint M'.C))) := by
    rw [← Scheme.Hom.comp_apply, hd]
  rw [h1] at h2
  rw [h2]
  show (Spec.map (CommRingCat.ofHom (ffHom M M' φ)) ≫ M.C.fromSpecStalk (genericPoint M.C))
    (IsLocalRing.closedPoint (M'.C.presheaf.stalk (genericPoint M'.C))) = genericPoint M.C
  rw [Scheme.Hom.comp_apply]
  have h3 : (Spec.map (CommRingCat.ofHom (ffHom M M' φ)))
      (IsLocalRing.closedPoint (M'.C.presheaf.stalk (genericPoint M'.C))) =
      IsLocalRing.closedPoint (M.C.presheaf.stalk (genericPoint M.C)) :=
    haveI : Subsingleton (PrimeSpectrum M.C.functionField) := inferInstance
    Subsingleton.elim (α := PrimeSpectrum M.C.functionField) _ _
  rw [h3]
  exact Scheme.fromSpecStalk_closedPoint

private theorem stalkMap_comp_stalkSpecializes (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (x : M'.C) :
    π.stalkMap x ≫ M'.C.presheaf.stalkSpecializes (genericPoint_specializes x) =
      M.C.presheaf.stalkSpecializes (genericPoint_specializes (π.base x)) ≫
        CommRingCat.ofHom (ffHom M M' φ) := by
  apply Spec.map_injective
  rw [← cancel_mono (M.C.fromSpecStalk (π.base x))]
  simp only [Spec.map_comp, Category.assoc]
  rw [Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, hd]
  rfl

private theorem algebraMap_stalkMap_apply (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (x : M'.C)
    (a : M.C.presheaf.stalk (π.base x)) :
    algebraMap (M'.C.presheaf.stalk x) M'.C.functionField ((π.stalkMap x).hom a) =
      ffHom M M' φ (algebraMap (M.C.presheaf.stalk (π.base x)) M.C.functionField a) := by
  have h := congrArg (fun g => g.hom a) (stalkMap_comp_stalkSpecializes M M' φ π hd x)
  simp [RingHom.algebraMap_toAlgebra] at h
  exact h

private theorem valuationRing_stalk' (M : CurveModel K F) (x : M.C) :
    ValuationRing (M.C.presheaf.stalk x) :=
  valuationRing_stalk M.toBase x

private theorem eq_of_fromSpecStalk_comp_eq (M : CurveModel K F) (M' : CurveModel K F')
    {π π' : M'.C ⟶ M.C}
    (h : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π' =
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π) :
    π' = π := by
  haveI : M.C.IsSeparated := isSeparated_of_over M.toBase
  haveI := isDominant_fromSpecStalk_genericPoint M'.C
  exact ext_of_isDominant (M'.C.fromSpecStalk (genericPoint M'.C)) h

end Generic

section Places

variable {K : Type u} [Field K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']

private def stalkRange (M : CurveModel K F) (x : M.C) : Subring F :=
  ((M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp
    (algebraMap (M.C.presheaf.stalk x) M.C.functionField)).range

private theorem stalkRange_closedPoint (M : CurveModel K F) (x : closedPoints M.C) :
    stalkRange M x.1 = (M.placeOfPoint x).toValuationSubring.toSubring :=
  M.range_stalk_eq x

private theorem mem_stalkRange_closedPoint (M : CurveModel K F) (x : closedPoints M.C) (f : F) :
    f ∈ stalkRange M x.1 ↔ f ∈ (M.placeOfPoint x).toValuationSubring := by
  rw [stalkRange_closedPoint]
  exact ValuationSubring.mem_toSubring _ _

private theorem stalkRange_genericPoint (M : CurveModel K F) :
    stalkRange M (genericPoint M.C) = ⊤ := by
  rw [eq_top_iff]
  rintro g -
  simp only [stalkRange, RingHom.mem_range, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  refine ⟨M.ffEquiv g, ?_⟩
  simp [RingHom.algebraMap_toAlgebra]

private theorem map_stalkRange_le (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (y : M'.C) :
    (stalkRange M (π.base y)).map φ.toRingHom ≤ stalkRange M' y := by
  intro g hg
  rw [Subring.mem_map] at hg
  obtain ⟨g, hg, rfl⟩ := hg
  simp only [stalkRange, RingHom.mem_range] at hg ⊢
  obtain ⟨a, rfl⟩ := hg
  refine ⟨(π.stalkMap y).hom a, ?_⟩
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [algebraMap_stalkMap_apply M M' φ π hd y a]
  simp [ffHom]

private theorem apply_mem_stalkRange (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (y : M'.C) {f : F}
    (hf : f ∈ stalkRange M (π.base y)) : φ f ∈ stalkRange M' y :=
  map_stalkRange_le M M' φ π hd y (Subring.mem_map.2 ⟨f, hf, rfl⟩)

private theorem eq_of_specializes (M : CurveModel K F) (x₀ : closedPoints M.C) {a b : M.C}
    (ha : a ⤳ x₀.1) (hb : b ⤳ x₀.1) (ha' : a ≠ x₀.1) (hb' : b ≠ x₀.1) : a = b := by

  let j : M.C.presheaf.stalk x₀.1 →+* F :=
    (M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp
      (algebraMap (M.C.presheaf.stalk x₀.1) M.C.functionField)
  have hj : Function.Injective j :=
    M.ffEquiv.symm.injective.comp
      (IsFractionRing.injective (M.C.presheaf.stalk x₀.1) M.C.functionField)
  haveI : IsPrincipalIdealRing j.range := by
    show IsPrincipalIdealRing (stalkRange M x₀.1)
    rw [stalkRange_closedPoint]
    exact inferInstanceAs (IsPrincipalIdealRing (M.placeOfPoint x₀).toValuationSubring)
  haveI : IsPrincipalIdealRing (M.C.presheaf.stalk x₀.1) := by
    let e : M.C.presheaf.stalk x₀.1 ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
      ⟨fun p q h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
    exact IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective

  have key : ∀ p : PrimeSpectrum (M.C.presheaf.stalk x₀.1),
      M.C.fromSpecStalk x₀.1 p ≠ x₀.1 → p.asIdeal = ⊥ := by
    intro p hp
    by_contra hne
    apply hp
    have hmax : p.asIdeal = IsLocalRing.maximalIdeal (M.C.presheaf.stalk x₀.1) :=
      IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne p.isPrime)
    have hp' : p = IsLocalRing.closedPoint (M.C.presheaf.stalk x₀.1) := PrimeSpectrum.ext hmax
    rw [hp']
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨pa, hpa⟩ : a ∈ Set.range (M.C.fromSpecStalk x₀.1) := by
    rw [Scheme.range_fromSpecStalk]
    exact ha
  obtain ⟨pb, hpb⟩ : b ∈ Set.range (M.C.fromSpecStalk x₀.1) := by
    rw [Scheme.range_fromSpecStalk]
    exact hb
  have hab : pa = pb :=
    PrimeSpectrum.ext ((key pa (by rw [hpa]; exact ha')).trans
      (key pb (by rw [hpb]; exact hb')).symm)
  rw [← hpa, ← hpb, hab]

private theorem mem_closedPoints_or_eq_genericPoint (M : CurveModel K F) (x : M.C) :
    x ∈ closedPoints M.C ∨ x = genericPoint M.C := by
  by_cases hx : x ∈ closedPoints M.C
  · exact Or.inl hx
  right
  haveI : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  obtain ⟨x₀, hxx₀, hx₀⟩ := nonempty_inter_closedPoints (X := M.C) (Z := closure {x})
    ⟨x, subset_closure (Set.mem_singleton x)⟩ isClosed_closure.isLocallyClosed
  have hspec : x ⤳ x₀ := specializes_iff_mem_closure.2 hxx₀
  have hne : x ≠ x₀ := fun h => hx (h ▸ hx₀)
  by_cases hη : genericPoint M.C = x₀
  · have hx' : x ⤳ genericPoint M.C := by
      rw [hη]
      exact hspec
    exact (hx'.antisymm (genericPoint_specializes x)).eq
  · exact eq_of_specializes M ⟨x₀, hx₀⟩ hspec (genericPoint_specializes x₀) hne hη

private theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F')
    (f : F) : f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

private theorem apply_ne_genericPoint (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (y : closedPoints M'.C) : π.base y.1 ≠ genericPoint M.C := by
  intro hgen
  apply ((M'.placeOfPoint y).restrictAlong φ hφ).ne_top'
  refine SetLike.ext fun f => ⟨fun _ => ValuationSubring.mem_top f, fun _ => ?_⟩
  rw [mem_restrictAlong_iff, ← mem_stalkRange_closedPoint]
  apply apply_mem_stalkRange M M' φ π hd y.1
  rw [hgen, stalkRange_genericPoint]
  exact Subring.mem_top f

private theorem apply_mem_closedPoints (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (y : closedPoints M'.C) : π.base y.1 ∈ closedPoints M.C :=
  (mem_closedPoints_or_eq_genericPoint M _).resolve_right (apply_ne_genericPoint M M' φ hφ π hd y)

private theorem ofPrime_eq_top_or_eq {A : ValuationSubring F} [IsDiscreteValuationRing A]
    (P : Ideal A)
    [P.IsPrime] : A.ofPrime P = ⊤ ∨ A.ofPrime P = A := by
  by_cases hP : P = ⊥
  · left
    subst hP
    exact ValuationSubring.ofPrime_bot A
  · right
    have hmax : P = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hP inferInstance)
    subst hmax
    exact ValuationSubring.ofPrime_top A

private theorem place_eq_of_le {v v' : Place K F}
    (h : v.toValuationSubring ≤ v'.toValuationSubring) : v = v' := by
  apply Place.ext
  have key := ValuationSubring.ofPrime_idealOfLE v.toValuationSubring v'.toValuationSubring h
  rcases ofPrime_eq_top_or_eq (v.toValuationSubring.idealOfLE v'.toValuationSubring h) with
    htop | heq
  · exact absurd (key.symm.trans htop) v'.ne_top'
  · exact (key.symm.trans heq).symm

private theorem exists_mem_closedPoints_placeOfPoint_eq (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (y : closedPoints M'.C) :
    ∃ h : π.base y.1 ∈ closedPoints M.C,
      M.placeOfPoint ⟨π.base y.1, h⟩ = (M'.placeOfPoint y).restrictAlong φ hφ := by
  have _ := hfin
  have _ := ha
  have h := apply_mem_closedPoints M M' φ hφ π hd y
  refine ⟨h, place_eq_of_le ?_⟩
  intro f hf
  rw [mem_restrictAlong_iff, ← mem_stalkRange_closedPoint M' y]
  apply apply_mem_stalkRange M M' φ π hd y.1
  exact (mem_stalkRange_closedPoint M ⟨π.base y.1, h⟩ f).2 hf

variable [CharZero K]

private theorem restrictAlong_fiber_finite (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (v : Place K F) :
    {w : Place K F' | w.restrictAlong φ hφ = v}.Finite := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Module.Finite F F' := hfin
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  exact Place.finite_setOf_restrict_eq (F := F) (F' := F') v

private theorem finite_preimage_singleton (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (x : M.C) : (π.base ⁻¹' {x}).Finite := by
  classical
  rcases mem_closedPoints_or_eq_genericPoint M x with hx | rfl
  ·

    let T : Set (closedPoints M'.C) := {y | π.base y.1 = x}
    have hT : T.Finite := by
      refine Set.Finite.of_finite_image (f := fun y => M'.placeOfPoint y) ?_ ?_
      · refine (restrictAlong_fiber_finite φ hφ hfin (M.placeOfPoint ⟨x, hx⟩)).subset ?_
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨h, he⟩ := exists_mem_closedPoints_placeOfPoint_eq M M' φ hφ hfin π ha hd y
        show (M'.placeOfPoint y).restrictAlong φ hφ = M.placeOfPoint ⟨x, hx⟩
        rw [← he]
        congr 1
        exact Subtype.ext hy
      · exact fun y _ y' _ hyy' => M'.placeOfPoint_bijective.1 hyy'
    refine ((hT.image Subtype.val).union (Set.finite_singleton (genericPoint M'.C))).subset ?_
    intro y hy
    rcases mem_closedPoints_or_eq_genericPoint M' y with hy' | rfl
    · exact Or.inl ⟨⟨y, hy'⟩, hy, rfl⟩
    · exact Or.inr rfl
  ·
    refine (Set.finite_singleton (genericPoint M'.C)).subset ?_
    intro y hy
    rcases mem_closedPoints_or_eq_genericPoint M' y with hy' | rfl
    · exact absurd hy (apply_ne_genericPoint M M' φ hφ π hd ⟨y, hy'⟩)
    · rfl

end Places

section Rank

variable {K : Type u} [Field K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']

private theorem isProper (M : CurveModel K F) (M' : CurveModel K F')
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase) : IsProper π := by
  have h : IsProper (π ≫ M.toBase) := by rw [ha]; infer_instance
  exact IsProper.of_comp π M.toBase

private theorem locallyOfFiniteType (M : CurveModel K F) (M' : CurveModel K F')
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase) : LocallyOfFiniteType π := by
  have h : LocallyOfFiniteType (π ≫ M.toBase) := by rw [ha]; infer_instance
  exact locallyOfFiniteType_of_comp π M.toBase

private theorem locallyQuasiFinite [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    LocallyQuasiFinite π := by
  haveI := isProper M M' π ha
  haveI := locallyOfFiniteType M M' π ha
  exact (locallyQuasiFinite_iff_finite_preimage_singleton (f := π)).mpr
    (fun x => finite_preimage_singleton M M' φ hφ hfin π ha hd x)

private theorem isFinite [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    IsFinite π := by
  haveI := isProper M M' π ha
  haveI := locallyQuasiFinite M M' φ hφ hfin π ha hd
  exact IsFinite.of_isProper_of_locallyQuasiFinite π

private theorem stalkMap_injective (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (x : M'.C) :
    Function.Injective (π.stalkMap x).hom := by
  intro a b hab
  have h := congrArg (algebraMap (M'.C.presheaf.stalk x) M'.C.functionField) hab
  rw [algebraMap_stalkMap_apply M M' φ π hd x a, algebraMap_stalkMap_apply M M' φ π hd x b] at h
  exact IsFractionRing.injective (M.C.presheaf.stalk (π.base x)) M.C.functionField
    ((ffHom M M' φ).injective h)

private theorem flat_of_injective_of_valuationRing {A B : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Injective f) :
    f.Flat := by
  letI : Algebra A B := f.toAlgebra
  show Module.Flat A B
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
  intro b hb
  obtain ⟨⟨a, ha⟩, hab⟩ := (Submodule.mem_torsion_iff b).mp hb
  have hab' : f a * b = 0 := hab
  rcases mul_eq_zero.mp hab' with h | h
  · exact absurd ((map_eq_zero_iff f hf).mp h) (nonZeroDivisors.ne_zero ha)
  · exact h

private theorem flat_stalkMap (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (x : M'.C) :
    (π.stalkMap x).hom.Flat := by
  haveI := valuationRing_stalk' M (π.base x)
  exact flat_of_injective_of_valuationRing (π.stalkMap x).hom
    (stalkMap_injective M M' φ π hd x)

private theorem flat (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    Flat π := by
  have _ := hφ
  have _ := hfin
  have _ := ha
  exact Flat.of_stalkMap π (fun x => flat_stalkMap M M' φ π hd x)

private theorem locallyOfFinitePresentation_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] : LocallyOfFinitePresentation f :=
  LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

private theorem _root_.HG1A.isLocallyNoetherian (M : CurveModel K F) : IsLocallyNoetherian M.C :=
  LocallyOfFiniteType.isLocallyNoetherian M.toBase

p2m_export "HG1A" "isLocallyNoetherian"
private theorem locallyOfFinitePresentation (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    LocallyOfFinitePresentation π := by
  have _ := hφ
  have _ := hfin
  have _ := hd
  haveI := isLocallyNoetherian M
  haveI := locallyOfFiniteType M M' π ha
  exact locallyOfFinitePresentation_of_locallyOfFiniteType π

private theorem finrank_eq_finrank_genericPoint [CharZero K] (M : CurveModel K F)
    (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (x : M.C) :
    π.finrank x = π.finrank (genericPoint M.C) := by
  haveI := isFinite M M' φ hφ hfin π ha hd
  haveI := flat M M' φ hφ hfin π ha hd
  haveI := locallyOfFinitePresentation M M' φ hφ hfin π ha hd
  have hc : IsLocallyConstant π.finrank := Scheme.Hom.isLocallyConstant_finrank π
  exact hc.apply_eq_of_preconnectedSpace x (genericPoint M.C)

private theorem rankAtStalk_bot_eq_finrank {A B KA KB : Type u} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [FaithfulSMul A B]
    [Field KA] [Algebra A KA] [IsFractionRing A KA] [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Algebra KA KB] [Algebra A KB] [IsScalarTower A B KB] [IsScalarTower A KA KB] :
    Module.rankAtStalk (R := A) B ⊥ = Module.finrank KA KB := by
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing A KA B KB]
  have hp : (⊥ : Ideal A).primeCompl ≤ nonZeroDivisors A := (Ideal.primeCompl_bot (α := A)).le
  show Module.finrank (Localization.AtPrime (⊥ : Ideal A))
      (LocalizedModule (⊥ : Ideal A).primeCompl B) = Module.finrank A B
  rw [Module.finrank, IsLocalization.rank_eq (Localization.AtPrime (⊥ : Ideal A))
    (⊥ : Ideal A).primeCompl hp]
  exact IsLocalizedModule.finrank_eq (⊥ : Ideal A).primeCompl
    (LocalizedModule.mkLinearMap (⊥ : Ideal A).primeCompl B) hp

private theorem genericPoint_mem_preimage (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    {U : M.C.Opens} (hη : genericPoint M.C ∈ U) : genericPoint M'.C ∈ π ⁻¹ᵁ U := by
  show π.base (genericPoint M'.C) ∈ U
  rw [apply_genericPoint_eq M M' φ π hd]
  exact hη

private theorem algebraMap_germ (M : CurveModel K F) (U : M.C.Opens) (hη : genericPoint M.C ∈ U)
    (x : M.C) (hx : x ∈ U) (b : Γ(M.C, U)) :
    haveI : Nonempty U := ⟨⟨_, hη⟩⟩
    @algebraMap (M.C.presheaf.stalk x) M.C.functionField _ _ (stalkFunctionFieldAlgebra M.C x)
        ((M.C.presheaf.germ U x hx).hom b) =
      algebraMap Γ(M.C, U) M.C.functionField b := by
  haveI : Nonempty U := ⟨⟨_, hη⟩⟩
  change (M.C.presheaf.stalkSpecializes _).hom ((M.C.presheaf.germ U x hx).hom b) =
    (M.C.presheaf.germ U (genericPoint M.C) _).hom b
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]

private theorem algebraMap_app_apply (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hη : genericPoint M.C ∈ U) (a : Γ(M.C, U)) :
    haveI : Nonempty U := ⟨⟨_, hη⟩⟩
    haveI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, genericPoint_mem_preimage M M' φ π hd hη⟩⟩
    algebraMap Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField ((π.app U).hom a) =
      ffHom M M' φ (algebraMap Γ(M.C, U) M.C.functionField a) := by
  haveI : Nonempty U := ⟨⟨_, hη⟩⟩
  have hη' : genericPoint M'.C ∈ π ⁻¹ᵁ U := genericPoint_mem_preimage M M' φ π hd hη
  have hx : π.base (genericPoint M'.C) ∈ U := hη'
  haveI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hη'⟩⟩
  calc algebraMap Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField ((π.app U).hom a)
      = @algebraMap (M'.C.presheaf.stalk (genericPoint M'.C)) M'.C.functionField _ _
          (stalkFunctionFieldAlgebra M'.C (genericPoint M'.C))
          ((M'.C.presheaf.germ (π ⁻¹ᵁ U) (genericPoint M'.C) hη').hom ((π.app U).hom a)) :=
        (algebraMap_germ M' (π ⁻¹ᵁ U) hη' (genericPoint M'.C) hη' ((π.app U).hom a)).symm
    _ = @algebraMap (M'.C.presheaf.stalk (genericPoint M'.C)) M'.C.functionField _ _
          (stalkFunctionFieldAlgebra M'.C (genericPoint M'.C))
          ((π.stalkMap (genericPoint M'.C)).hom
            ((M.C.presheaf.germ U (π.base (genericPoint M'.C)) hx).hom a)) :=
        congrArg (@algebraMap (M'.C.presheaf.stalk (genericPoint M'.C)) M'.C.functionField
            _ _ (stalkFunctionFieldAlgebra M'.C (genericPoint M'.C)))
          (Scheme.Hom.germ_stalkMap_apply π U (genericPoint M'.C) hx a).symm
    _ = ffHom M M' φ (@algebraMap (M.C.presheaf.stalk (π.base (genericPoint M'.C)))
          M.C.functionField _ _ (stalkFunctionFieldAlgebra M.C (π.base (genericPoint M'.C)))
          ((M.C.presheaf.germ U (π.base (genericPoint M'.C)) hx).hom a)) :=
        algebraMap_stalkMap_apply M M' φ π hd (genericPoint M'.C) _
    _ = ffHom M M' φ (algebraMap Γ(M.C, U) M.C.functionField a) :=
        congrArg (ffHom M M' φ) (algebraMap_germ M U hη (π.base (genericPoint M'.C)) hx a)

private theorem injective_app (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hη : genericPoint M.C ∈ U) : Function.Injective (π.app U).hom := by
  haveI : Nonempty U := ⟨⟨_, hη⟩⟩
  haveI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, genericPoint_mem_preimage M M' φ π hd hη⟩⟩
  intro a b hab
  have h := congrArg (algebraMap Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField) hab
  rw [algebraMap_app_apply M M' φ π hd U hη a, algebraMap_app_apply M M' φ π hd U hη b] at h
  exact M.C.germToFunctionField_injective U ((ffHom M M' φ).injective h)

private theorem isPullback_fromSpec (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen (π ⁻¹ᵁ U)) :
    IsPullback hV.fromSpec (Spec.map (π.app U)) π hU.fromSpec := by
  have _ := hφ
  have _ := hfin
  have _ := ha
  have _ := hd
  refine (IsOpenImmersion.isPullback (Spec.map (π.app U)) hV.fromSpec hU.fromSpec π ?_ ?_).flip
  · rw [Scheme.Hom.app_eq_appLE]
    exact (IsAffineOpen.SpecMap_appLE_fromSpec π hU hV le_rfl).symm
  · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]

private theorem finite_app [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hU : IsAffineOpen U) : (π.app U).hom.Finite := by
  haveI := isFinite M M' φ hφ hfin π ha hd
  exact (IsFinite.SpecMap_iff _).mp
    (MorphismProperty.of_isPullback (P := @IsFinite)
      (isPullback_fromSpec M M' φ hφ hfin π ha hd U hU (hU.preimage π))
      (inferInstanceAs (IsFinite π)))

private theorem flat_app [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hU : IsAffineOpen U) : (π.app U).hom.Flat := by
  haveI := isFinite M M' φ hφ hfin π ha hd
  haveI := flat M M' φ hφ hfin π ha hd
  exact Flat.SpecMap_iff.mp
    (MorphismProperty.of_isPullback (P := @Flat)
      (isPullback_fromSpec M M' φ hφ hfin π ha hd U hU (hU.preimage π))
      (inferInstanceAs (Flat π)))

private theorem fromSpec_bot (M : CurveModel K F) (U : M.C.Opens) (hU : IsAffineOpen U)
    (hη : genericPoint M.C ∈ U) :
    haveI : Nonempty U := ⟨⟨_, hη⟩⟩
    hU.fromSpec (⊥ : PrimeSpectrum Γ(M.C, U)) = genericPoint M.C := by
  haveI : Nonempty U := ⟨⟨_, hη⟩⟩
  have h := hU.fromSpec_primeIdealOf ⟨genericPoint M.C, hη⟩
  rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine] at h
  exact h

private theorem finrank_genericPoint_eq_ringHom_finrank [CharZero K] (M : CurveModel K F)
    (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hU : IsAffineOpen U) (hη : genericPoint M.C ∈ U) :
    haveI : Nonempty U := ⟨⟨_, hη⟩⟩
    π.finrank (genericPoint M.C) = (π.app U).hom.finrank (⊥ : PrimeSpectrum Γ(M.C, U)) := by
  haveI : Nonempty U := ⟨⟨_, hη⟩⟩
  haveI := isFinite M M' φ hφ hfin π ha hd
  haveI := flat M M' φ hφ hfin π ha hd
  have hb : hU.fromSpec (⊥ : PrimeSpectrum Γ(M.C, U)) = genericPoint M.C := fromSpec_bot M U hU hη

  have h1 := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_fromSpec M M' φ hφ hfin π ha hd U hU (hU.preimage π)) (⊥ : PrimeSpectrum Γ(M.C, U))
  rw [hb] at h1
  exact h1.symm.trans (congrFun (Scheme.Hom.finrank_SpecMap_eq_finrank
    (finite_app M M' φ hφ hfin π ha hd U hU) (flat_app M M' φ hφ hfin π ha hd U hU)) _)

private theorem finrank_functionField (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F') :
    letI := (ffHom M M' φ).toAlgebra
    Module.finrank M.C.functionField M'.C.functionField = finrankAlong K φ := by
  letI := (ffHom M M' φ).toAlgebra
  letI := algebraAlong φ
  show Module.finrank M.C.functionField M'.C.functionField = Module.finrank F F'
  refine Algebra.finrank_eq_of_equiv_equiv M.ffEquiv.symm M'.ffEquiv.symm ?_
  ext x
  simp [ffHom, RingHom.algebraMap_toAlgebra]

private theorem finrank_genericPoint [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    π.finrank (genericPoint M.C) = finrankAlong K φ := by
  obtain ⟨U, hU, hmem⟩ := M.finset_subset_affineOpen {genericPoint M.C}
  have hη : genericPoint M.C ∈ U := hmem _ (Finset.mem_singleton_self _)
  haveI : Nonempty U := ⟨⟨_, hη⟩⟩
  have hη' := genericPoint_mem_preimage M M' φ π hd hη
  haveI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hη'⟩⟩
  have hf := finrank_functionField M M' φ
  rw [finrank_genericPoint_eq_ringHom_finrank M M' φ hφ hfin π ha hd U hU hη, ← hf]

  letI : Algebra Γ(M.C, U) Γ(M'.C, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  letI : Algebra M.C.functionField M'.C.functionField := (ffHom M M' φ).toAlgebra
  letI : Algebra Γ(M.C, U) M'.C.functionField :=
    ((algebraMap Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField).comp (π.app U).hom).toAlgebra
  haveI : Module.Finite Γ(M.C, U) Γ(M'.C, π ⁻¹ᵁ U) := finite_app M M' φ hφ hfin π ha hd U hU
  haveI : FaithfulSMul Γ(M.C, U) Γ(M'.C, π ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (injective_app M M' φ π hd U hη)
  haveI : IsFractionRing Γ(M.C, U) M.C.functionField :=
    functionField_isFractionRing_of_isAffineOpen M.C U hU
  haveI : IsFractionRing Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField :=
    functionField_isFractionRing_of_isAffineOpen M'.C (π ⁻¹ᵁ U)
      (by haveI := isFinite M M' φ hφ hfin π ha hd; exact hU.preimage π)
  haveI : IsScalarTower Γ(M.C, U) Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  haveI : IsScalarTower Γ(M.C, U) M.C.functionField M'.C.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => algebraMap_app_apply M M' φ π hd U hη a
  exact rankAtStalk_bot_eq_finrank (A := Γ(M.C, U)) (B := Γ(M'.C, π ⁻¹ᵁ U))
    (KA := M.C.functionField) (KB := M'.C.functionField)

private theorem _root_.HG1A.finrank_eq [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (x : M.C) : π.finrank x = finrankAlong K φ := by
  rw [finrank_eq_finrank_genericPoint M M' φ hφ hfin π ha hd x,
    finrank_genericPoint M M' φ hφ hfin π ha hd]

p2m_export "HG1A" "finrank_eq"
end Rank

end HG1A

open AlgebraicCurve.CurveModel HG1A in
theorem solution {K : Type u} [Field K] [CharZero K]
    {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']
    (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) :
    ∃ π : M'.C ⟶ M.C,
      π ≫ M.toBase = M'.toBase ∧
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧
      (∀ x : M.C, π.finrank x = finrankAlong K φ) ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π =
        Spec.map (CommRingCat.ofHom
          (M'.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) ∧
      (∀ y : closedPoints M'.C, ∃ h : π.base y.1 ∈ closedPoints M.C,
        M.placeOfPoint ⟨π.base y.1, h⟩ = (M'.placeOfPoint y).restrictAlong φ hφ) ∧
      ∀ π' : M'.C ⟶ M.C,
        M'.C.fromSpecStalk (genericPoint M'.C) ≫ π' =
          M'.C.fromSpecStalk (genericPoint M'.C) ≫ π → π' = π := by
  obtain ⟨π, ha, hd⟩ := exists_hom_comp_toBase_eq M M' φ
  exact ⟨π, ha, isFinite M M' φ hφ hfin π ha hd, flat M M' φ hφ hfin π ha hd,
    locallyOfFinitePresentation M M' φ hφ hfin π ha hd,
    fun x => finrank_eq M M' φ hφ hfin π ha hd x, hd,
    fun y => exists_mem_closedPoints_placeOfPoint_eq M M' φ hφ hfin π ha hd y,
    fun π' h => eq_of_fromSpecStalk_comp_eq M M' h⟩

end

end S_AlgebraicCurve_CurveModel_exists_hom_of_algHom
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_hom_of_algHom (solution)
