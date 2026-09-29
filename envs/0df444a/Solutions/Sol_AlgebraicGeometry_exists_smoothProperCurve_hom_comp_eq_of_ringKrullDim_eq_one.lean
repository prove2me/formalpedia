-- Prove2me | solution 1 for AlgebraicGeometry.exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fef5f62d-de09-551e-a2a5-2bc9b1fb35f0

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_of_perfectField
import Theorems.Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

namespace P2mNormExt

section Spread

variable {X Y S : Scheme.{u}}

theorem fromSpecStalkOfMem_eq_of_specializes (U : X.Opens) {ξ x : X} (h : ξ ⤳ x)
    (hx : x ∈ U) (hξ : ξ ∈ U) :
    U.fromSpecStalkOfMem ξ hξ =
      Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

theorem partialMap_fromSpecStalkOfMem_eq_of_specializes (f : X.PartialMap Y) {ξ x : X}
    (h : ξ ⤳ x) (hx : x ∈ f.domain) (hξ : ξ ∈ f.domain) :
    f.fromSpecStalkOfMem hξ =
      Spec.map (X.presheaf.stalkSpecializes h) ≫ f.fromSpecStalkOfMem hx := by
  change f.domain.fromSpecStalkOfMem ξ hξ ≫ f.hom =
    Spec.map (X.presheaf.stalkSpecializes h) ≫ f.domain.fromSpecStalkOfMem x hx ≫ f.hom
  rw [fromSpecStalkOfMem_eq_of_specializes f.domain h hx hξ, Category.assoc]

theorem partialMap_fromFunctionField_eq_of_mem [IrreducibleSpace X] (f : X.PartialMap Y)
    {x : X} (hx : x ∈ f.domain) :
    f.fromFunctionField =
      Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
        f.fromSpecStalkOfMem hx :=
  partialMap_fromSpecStalkOfMem_eq_of_specializes f (genericPoint_specializes x) hx
    ((genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec)

theorem ofHom_algebraMap_stalk_functionField [IrreducibleSpace X] (x : X) :
    CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
  simp_rw [RingHom.algebraMap_toAlgebra]
  exact CommRingCat.ofHom_hom _

theorem mem_domain_of_valuationRing (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X]
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

theorem valuationRing_of_surjective {A B : Type*} [CommRing A] [IsDomain A]
    [ValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Surjective f) : ValuationRing B := by
  have : PreValuationRing B := ⟨fun a b => by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    obtain ⟨c, h | h⟩ := ValuationRing.cond a b
    · exact ⟨f c, Or.inl (by rw [← map_mul, h])⟩
    · exact ⟨f c, Or.inr (by rw [← map_mul, h])⟩⟩
  exact ⟨⟩

theorem valuationRing_localization_atPrime {R B : Type*} [CommRing R] [CommRing B]
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

theorem isPrincipalIdealRing_mvPolynomial_fin_one (K : Type*) [Field K] :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) K) :=
  let e : MvPolynomial (Fin 1) K ≃ₐ[K] Polynomial K := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective

theorem valuationRing_stalk {K : Type u} [Field K] {C : Scheme.{u}}
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

section Extend

variable {K : Type u} [Field K]

theorem fromSpecStalk_genericPoint_comp_eq {C : Scheme.{u}} [IsIntegral C]
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

theorem isSeparated_of_over {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K))
    [IsSeparated g] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

theorem existence_of_isProper {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] :
    ValuativeCriterion.Existence g := by
  have h : IsProper g := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1.existence

theorem exists_hom_of_generic {C Y : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] (y : Y ⟶ Spec (CommRingCat.of K))
    [IsProper y] (f : Spec C.functionField ⟶ Y)
    (hf : f ≫ y = C.fromSpecStalk (genericPoint C) ≫ c) :
    ∃ ψ : C ⟶ Y, ψ ≫ y = c ∧ C.fromSpecStalk (genericPoint C) ≫ ψ = f := by
  haveI : Y.IsSeparated := isSeparated_of_over y

  let f₀ : C.PartialMap Y := Scheme.PartialMap.ofFromSpecStalk c y f hf
  have hf₀ : f₀.hom ≫ y = f₀.domain.ι ≫ c := Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _
  have hη : genericPoint C ∈ f₀.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hf₀η : f₀.fromSpecStalkOfMem hη = f :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _

  have hdom : f₀.toRationalMap.domain = ⊤ := top_unique fun x _ =>
    mem_domain_of_valuationRing c y (existence_of_isProper y) f₀ hf₀ x (valuationRing_stalk c x)
  let g := f₀.toRationalMap.toPartialMap
  let ψ : C ⟶ Y := C.topIso.inv ≫ C.homOfLE hdom.ge ≫ g.hom

  have hι : f₀.domain.ι ≫ ψ = f₀.hom := by
    have key := f₀.toPartialMap_toRationalMap_restrict
    rw [Scheme.PartialMap.restrict_hom] at key
    rw [← key]
    change f₀.domain.ι ≫ C.topIso.inv ≫ C.homOfLE hdom.ge ≫ g.hom =
      C.homOfLE f₀.le_domain_toRationalMap ≫ g.hom
    simp only [← Category.assoc]
    congr 1
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.toIso_inv_ι, Category.comp_id]
  refine ⟨ψ, ?_, ?_⟩
  ·
    haveI : IsDominant f₀.domain.ι :=
      ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact f₀.dense_domain⟩
    refine ext_of_isDominant f₀.domain.ι ?_
    rw [reassoc_of% hι, hf₀]
  · rw [← Scheme.Opens.fromSpecStalkOfMem_ι f₀.domain (genericPoint C) hη, Category.assoc, hι]
    exact hf₀η

end Extend

section Ticket

theorem exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp [hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    exact PrimeSpectrum.ext hQcomap

theorem ringKrullDim_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  refine le_antisymm ?_ ?_
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    refine iSup_le fun l => ?_
    obtain ⟨L, hlen, -⟩ := exists_ltSeries_comap_eq_last hinj l
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  · change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)

theorem ringKrullDim_eq_of_ringHom_isIntegral_of_injective {R S : Type*} [CommRing R]
    [CommRing S] (f : R →+* S) (hint : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R = ringKrullDim S := by
  algebraize [f]
  exact ringKrullDim_eq_of_isIntegral_of_injective hinj

theorem ringKrullDim_mvPolynomial_fin (k : Type u) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_transcendental_finiteDimensional (k : Type u) (A : Type v) [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (hA : ringKrullDim A = 1) :
    ∃ x : FractionRing A, Transcendental k x ∧
      FiniteDimensional (IntermediateField.adjoin k ({x} : Set (FractionRing A)))
        (FractionRing A) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hs : s = 1 := by
    have h := ringKrullDim_eq_of_ringHom_isIntegral_of_injective g.toRingHom
      (RingHom.Finite.to_isIntegral hfin) hinj
    rw [ringKrullDim_mvPolynomial_fin, hA] at h
    have h' : ((s : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ) : ℕ∞) := h
    have h'' : (s : ℕ∞) = ((1 : ℕ) : ℕ∞) := WithBot.coe_injective h'
    exact_mod_cast h''
  subst hs
  set L := FractionRing A
  let R := MvPolynomial (Fin 1) k
  let x₀ : A := g (MvPolynomial.X 0)
  let x : L := algebraMap A L x₀

  have haeval : MvPolynomial.aeval (fun i : Fin 1 => g (MvPolynomial.X i)) = g := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have hind : AlgebraicIndependent k (fun i : Fin 1 => g (MvPolynomial.X i)) := by
    rw [algebraicIndependent_iff_injective_aeval, haeval]
    exact hinj
  have hx₀ : Transcendental k x₀ := hind.transcendental 0
  have hx : Transcendental k x :=
    (transcendental_algebraMap_iff (IsFractionRing.injective A L)).mpr hx₀
  refine ⟨x, hx, ?_⟩

  set E := IntermediateField.adjoin k ({x} : Set L)
  letI : Algebra R A := g.toRingHom.toAlgebra
  haveI : Module.Finite R A := hfin
  have hxE : x ∈ E := IntermediateField.mem_adjoin_simple_self k x
  have hgen : (IsScalarTower.toAlgHom k A L).comp g = MvPolynomial.aeval (fun _ : Fin 1 => x) := by
    apply MvPolynomial.algHom_ext
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp [x, x₀]
  have hrange : ∀ r : R, algebraMap A L (algebraMap R A r) ∈ (algebraMap E L).range := by
    intro r
    have h1 : algebraMap A L (algebraMap R A r) = MvPolynomial.aeval (fun _ : Fin 1 => x) r := by
      rw [← hgen]; rfl
    have h2 : MvPolynomial.aeval (fun _ : Fin 1 => x) r ∈ E.toSubalgebra := by
      have hr : MvPolynomial.aeval (fun _ : Fin 1 => x) r ∈
          (MvPolynomial.aeval (R := k) (fun _ : Fin 1 => x)).range := ⟨r, rfl⟩
      rw [← Algebra.adjoin_range_eq_range_aeval] at hr
      exact (Algebra.adjoin_le (by rintro _ ⟨_, rfl⟩; exact hxE) : _ ≤ E.toSubalgebra) hr
    rw [h1]
    exact ⟨⟨_, h2⟩, rfl⟩
  have hfd := RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
    (R := R) (S := A) (E := E) (K := L) (algebraMap A L) hrange
  have htop : IntermediateField.adjoin E (Set.range (algebraMap A L)) = ⊤ := by
    rw [eq_top_iff]
    intro l _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) l
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩)
  rw [htop] at hfd
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := E) (E := L)).toLinearEquiv

end Ticket

section Main

theorem main {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : ringKrullDim A = 1) (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (_ : IsProper c)
      (_ : SmoothOfRelativeDimension 1 c) (_ : IsIntegral C) (ψ : C ⟶ Y), ψ ≫ y = c ∧
      ∀ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ →
        ∃ p : Spec (CommRingCat.of k) ⟶ C, p ≫ c = 𝟙 _ ∧ p ≫ ψ = a ≫ φ := by

  let L := FractionRing A
  obtain ⟨M⟩ : Nonempty (CurveModel k L) :=
    CurveModel.nonempty_of_perfectField k L (exists_transcendental_finiteDimensional k A hA)

  let ρ : A →+* M.C.functionField := M.ffEquiv.toRingHom.comp (algebraMap A L)
  have hρ : Function.Injective ρ :=
    M.ffEquiv.injective.comp (IsFractionRing.injective A L)
  let f₀ : Spec M.C.functionField ⟶ Y := Spec.map (CommRingCat.ofHom ρ) ≫ φ
  have hf₀ : f₀ ≫ y = M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase := by
    rw [fromSpecStalk_genericPoint_comp_eq]
    simp only [f₀, Category.assoc, hφ, ← Spec.map_comp]
    congr 1
    ext a
    change M.ffEquiv (algebraMap A L (algebraMap k A a)) = baseToFunctionField M.toBase a
    rw [← IsScalarTower.algebraMap_apply, M.ffEquiv_algebraMap]
  obtain ⟨ψ, hψy, hψη⟩ := exists_hom_of_generic M.toBase y f₀ hf₀
  refine ⟨M.C, M.toBase, inferInstance, inferInstance, inferInstance, ψ, hψy, ?_⟩

  intro a ha

  haveI : UniversallyClosed ψ := by
    have : UniversallyClosed (ψ ≫ y) := by rw [hψy]; infer_instance
    exact UniversallyClosed.of_comp_of_isSeparated ψ y
  haveI : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase

  let pt : Spec M.C.functionField := IsLocalRing.closedPoint M.C.functionField
  let ηA : Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom ρ) pt
  let 𝔪 : Spec (CommRingCat.of A) := a (IsLocalRing.closedPoint k)

  have hgen : ψ (genericPoint M.C) = φ ηA := by
    have h1 : (M.C.fromSpecStalk (genericPoint M.C) ≫ ψ) pt = f₀ pt := by rw [hψη]
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at h1
    rw [h1]
    rfl

  have hsp : ηA ⤳ 𝔪 := by
    refine (PrimeSpectrum.le_iff_specializes (ηA : PrimeSpectrum A) 𝔪).mp ?_
    intro r hr
    have hr' : ρ r ∈ pt.asIdeal := hr
    have hr0 : ρ r = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp hr' (isUnit_iff_ne_zero.mpr hne)
    have : r = 0 := hρ (by rw [hr0, map_zero])
    rw [this]
    exact zero_mem _

  have hφy : (a ≫ φ) ≫ y = 𝟙 _ := by rw [Category.assoc, hφ, ha]
  have hclosed : IsClosed ({φ 𝔪} : Set Y) := by
    have h := (pointEquivClosedPoint y ⟨a ≫ φ, hφy⟩).2
    simpa [𝔪] using h

  have hmem : φ 𝔪 ∈ Set.range ψ := by
    have h1 : φ ηA ⤳ φ 𝔪 := hsp.map φ.continuous
    rw [← hgen] at h1
    exact h1.mem_closed ψ.isClosedMap.isClosed_range ⟨_, rfl⟩
  obtain ⟨x, hx⟩ := hmem

  obtain ⟨z, hxz, hz⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set M.C))
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hxz' : x ⤳ z := specializes_iff_mem_closure.mpr hxz
  have hψz : ψ z = φ 𝔪 := by
    have h1 : ψ x ⤳ ψ z := hxz'.map ψ.continuous
    rw [hx] at h1
    exact h1.mem_closed hclosed rfl

  refine ⟨pointOfClosedPoint M.toBase z hz, pointOfClosedPoint_comp _ _ _, ?_⟩
  refine ext_of_apply_closedPoint_eq y ?_ hφy ?_
  · rw [Category.assoc, hψy, pointOfClosedPoint_comp]
  · rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply, hψz]
    rfl

end Main

end P2mNormExt

end

open CategoryTheory AlgebraicGeometry in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : ringKrullDim A = 1) (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (_ : IsProper c)
      (_ : SmoothOfRelativeDimension 1 c) (_ : IsIntegral C) (ψ : C ⟶ Y), ψ ≫ y = c ∧
      ∀ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ →
        ∃ p : Spec (CommRingCat.of k) ⟶ C, p ≫ c = 𝟙 _ ∧ p ≫ ψ = a ≫ φ :=
  P2mNormExt.main y A hA φ hφ

end S_AlgebraicGeometry_exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one (solution)
