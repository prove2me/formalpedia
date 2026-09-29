-- Prove2me | solution 1 for AlgebraicGeometry.exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3d8cca89-e3e5-5b7c-a58b-ec7f092fc199

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_of_perfectField
import Theorems.Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

namespace P2mNormOpen

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

theorem fromSpecStalk_comp_eq {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) (z : C) :
    C.fromSpecStalk z ≫ c =
      Spec.map (CommRingCat.ofHom ((C.presheaf.germ ⊤ z trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))) := by
  refine ext_of_isAffine ?_
  set θ : K →+* C.presheaf.stalk z := (C.presheaf.germ ⊤ z trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have h1 : (Spec.map (CommRingCat.ofHom θ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom θ ≫
        (Scheme.ΓSpecIso (C.presheaf.stalk z)).inv := by
    rw [← Iso.inv_comp_eq]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  have h2 : CommRingCat.ofHom θ =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ z trivial := by
    ext a
    rfl
  have h3 : (Spec (C.presheaf.stalk z)).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk z)).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE _).op = 𝟙 (Opposite.op ⊤) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, h3, Category.comp_id, h1, h2]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

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

section Centre

variable {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L]

theorem exists_place_le_and_subset_nonunits (M : CurveModel k L) (A : Type u) [CommRing A]
    [Algebra k A] [Algebra A L] [IsScalarTower k A L]
    (hinj : Function.Injective (algebraMap A L)) (𝔪 : Ideal A) [h𝔪 : 𝔪.IsMaximal] (h𝔪0 : 𝔪 ≠ ⊥) :
    ∃ P : Place k L, (∀ a : A, algebraMap A L a ∈ P.toValuationSubring) ∧
      ∀ m ∈ 𝔪, algebraMap A L m ∈ P.toValuationSubring.nonunits := by
  classical
  set ι := algebraMap A L with hι

  let A' : Subring L := ι.range
  let e : A ≃+* A' := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩
  let I : Ideal A' := 𝔪.comap e.symm.toRingHom
  have hI : I ≠ ⊤ := Ideal.comap_ne_top _ h𝔪.ne_top
  obtain ⟨V, hAV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hAmem : ∀ a : A, ι a ∈ V := fun a => hAV ⟨a, rfl⟩
  have hmnon : ∀ m ∈ 𝔪, ι m ∈ V.nonunits := by
    intro m hm
    refine hIV ⟨e m, ?_, rfl⟩
    change e.symm.toRingHom (e m) ∈ 𝔪
    simpa using hm
  have hkV : ∀ a : k, algebraMap k L a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply k A L]; exact hAmem _

  obtain ⟨m, hm𝔪, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪0
  have hVtop : V ≠ ⊤ := by
    intro hV
    have h1 : ι m ∈ V.nonunits := hmnon m hm𝔪
    rw [ValuationSubring.mem_nonunits_iff_or] at h1
    rcases h1 with h1 | h1
    · exact hm0 (hinj (by rw [h1, map_zero]))
    · exact h1 (hV ▸ ValuationSubring.mem_top _)

  let C := M.C
  let kV : k →+* V := (algebraMap k L).codRestrict V.toSubring hkV
  let i₂ : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom kV)
  let eKL : C.presheaf.stalk (genericPoint C) ⟶ CommRingCat.of L :=
    CommRingCat.ofHom (M.ffEquiv.symm : C.functionField →+* L)
  let i₁ : Spec (CommRingCat.of L) ⟶ C := Spec.map eKL ≫ C.fromSpecStalk (genericPoint C)
  have hsq : i₁ ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ i₂ := by
    simp only [i₁, i₂, Category.assoc, fromSpecStalk_comp_eq, ← Spec.map_comp]
    congr 1
    ext a
    change M.ffEquiv.symm (baseToFunctionField M.toBase a) = algebraMap k L a
    rw [← M.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]
  obtain ⟨l, hl₁, hl₂⟩ := (existence_of_isProper M.toBase
    { R := V, K := L, i₁ := i₁, i₂ := i₂, commSq := ⟨hsq⟩ }).exists_lift

  let θ := Scheme.stalkClosedPointTo l
  haveI : IsLocalHom θ.hom := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo l).hom)
  have hθl : Spec.map θ ≫ C.fromSpecStalk _ = l := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  let g : C.presheaf.stalk (l (IsLocalRing.closedPoint V)) →+* L :=
    (M.ffEquiv.symm : C.functionField →+* L).comp
      (algebraMap (C.presheaf.stalk (l (IsLocalRing.closedPoint V))) C.functionField)
  have hg : Function.Injective g :=
    M.ffEquiv.symm.injective.comp
      (IsFractionRing.injective (C.presheaf.stalk (l (IsLocalRing.closedPoint V))) C.functionField)

  have hcompat : ∀ s, algebraMap V L (θ.hom s) = g s := by
    have key : θ ≫ CommRingCat.ofHom (algebraMap V L) =
        C.presheaf.stalkSpecializes (genericPoint_specializes (l (IsLocalRing.closedPoint V))) ≫
          eKL := by
      apply Spec.map_injective
      rw [← cancel_mono (C.fromSpecStalk (l (IsLocalRing.closedPoint V))), Spec.map_comp,
        Category.assoc, hθl, hl₁, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    intro s
    have h1 := congrArg (fun φ : C.presheaf.stalk _ ⟶ CommRingCat.of L => φ.hom s) key
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h1
    rw [h1]
    change M.ffEquiv.symm ((C.presheaf.stalkSpecializes
      (genericPoint_specializes (l (IsLocalRing.closedPoint V)))).hom s) = g s
    rw [← ofHom_algebraMap_stalk_functionField]
    rfl

  haveI hvz : ValuationRing (C.presheaf.stalk (l (IsLocalRing.closedPoint V))) :=
    valuationRing_stalk M.toBase _
  let W : ValuationSubring L :=
    { toSubring := g.range
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger
          (C.presheaf.stalk (l (IsLocalRing.closedPoint V))) (M.ffEquiv x) with ⟨s, hs⟩ | ⟨s, hs⟩
        · refine Or.inl ⟨s, ?_⟩
          change M.ffEquiv.symm (algebraMap _ _ s) = x
          rw [hs, RingEquiv.symm_apply_apply]
        · refine Or.inr ⟨s, ?_⟩
          change M.ffEquiv.symm (algebraMap _ _ s) = x⁻¹
          rw [hs, ← map_inv₀, RingEquiv.symm_apply_apply] }
  have hsub : W.toSubring ≤ V.toSubring := by
    rintro _ ⟨s, rfl⟩
    rw [← hcompat]
    exact (θ.hom s).2
  have hWV : W.toLocalSubring ≤ V.toLocalSubring := by
    refine ⟨hsub, ⟨?_⟩⟩
    intro a hu
    obtain ⟨s, hs⟩ : (a : L) ∈ g.range := a.2
    have e0 : Subring.inclusion hsub a = θ.hom s := by
      apply Subtype.ext
      change (a : L) = algebraMap V L (θ.hom s)
      rw [hcompat, hs]
    have hu0 : IsUnit (θ.hom s) := by
      have hu' := e0 ▸ hu
      exact hu'
    have hs' : IsUnit s := (isUnit_map_iff θ.hom s).mp hu0
    rw [show a = g.rangeRestrict s from Subtype.ext hs.symm]
    exact hs'.map _
  have hVW : V.toLocalSubring ≤ W.toLocalSubring := W.isMax_toLocalSubring hWV
  have hVsub : ∀ v : V, (v : L) ∈ g.range := fun v => hVW.1 v.2

  have hθbij : Function.Bijective θ.hom := by
    constructor
    · intro s t hst
      apply hg
      rw [← hcompat, ← hcompat, hst]
    · intro v
      obtain ⟨s, hs⟩ := hVsub v
      exact ⟨s, Subtype.ext ((hcompat s).trans hs)⟩
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  let eθ : C.presheaf.stalk (l (IsLocalRing.closedPoint V)) ≃+* V :=
    RingEquiv.ofBijective (θ.hom : C.presheaf.stalk (l (IsLocalRing.closedPoint V)) →+* V) hθbij
  haveI : IsNoetherianRing V := isNoetherianRing_of_ringEquiv _ eθ
  have hPIR : IsPrincipalIdealRing V :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain V).out 1 0).mp (show ValuationRing V from inferInstance)
  exact ⟨⟨V, hkV, hVtop, hPIR⟩, hAmem, hmnon⟩

end Centre

section Main

theorem isClosed_singleton_opens {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U)
    (hcl : IsClosed ({x} : Set X)) : IsClosed ({(⟨x, hx⟩ : U)} : Set U) := by
  have : ({(⟨x, hx⟩ : U)} : Set U) = U.ι ⁻¹' {x} := by
    ext u
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Scheme.Opens.ι_apply]
    constructor
    · rintro rfl; rfl
    · intro h; exact Subtype.ext h
  rw [this]
  exact hcl.preimage U.ι.continuous

theorem main {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated y] [LocallyOfFiniteType y] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : ringKrullDim A = 1) (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (_ : IsProper c)
      (_ : SmoothOfRelativeDimension 1 c) (_ : IsIntegral C) (U : C.Opens)
      (ψ : (U : Scheme.{u}) ⟶ Y), ψ ≫ y = U.ι ≫ c ∧
      ∀ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ →
        ∃ p : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}), p ≫ U.ι ≫ c = 𝟙 _ ∧ p ≫ ψ = a ≫ φ := by
  classical

  let L := FractionRing A
  obtain ⟨M⟩ : Nonempty (CurveModel k L) :=
    CurveModel.nonempty_of_perfectField k L (exists_transcendental_finiteDimensional k A hA)
  haveI : Y.IsSeparated := isSeparated_of_over y

  let ρ : A →+* M.C.functionField := (M.ffEquiv : L →+* M.C.functionField).comp (algebraMap A L)
  let f₀ : Spec M.C.functionField ⟶ Y := Spec.map (CommRingCat.ofHom ρ) ≫ φ
  have hf₀ : f₀ ≫ y = M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase := by
    rw [fromSpecStalk_comp_eq]
    simp only [f₀, Category.assoc, hφ, ← Spec.map_comp]
    congr 1
    ext a
    change M.ffEquiv (algebraMap A L (algebraMap k A a)) = baseToFunctionField M.toBase a
    rw [← IsScalarTower.algebraMap_apply, M.ffEquiv_algebraMap]
  let f₁ : M.C.PartialMap Y := Scheme.PartialMap.ofFromSpecStalk M.toBase y f₀ hf₀
  have hf₁ : f₁.hom ≫ y = f₁.domain.ι ≫ M.toBase := Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _
  have hη : genericPoint M.C ∈ f₁.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hf₁η : f₁.fromSpecStalkOfMem hη = f₀ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
  let r : M.C ⤏ Y := f₁.toRationalMap
  let U : M.C.Opens := r.toPartialMap.domain
  let ψ : (U : Scheme.{u}) ⟶ Y := r.toPartialMap.hom

  have hψ : ψ ≫ y = U.ι ≫ M.toBase := by
    have hle : f₁.domain ≤ U := f₁.le_domain_toRationalMap
    haveI : IsDominant (M.C.homOfLE hle) := Opens.isDominant_homOfLE f₁.dense_domain hle
    haveI : IsReduced (U : Scheme.{u}) := isReduced_of_isOpenImmersion U.ι
    apply ext_of_isDominant (M.C.homOfLE hle)
    have key : M.C.homOfLE hle ≫ ψ = f₁.hom := by
      have := f₁.toPartialMap_toRationalMap_restrict
      rwa [Scheme.PartialMap.restrict_hom] at this
    rw [reassoc_of% key, hf₁, Scheme.homOfLE_ι_assoc]
  refine ⟨M.C, M.toBase, inferInstance, inferInstance, inferInstance, U, ψ, hψ, ?_⟩

  intro a ha
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let 𝔪pt : Spec (CommRingCat.of A) := a (IsLocalRing.closedPoint k)
  haveI h𝔪 : 𝔪pt.asIdeal.IsMaximal := by
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    exact ((pointEquivClosedPoint (Spec.map (CommRingCat.ofHom (algebraMap k A)))) ⟨a, ha⟩).2
  have h𝔪0 : 𝔪pt.asIdeal ≠ ⊥ := by
    intro hbot
    have h1 : (1 : WithBot ℕ∞) ≤ ringKrullDim A := by rw [hA]
    rw [ringKrullDim, Order.one_le_krullDim_iff] at h1
    obtain ⟨p, q, hpq⟩ := h1
    have hp : p.asIdeal = ⊥ := by
      have := h𝔪.eq_of_le p.isPrime.ne_top (hbot ▸ bot_le)
      rw [← this, hbot]
    have hq : q.asIdeal = ⊥ := by
      have := h𝔪.eq_of_le q.isPrime.ne_top (hbot ▸ bot_le)
      rw [← this, hbot]
    exact (ne_of_lt hpq) (PrimeSpectrum.ext (hp.trans hq.symm))

  obtain ⟨P, hAP, hmP⟩ := exists_place_le_and_subset_nonunits M A
    (IsFractionRing.injective A L) 𝔪pt.asIdeal h𝔪0
  obtain ⟨x, hxP⟩ := M.placeOfPoint_bijective.2 P
  let gx : M.C.presheaf.stalk x.1 →+* L :=
    (M.ffEquiv.symm : M.C.functionField →+* L).comp
      (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)
  have hgx : Function.Injective gx :=
    M.ffEquiv.symm.injective.comp (IsFractionRing.injective (M.C.presheaf.stalk x.1) M.C.functionField)
  have hst : gx.range = P.toValuationSubring.toSubring := by
    have := M.range_stalk_eq x
    rw [hxP] at this
    exact this
  have hAr : ∀ a' : A, algebraMap A L a' ∈ gx.range := fun a' => by rw [hst]; exact hAP a'
  have hVr : ∀ s, gx s ∈ P.toValuationSubring := fun s => by
    have : gx s ∈ gx.range := ⟨s, rfl⟩
    rw [hst] at this
    exact this

  let eg : M.C.presheaf.stalk x.1 ≃+* gx.range := RingEquiv.ofBijective gx.rangeRestrict
    ⟨fun s t h => hgx (congrArg Subtype.val h), gx.rangeRestrict_surjective⟩
  let α : A →+* M.C.presheaf.stalk x.1 :=
    eg.symm.toRingHom.comp ((algebraMap A L).codRestrict gx.range hAr)
  have hα : ∀ a' : A, gx (α a') = algebraMap A L a' := fun a' => by
    have h1 : eg (eg.symm ((algebraMap A L).codRestrict gx.range hAr a')) =
        (algebraMap A L).codRestrict gx.range hAr a' := eg.apply_symm_apply _
    exact congrArg Subtype.val h1

  have hcomap : Ideal.comap α (IsLocalRing.maximalIdeal _) = 𝔪pt.asIdeal := by
    symm
    refine h𝔪.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) ?_
    intro m hm
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    let gV : M.C.presheaf.stalk x.1 →+* P.toValuationSubring :=
      gx.codRestrict P.toValuationSubring.toSubring hVr
    have hu' : IsUnit (gV (α m)) := hu.map gV
    have hnon : (gV (α m) : L) ∈ P.toValuationSubring.nonunits := by
      change gx (α m) ∈ _
      rw [hα]
      exact hmP m hm
    rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal] at hnon
    exact hnon hu'

  let lx : Spec (M.C.presheaf.stalk x.1) ⟶ Y := Spec.map (CommRingCat.ofHom α) ≫ φ
  have hgerm : ∀ t : k, gx ((M.C.presheaf.germ ⊤ x.1 trivial).hom
      (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom t))) = algebraMap k L t := by
    intro t
    change M.ffEquiv.symm (algebraMap _ M.C.functionField ((M.C.presheaf.germ ⊤ x.1 trivial).hom _)) = _
    have h1 : algebraMap (M.C.presheaf.stalk x.1) M.C.functionField
        ((M.C.presheaf.germ ⊤ x.1 trivial).hom
          (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom t))) =
        baseToFunctionField M.toBase t := by
      change (CommRingCat.ofHom (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)).hom
        ((M.C.presheaf.germ ⊤ x.1 trivial).hom _) = _
      rw [ofHom_algebraMap_stalk_functionField, ← CommRingCat.comp_apply,
        TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    rw [h1, ← M.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]
  have hlx : lx ≫ y = M.C.fromSpecStalk x.1 ≫ M.toBase := by
    simp only [lx, Category.assoc, hφ, ← Spec.map_comp, fromSpecStalk_comp_eq]
    congr 1
    ext t
    apply hgx
    change gx (α (algebraMap k A t)) = gx ((M.C.presheaf.germ ⊤ x.1 trivial).hom
      (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom t)))
    rw [hα, hgerm, ← IsScalarTower.algebraMap_apply]

  let g₁ : M.C.PartialMap Y := Scheme.PartialMap.ofFromSpecStalk M.toBase y lx hlx
  have hxg₁ : x.1 ∈ g₁.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hg₁x : g₁.fromSpecStalkOfMem hxg₁ = lx :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
  have hg₁r : g₁.toRationalMap = r := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq_of_mem g₁ hxg₁, hg₁x,
      partialMap_fromFunctionField_eq_of_mem f₁ hη, hf₁η]
    have hspec : M.C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint M.C)) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    simp only [lx, f₀, ← Category.assoc, ← Spec.map_comp]
    congr 2
    rw [hspec, Category.comp_id]
    ext a'
    apply M.ffEquiv.symm.injective
    change M.ffEquiv.symm ((M.C.presheaf.stalkSpecializes (genericPoint_specializes x.1)).hom (α a')) =
      M.ffEquiv.symm (M.ffEquiv (algebraMap A L a'))
    rw [RingEquiv.symm_apply_apply, ← hα a', ← ofHom_algebraMap_stalk_functionField]
    rfl
  have hxU : x.1 ∈ U := by
    have : x.1 ∈ g₁.toRationalMap.domain := g₁.le_domain_toRationalMap hxg₁
    rw [hg₁r] at this
    exact this

  have hψx : ψ ⟨x.1, hxU⟩ = φ 𝔪pt := by
    have key : ∀ (r' : M.C ⤏ Y) (hr : g₁.toRationalMap = r') (h : g₁.domain ≤ r'.toPartialMap.domain),
        M.C.homOfLE h ≫ r'.toPartialMap.hom = g₁.hom := by
      rintro _ rfl h
      have := g₁.toPartialMap_toRationalMap_restrict
      rwa [Scheme.PartialMap.restrict_hom] at this
    have hle : g₁.domain ≤ U := fun z hz => by
      have : z ∈ g₁.toRationalMap.domain := g₁.le_domain_toRationalMap hz
      rw [hg₁r] at this
      exact this
    have h1 : ψ ⟨x.1, hxU⟩ = (M.C.homOfLE hle ≫ ψ) ⟨x.1, hxg₁⟩ := by
      rw [Scheme.Hom.comp_apply, Scheme.homOfLE_apply']
    have h2' : g₁.domain.ι (g₁.domain.fromSpecStalkOfMem x.1 hxg₁ (IsLocalRing.closedPoint _)) = x.1 := by
      rw [← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]
    have h2 : (⟨x.1, hxg₁⟩ : g₁.domain) =
        g₁.domain.fromSpecStalkOfMem x.1 hxg₁ (IsLocalRing.closedPoint _) := by
      apply Subtype.ext
      rw [Scheme.Opens.ι_apply] at h2'
      exact h2'.symm
    rw [h1, key r hg₁r hle, h2, ← Scheme.Hom.comp_apply]
    change (g₁.fromSpecStalkOfMem hxg₁) _ = _
    rw [hg₁x, Scheme.Hom.comp_apply]
    congr 1
    rw [Spec.map_apply]
    apply PrimeSpectrum.ext
    exact hcomap

  have hxcl : IsClosed ({(⟨x.1, hxU⟩ : U)} : Set U) := isClosed_singleton_opens U x.1 hxU x.2
  refine ⟨pointOfClosedPoint (U.ι ≫ M.toBase) ⟨x.1, hxU⟩ hxcl, pointOfClosedPoint_comp _ _ _, ?_⟩
  have hφy : (a ≫ φ) ≫ y = 𝟙 _ := by rw [Category.assoc, hφ, ha]
  apply ext_of_apply_closedPoint_eq y _ hφy
  · rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply, hψx, Scheme.Hom.comp_apply]
  · rw [Category.assoc, hψ, pointOfClosedPoint_comp]

end Main

end P2mNormOpen

end

open CategoryTheory AlgebraicGeometry in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated y] [LocallyOfFiniteType y] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : ringKrullDim A = 1) (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (_ : IsProper c)
      (_ : SmoothOfRelativeDimension 1 c) (_ : IsIntegral C) (U : C.Opens)
      (ψ : (U : Scheme.{u}) ⟶ Y), ψ ≫ y = U.ι ≫ c ∧
      ∀ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ →
        ∃ p : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}), p ≫ U.ι ≫ c = 𝟙 _ ∧ p ≫ ψ = a ≫ φ :=
  P2mNormOpen.main y A hA φ hφ

end S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one (solution)
