-- Prove2me | solution 1 for AlgebraicGeometry.exists_tendsto_appLE_of_isProper_of_smoothOfRelativeDimension_one_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/bab26167-ed69-5f7c-88c8-514ee06dcfbb

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_exists_strictMono_forall_tendsto_evalAt_complex
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_tendsto_appLE_of_isProper_of_smoothOfRelativeDimension_one_complex
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve Filter Topology

namespace CompactValuesComplexCurve

section Places

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isRational_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem evalAt_eq_of_sub_algebraMap_mem_nonunits (v : Place K F) {f : F} (c : K)
    (hf : f ∈ v.toValuationSubring)
    (h : f - algebraMap K F c ∈ v.toValuationSubring.nonunits) : v.evalAt f = c := by
  rw [v.evalAt_of_mem hf]
  have hc : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : (⟨f, hf⟩ : v.toValuationSubring) - ⟨algebraMap K F c, hc⟩ ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    have h' : ((⟨f - algebraMap K F c, sub_mem hf hc⟩ : v.toValuationSubring) : F) ∈
        v.toValuationSubring.nonunits := h
    rw [ValuationSubring.coe_mem_nonunits_iff] at h'
    exact h'
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ =
      IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F c, hc⟩ := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hsub
  rw [hres]
  exact v.residueInv_algebraMap c

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases hf0 : f = 0
  · rw [hf0, Place.ord_zero]
  · have h1 : v.adicValuation f ≤ 1 := by
      have h := (v.adicValuation_coe ⟨f, hf⟩).trans_le (v.heightOneSpectrum.intValuation_le_one ⟨f, hf⟩)
      simpa using h
    have h2 : v.adicValuation f = WithZero.exp (-v.ord f) := by
      unfold Place.ord
      rw [neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf0)]
    rw [h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0]; exact zero_mem _
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
    rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
    exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem exists_mem_and_not_mem {v w : Place K F} (hne : v ≠ w) :
    ∃ x : F, x ∈ v.toValuationSubring ∧ x ∉ w.toValuationSubring := by
  by_contra hcon
  push Not at hcon
  have hle : v.toValuationSubring ≤ w.toValuationSubring := fun x hx => hcon x hx
  apply hne
  apply Place.ext
  set P : Ideal v.toValuationSubring := v.toValuationSubring.idealOfLE w.toValuationSubring hle with hP
  have hPw : v.toValuationSubring.ofPrime P = w.toValuationSubring :=
    ValuationSubring.ofPrime_idealOfLE _ _ hle
  by_cases hbot : P = ⊥
  · exfalso
    apply w.ne_top'
    rw [← hPw]
    haveI : (⊥ : Ideal v.toValuationSubring).IsPrime := Ideal.isPrime_bot
    have : v.toValuationSubring.ofPrime P = v.toValuationSubring.ofPrime ⊥ := by
      congr 1
    rw [this]
    exact ValuationSubring.ofPrime_bot _
  · have hmax : P = IsLocalRing.maximalIdeal v.toValuationSubring := by
      haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hbot
      exact IsLocalRing.eq_maximalIdeal inferInstance
    rw [← hPw]
    have : v.toValuationSubring.ofPrime P =
        v.toValuationSubring.ofPrime (IsLocalRing.maximalIdeal v.toValuationSubring) := by
      congr 1
    rw [this, ValuationSubring.ofPrime_top]

end Places

section Values

universe u

variable {K : Type u} [Field K]

def value {Y : Scheme.{u}} (q : Spec (CommRingCat.of K) ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) : K :=
  by classical exact if h : ⊤ ≤ q ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of K)).hom (q.appLE U ⊤ h s) else 0

theorem value_of_le {Y : Scheme.{u}} (q : Spec (CommRingCat.of K) ⟶ Y) (U : Y.Opens) (s : Γ(Y, U))
    (h : ⊤ ≤ q ⁻¹ᵁ U) :
    value q U s = (Scheme.ΓSpecIso (CommRingCat.of K)).hom (q.appLE U ⊤ h s) := by
  classical
  unfold value
  rw [dif_pos h]

theorem appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

theorem top_le_preimage_iff {Y : Scheme.{u}} (q : Spec (CommRingCat.of K) ⟶ Y) (U : Y.Opens) :
    ⊤ ≤ q ⁻¹ᵁ U ↔ q.base (IsLocalRing.closedPoint K) ∈ U := by
  constructor
  · intro h
    exact h (Set.mem_univ (IsLocalRing.closedPoint K))
  · intro h p _
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst hp
    exact h

end Values

theorem main (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of ℂ)) [IsIntegral Y] [IsProper πY]
    [SmoothOfRelativeDimension 1 πY]
    (σ : ℕ → {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _}) :
    ∃ (τ : {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _}) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ U : Y.Opens, ⊤ ≤ τ.1 ⁻¹ᵁ U →
        (∀ᶠ n in atTop, ⊤ ≤ (σ (φ n)).1 ⁻¹ᵁ U) ∧
        ∀ s : Γ(Y, U), Tendsto (fun n => value (σ (φ n)).1 U s) atTop (𝓝 (value τ.1 U s)) := by
  classical
  letI hAlg : Algebra ℂ Y.functionField := (baseToFunctionField πY).toAlgebra
  obtain ⟨hco, hess, M, e, he, hgerm⟩ :=
    AlgebraicGeometry.SmoothProperCurve.exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed ℂ Y πY

  obtain ⟨t, ht, hfd, -⟩ :=
    (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional
      (K := ℂ) (F := Y.functionField)).mp hco
  have hfg : ∃ x : Y.functionField, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set Y.functionField)) Y.functionField :=
    ⟨t, ht, hfd⟩

  have hinv : e.inv ≫ M.toBase = πY := by rw [← he, Iso.inv_hom_id_assoc]
  let z : {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _} →
      {p : Spec (CommRingCat.of ℂ) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
    fun q => ⟨q.1 ≫ e.inv, by rw [Category.assoc, hinv, q.2]⟩
  have hz1 : ∀ q : {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _}, (z q).1 ≫ e.hom = q.1 := by
    intro q
    show (q.1 ≫ e.inv) ≫ e.hom = q.1
    simp
  let pl : {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _} → Place ℂ Y.functionField :=
    fun q => M.pointEquivPlace (z q)
  have hz_inj : Function.Injective z := by
    intro q q' h
    apply Subtype.ext
    rw [← hz1 q, ← hz1 q', h]
  have hpl_inj : Function.Injective pl := M.pointEquivPlace.injective.comp hz_inj

  obtain ⟨v, φ, hφ, hconv⟩ :=
    AlgebraicCurve.Place.exists_strictMono_forall_tendsto_evalAt_complex Y.functionField hfg (fun n => pl (σ n))

  let τ : {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _} :=
    ⟨(M.pointEquivPlace.symm v).1 ≫ e.hom, by rw [Category.assoc, he, (M.pointEquivPlace.symm v).2]⟩
  have hzτ : z τ = M.pointEquivPlace.symm v := by
    apply Subtype.ext
    show ((M.pointEquivPlace.symm v).1 ≫ e.hom) ≫ e.inv = _
    simp
  have hplτ : pl τ = v := by
    show M.pointEquivPlace (z τ) = v
    rw [hzτ, Equiv.apply_symm_apply]
  refine ⟨τ, φ, hφ, fun U hU => ?_⟩
  have hτU : τ.1.base (IsLocalRing.closedPoint ℂ) ∈ U := (top_le_preimage_iff τ.1 U).mp hU
  haveI hUne : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hτU⟩⟩

  have hV : ∀ (q : {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _}) (hq : ⊤ ≤ q.1 ⁻¹ᵁ U) (s : Γ(Y, U)),
      Y.germToFunctionField U s ∈ (pl q).toValuationSubring ∧
      Y.germToFunctionField U s - algebraMap ℂ Y.functionField (value q.1 U s) ∈
        (pl q).toValuationSubring.nonunits := by
    intro q hq s
    have hqU : ((z q).1 ≫ e.hom).base (IsLocalRing.closedPoint ℂ) ∈ U := by
      rw [hz1 q]; exact (top_le_preimage_iff q.1 U).mp hq
    have hq' : ⊤ ≤ (z q).1 ⁻¹ᵁ (e.hom ⁻¹ᵁ U) := by
      rw [top_le_preimage_iff]
      simpa using hqU
    haveI : Nonempty (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ U)) :=
      ⟨⟨(z q).1.base (IsLocalRing.closedPoint ℂ), (top_le_preimage_iff _ _).mp hq'⟩⟩
    obtain ⟨hmem, hnon⟩ :=
      AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
        M (e.hom ⁻¹ᵁ U) ((e.hom.app U).hom s) (z q) hq'
    rw [hgerm U s] at hmem hnon
    refine ⟨hmem, ?_⟩
    have h4 : q.1.appLE U ⊤ hq = e.hom.app U ≫ (z q).1.appLE (e.hom ⁻¹ᵁ U) ⊤ hq' :=
      (appLE_eq_of_eq (hz1 q) U ⊤ hq').symm.trans (Scheme.Hom.comp_appLE _ _ _ _ _)
    have hval : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((z q).1.appLE (e.hom ⁻¹ᵁ U) ⊤ hq' ((e.hom.app U).hom s)) = value q.1 U s := by
      rw [value_of_le q.1 U s hq, h4]
      rfl
    rw [hval] at hnon
    exact hnon

  have hZ : ((U : Set Y)ᶜ).Finite := AlgebraicCurve.finite_compl_of_isOpen πY U ⟨_, hτU⟩
  let g : {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _} → Y := fun q => q.1.base (IsLocalRing.closedPoint ℂ)
  have hg_inj : Function.Injective g := fun q q' h =>
    Subtype.ext (ext_of_apply_closedPoint_eq πY q.2 q'.2 h)
  have hQ : (g ⁻¹' ((U : Set Y)ᶜ)).Finite := hZ.preimage hg_inj.injOn
  have hev : ∀ q' ∈ g ⁻¹' ((U : Set Y)ᶜ), ∀ᶠ n in atTop, σ (φ n) ≠ q' := by
    intro q' hq'
    have hne : v ≠ pl q' := by
      intro h
      apply hq'
      have hq'τ : q' = τ := hpl_inj (by rw [hplτ]; exact h.symm)
      rw [hq'τ]
      exact hτU
    obtain ⟨x, hxv, hxq'⟩ := exists_mem_and_not_mem hne
    have h1 := (hconv x (ord_nonneg_of_mem v hxv)).1
    filter_upwards [h1] with n hn
    intro heq
    apply hxq'
    rw [← heq]
    exact mem_of_ord_nonneg _ hn
  have hall : ∀ᶠ n in atTop, ∀ q' ∈ g ⁻¹' ((U : Set Y)ᶜ), σ (φ n) ≠ q' := hQ.eventually_all.mpr hev
  have hmemU : ∀ᶠ n in atTop, ⊤ ≤ (σ (φ n)).1 ⁻¹ᵁ U := by
    filter_upwards [hall] with n hn
    rw [top_le_preimage_iff]
    by_contra hnot
    exact hn (σ (φ n)) hnot rfl

  refine ⟨hmemU, fun s => ?_⟩
  obtain ⟨hxτ, hxτ'⟩ := hV τ hU s
  rw [hplτ] at hxτ hxτ'
  have hlim := (hconv (Y.germToFunctionField U s) (ord_nonneg_of_mem v hxτ)).2
  have hvval : v.evalAt (Y.germToFunctionField U s) = value τ.1 U s :=
    evalAt_eq_of_sub_algebraMap_mem_nonunits v _ hxτ hxτ'
  rw [hvval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hmemU] with n hn
  obtain ⟨h1, h2⟩ := hV (σ (φ n)) hn s
  exact evalAt_eq_of_sub_algebraMap_mem_nonunits _ _ h1 h2

section General

universe u

variable {K : Type u} [Field K]

theorem value_comp {X Y : Scheme.{u}} (q : Spec (CommRingCat.of K) ⟶ X) (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) :
    value (q ≫ f) U s = value q (f ⁻¹ᵁ U) ((f.app U).hom s) := by
  classical
  by_cases h : ⊤ ≤ (q ≫ f) ⁻¹ᵁ U
  · have h' : ⊤ ≤ q ⁻¹ᵁ (f ⁻¹ᵁ U) := h
    rw [value_of_le _ _ _ h, value_of_le _ _ _ h', Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ q ⁻¹ᵁ (f ⁻¹ᵁ U) := h
    unfold value
    rw [dif_neg h, dif_neg h']

end General

theorem isOpen_connectedComponent_of_noetherianSpace {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) := by
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have hcompl : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | Disjoint Z (connectedComponent x)}, Z := by
    ext y
    constructor
    · intro hy
      refine Set.mem_iUnion₂.mpr ⟨irreducibleComponent y,
        ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩, mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro z hzZ hzx
      apply hy
      have hsub : irreducibleComponent y ⊆ connectedComponent x := by
        have h1 := isIrreducible_irreducibleComponent.2.isPreconnected.subset_connectedComponent hzZ
        rw [← connectedComponent_eq hzx] at h1
        exact h1
      exact hsub mem_irreducibleComponent
    · intro hy hyx
      obtain ⟨Z, hZ, hyZ⟩ := Set.mem_iUnion₂.mp hy
      exact Set.disjoint_left.mp hZ.2 hyZ hyx
  rw [← isClosed_compl_iff, hcompl]
  exact Set.Finite.isClosed_biUnion (hfin.subset fun Z hZ => hZ.1)
    fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1

theorem main_general (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper πY]
    [SmoothOfRelativeDimension 1 πY]
    (σ : ℕ → {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _}) :
    ∃ (τ : {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _}) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ U : Y.Opens, ⊤ ≤ τ.1 ⁻¹ᵁ U →
        (∀ᶠ n in atTop, ⊤ ≤ (σ (φ n)).1 ⁻¹ᵁ U) ∧
        ∀ s : Γ(Y, U), Tendsto (fun n => value (σ (φ n)).1 U s) atTop (𝓝 (value τ.1 U s)) := by
  classical
  haveI : Smooth πY := SmoothOfRelativeDimension.smooth 1 πY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian πY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace πY
  haveI : IsNoetherian Y := {}
  let g : {q : Spec (CommRingCat.of ℂ) ⟶ Y // q ≫ πY = 𝟙 _} → Y := fun q => q.1.base (IsLocalRing.closedPoint ℂ)

  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)
  haveI := hfin.to_subtype
  have hcomp : ∀ n, ∃ Z ∈ irreducibleComponents Y, g (σ n) ∈ Z := fun n =>
    ⟨_, irreducibleComponent_mem_irreducibleComponents _, mem_irreducibleComponent⟩
  choose Zn hZn hgZn using hcomp
  obtain ⟨⟨Z₀, hZ₀⟩, hinf⟩ :=
    Finite.exists_infinite_fiber (fun n : ℕ => (⟨Zn n, hZn n⟩ : irreducibleComponents Y))
  have hfreq : ∃ᶠ n in atTop, Zn n = Z₀ := by
    rw [Nat.frequently_atTop_iff_infinite]
    refine (Set.infinite_coe_iff.mp hinf).mono ?_
    intro n hn
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk.injEq] at hn
    exact hn
  obtain ⟨ψ, hψ, hψZ⟩ := Filter.extraction_of_frequently_atTop hfreq

  set x₀ : Y := g (σ (ψ 0)) with hx₀
  have hCopen : IsOpen (connectedComponent x₀) := isOpen_connectedComponent_of_noetherianSpace x₀
  have hx₀Z : x₀ ∈ Z₀ := by rw [hx₀, ← hψZ 0]; exact hgZn (ψ 0)
  have hZC : Z₀ ⊆ connectedComponent x₀ := by
    have h1 := hZ₀.1.2.isPreconnected.subset_connectedComponent hx₀Z
    exact h1
  have hσC : ∀ n, g (σ (ψ n)) ∈ connectedComponent x₀ := fun n =>
    hZC (by rw [← hψZ n]; exact hgZn (ψ n))
  let U₀ : Y.Opens := ⟨connectedComponent x₀, hCopen⟩
  haveI : Nonempty (Scheme.Opens.toScheme U₀) := ⟨⟨x₀, mem_connectedComponent⟩⟩
  haveI : PreconnectedSpace (Scheme.Opens.toScheme U₀) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
  haveI : Smooth (U₀.ι ≫ πY) := MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  haveI hint : IsIntegral (Scheme.Opens.toScheme U₀) :=
    AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace (U₀.ι ≫ πY)
  haveI : IsClosedImmersion U₀.ι :=
    IsClosedImmersion.of_isPreimmersion U₀.ι (by rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  haveI : IsProper (U₀.ι ≫ πY) := inferInstance
  haveI : SmoothOfRelativeDimension 1 (U₀.ι ≫ πY) := by
    have h := AlgebraicGeometry.smoothOfRelativeDimension_comp (n := 0) (m := 1) (f := U₀.ι) πY
    simpa using h

  have hrange : ∀ n, Set.range (σ (ψ n)).1.base ⊆ Set.range U₀.ι.base := by
    intro n
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    rw [Scheme.Opens.range_ι]
    exact hσC n
  let σ' : ℕ → {q : Spec (CommRingCat.of ℂ) ⟶ Scheme.Opens.toScheme U₀ // q ≫ (U₀.ι ≫ πY) = 𝟙 _} := fun n =>
    ⟨IsOpenImmersion.lift U₀.ι (σ (ψ n)).1 (hrange n), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (σ (ψ n)).2⟩
  have hσ' : ∀ n, (σ' n).1 ≫ U₀.ι = (σ (ψ n)).1 := fun n => IsOpenImmersion.lift_fac _ _ _
  obtain ⟨τ', φ, hφ, hmain⟩ := main (Scheme.Opens.toScheme U₀) (U₀.ι ≫ πY) σ'
  refine ⟨⟨τ'.1 ≫ U₀.ι, by rw [Category.assoc]; exact τ'.2⟩, ψ ∘ φ, hψ.comp hφ, fun U hU => ?_⟩
  have hU' : ⊤ ≤ τ'.1 ⁻¹ᵁ (U₀.ι ⁻¹ᵁ U) := hU
  obtain ⟨hmem, hval⟩ := hmain (U₀.ι ⁻¹ᵁ U) hU'
  refine ⟨?_, fun s => ?_⟩
  · filter_upwards [hmem] with n hn
    show ⊤ ≤ (σ (ψ (φ n))).1 ⁻¹ᵁ U
    rw [← hσ' (φ n)]
    exact hn
  · show Tendsto (fun n => value (σ (ψ (φ n))).1 U s) atTop (𝓝 (value (τ'.1 ≫ U₀.ι) U s))
    rw [value_comp]
    refine (hval ((U₀.ι.app U).hom s)).congr fun n => ?_
    show value (σ' (φ n)).1 (U₀.ι ⁻¹ᵁ U) ((U₀.ι.app U).hom s) = value (σ (ψ (φ n))).1 U s
    rw [← hσ' (φ n), value_comp]

end CompactValuesComplexCurve

open CategoryTheory AlgebraicGeometry NeronModelInfra Filter Topology in
theorem solution
    (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper g] (hsm : SmoothOfRelativeDimension 1 g)
    (P : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) :
    ∃ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ (U : Y.Opens), IsAffineOpen U → ∀ (hQ : ⊤ ≤ Q.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P (φ n)).1 ⁻¹ᵁ U,
          ∀ f : Γ(Y, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P (φ n)).1.appLE U ⊤ (hP n h)) f) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hQ) f))) := by
  classical
  haveI := hsm
  obtain ⟨τ, φ, hφ, hmain⟩ := CompactValuesComplexCurve.main_general Y g P
  refine ⟨τ, φ, hφ, fun U _ hQ => ?_⟩
  obtain ⟨hmem, hval⟩ := hmain U hQ
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hmem
  refine ⟨n₀, hn₀, fun f => ?_⟩
  have h1 := hval f
  rw [CompactValuesComplexCurve.value_of_le τ.1 U f hQ] at h1
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
  rw [dif_pos hn, CompactValuesComplexCurve.value_of_le _ U f (hn₀ n hn)]

end
end S_AlgebraicGeometry_exists_tendsto_appLE_of_isProper_of_smoothOfRelativeDimension_one_complex
end P2MW
export P2MW.S_AlgebraicGeometry_exists_tendsto_appLE_of_isProper_of_smoothOfRelativeDimension_one_complex (solution)
