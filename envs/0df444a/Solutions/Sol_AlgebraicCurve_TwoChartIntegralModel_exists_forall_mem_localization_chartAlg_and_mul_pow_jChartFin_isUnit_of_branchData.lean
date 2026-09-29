-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/55d26bab-3cd2-56e3-8d7c-052cba0b42dc

import Mathlib
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_TwoChartCech_Sections_finite_H1_ofSubmodules_of_forall_exists_pow_mul_mem
import Theorems.Thm_AlgebraicCurve_exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt
import Theorems.Thm_Module_exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero
import Theorems.Thm_IsFractionRing_exists_pow_mul_mem_colon_and_surjective_restrict_of_branchData
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower
import Theorems.Thm_AlgebraicCurve_linearIndependent_pow_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace PenLift

section Charts
variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (f : F) [Fact (f ≠ 0)]

theorem chartAlgFin_le_chartAlgMid : chartAlgFin R F f ≤ chartAlgMid R F f :=
  chartAlg_mono R F (sFin_subset F f)

theorem chartAlgInf_le_chartAlgMid : chartAlgInf R F f ≤ chartAlgMid R F f :=
  chartAlg_mono R F (sInf_subset F f)

theorem exists_pow_mul_mem_chartAlgFin_of_mem_chartAlgMid {z : F} (hz : z ∈ chartAlgMid R F f) :
    ∃ k : ℕ, f ^ k * z ∈ chartAlgFin R F f := by
  have hz' : z ∈ chartAlg R F (insert f⁻¹ {f}) := by
    rw [Set.pair_comm]; exact hz
  exact exists_pow_mul_mem_chartAlg (Set.mem_singleton f) (j_ne_zero f) hz'

theorem exists_pow_mul_mem_chartAlgInf_of_mem_chartAlgMid {z : F} (hz : z ∈ chartAlgMid R F f) :
    ∃ k : ℕ, f⁻¹ ^ k * z ∈ chartAlgInf R F f := by
  have hz' : z ∈ chartAlg R F (insert (f⁻¹)⁻¹ {f⁻¹}) := by
    rw [inv_inv]; exact hz
  exact exists_pow_mul_mem_chartAlg (Set.mem_singleton f⁻¹) (inv_ne_zero (j_ne_zero f)) hz'

end Charts

section Colon
variable {A : Type u} [CommRing A]

theorem pow_card_mem_prod {ι : Type u} [Fintype ι] (I : ι → Ideal A) (t : A) (ht : ∀ i, t ∈ I i) :
    t ^ Fintype.card ι ∈ ∏ i, I i := by
  rw [← Finset.card_univ, ← Finset.prod_const]
  exact Ideal.prod_mem_prod (fun i _ => ht i)

theorem mem_of_branchData {ι : Type u} (𝔪 : ι → Ideal A) (h𝔪 : ∀ i, 𝔪 i ≠ ⊤) (t : A) (I : ι → Ideal A)
    (hI : ∀ i (a : A), a ∈ I i ↔ ∃ s : A, s ∉ 𝔪 i ∧ s * a ∈ Ideal.span {t}) (i : ι) : t ∈ I i :=
  (hI i t).mpr ⟨1, fun h => h𝔪 i ((Ideal.eq_top_iff_one _).mpr h), by
    rw [one_mul]; exact Ideal.mem_span_singleton_self _⟩

end Colon

section ColonChart
variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (f : F) [Fact (f ≠ 0)]

theorem exists_mul_pow_eq_of_forall_mem_prod_pow {ι : Type u} [Fintype ι]
    (I : ι → Ideal ↥(chartAlgFin R F f)) (hfI : ∀ i, jChartFin R F f ∈ I i) (n : ℕ) (g : F)
    (hg : ∀ a ∈ (∏ i, I i) ^ n, ∃ b : ↥(chartAlgFin R F f), g * (a : F) = (b : F)) :
    ∃ b : ↥(chartAlgFin R F f), g * f ^ (Fintype.card ι * n) = (b : F) := by
  obtain ⟨b, hb⟩ := hg _ (Ideal.pow_mem_pow (pow_card_mem_prod I _ hfI) n)
  refine ⟨b, ?_⟩
  rw [← hb, pow_mul]
  simp

theorem exists_pow_mul_colon_of_mem_chartAlgMid {ι : Type u} [Fintype ι]
    (I : ι → Ideal ↥(chartAlgFin R F f)) (n : ℕ) {z : F} (hz : z ∈ chartAlgMid R F f) :
    ∃ k : ℕ, ∀ a ∈ (∏ i, I i) ^ n, ∃ b : ↥(chartAlgFin R F f), (f ^ k * z) * (a : F) = (b : F) := by
  obtain ⟨k, hk⟩ := exists_pow_mul_mem_chartAlgFin_of_mem_chartAlgMid R F f hz
  exact ⟨k, fun a _ => ⟨⟨f ^ k * z, hk⟩ * a, by simp⟩⟩

theorem exists_finset_span_adjoin_of_colon [IsNoetherianRing ↥(chartAlgFin R F f)]
    (hfin : letI := (polynomialToChartFin R F f).toRingHom.toAlgebra
      Module.Finite (Polynomial R) ↥(chartAlgFin R F f))
    (K : Ideal ↥(chartAlgFin R F f)) (d : ↥(chartAlgFin R F f)) (hd : d ∈ K) (hd0 : (d : F) ≠ 0) :
    ∃ G0 : Finset F,
      (∀ x ∈ G0, ∀ a ∈ K, ∃ b : ↥(chartAlgFin R F f), x * (a : F) = (b : F)) ∧
      ∀ g : F, (∀ a ∈ K, ∃ b : ↥(chartAlgFin R F f), g * (a : F) = (b : F)) →
        g ∈ Submodule.span ↥(Algebra.adjoin R ({f} : Set F)) (G0 : Set F) := by
  classical
  letI algP : Algebra (Polynomial R) ↥(chartAlgFin R F f) := (polynomialToChartFin R F f).toRingHom.toAlgebra
  haveI : Module.Finite (Polynomial R) ↥(chartAlgFin R F f) := hfin

  let N : Submodule ↥(chartAlgFin R F f) F :=
    { carrier := {g | ∀ a ∈ K, ∃ b : ↥(chartAlgFin R F f), g * (a : F) = (b : F)}
      add_mem' := by
        intro x y hx hy a ha
        obtain ⟨b, hb⟩ := hx a ha
        obtain ⟨c, hc⟩ := hy a ha
        exact ⟨b + c, by rw [add_mul, hb, hc, Subalgebra.coe_add]⟩
      zero_mem' := fun a _ => ⟨0, by simp⟩
      smul_mem' := by
        intro c x hx a ha
        obtain ⟨b, hb⟩ := hx a ha
        exact ⟨c * b, by rw [Algebra.smul_def, Subalgebra.coe_mul, mul_assoc, hb]; rfl⟩ }
  have hNle : N ≤ Submodule.span ↥(chartAlgFin R F f) {(d : F)⁻¹} := by
    intro g hg
    obtain ⟨b, hb⟩ := hg d hd
    have : g = b • (d : F)⁻¹ := by
      rw [Algebra.smul_def]
      show g = (b : F) * (d : F)⁻¹
      rw [← hb, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hNfg : N.FG := by
    have hM : (Submodule.span ↥(chartAlgFin R F f) {(d : F)⁻¹}).FG := Submodule.fg_span_singleton _
    haveI := isNoetherian_of_fg_of_noetherian _ hM
    have h1 : (N.comap (Submodule.span ↥(chartAlgFin R F f) {(d : F)⁻¹}).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Submodule.span ↥(chartAlgFin R F f) {(d : F)⁻¹}).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hNle] at h2
  obtain ⟨S, hS⟩ := hNfg
  obtain ⟨T, hT⟩ := Module.finite_def.mp ‹Module.Finite (Polynomial R) ↥(chartAlgFin R F f)›
  let G0 : Finset F := (S ×ˢ T).image (fun p => p.1 * (p.2 : F))

  have hsmulP : ∀ (p : Polynomial R) (a : ↥(chartAlgFin R F f)),
      ((p • a : ↥(chartAlgFin R F f)) : F) = Polynomial.aeval f p * (a : F) := by
    intro p a
    rw [Algebra.smul_def, Subalgebra.coe_mul]
    congr 1
    show ((Polynomial.aeval (jChartFin R F f) p : ↥(chartAlgFin R F f)) : F) = Polynomial.aeval f p
    rw [← coe_jChartFin R F f]
    exact (Polynomial.aeval_algebraMap_apply F (jChartFin R F f) p).symm
  have hPmem : ∀ p : Polynomial R, Polynomial.aeval f p ∈ Algebra.adjoin R ({f} : Set F) :=
    fun p => Polynomial.aeval_mem_adjoin_singleton R f

  have hAs : ∀ (a : ↥(chartAlgFin R F f)) (s : F), s ∈ S →
      (a : F) * s ∈ Submodule.span ↥(Algebra.adjoin R ({f} : Set F)) (G0 : Set F) := by
    intro a s hs
    have ha : a ∈ Submodule.span (Polynomial R) (T : Set ↥(chartAlgFin R F f)) := hT.symm ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem t ht =>
      rw [mul_comm]
      exact Submodule.subset_span (Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩)
    | zero => rw [Subalgebra.coe_zero, zero_mul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [Subalgebra.coe_add, add_mul]; exact Submodule.add_mem _ ha hb
    | smul p a _ ha =>
      rw [hsmulP, mul_assoc]
      exact Submodule.smul_mem _ (⟨Polynomial.aeval f p, hPmem p⟩ : ↥(Algebra.adjoin R ({f} : Set F))) ha

  have hAspan : ∀ (a : ↥(chartAlgFin R F f)) (y : F), y ∈ Submodule.span ↥(Algebra.adjoin R ({f} : Set F)) (G0 : Set F) →
      (a : F) * y ∈ Submodule.span ↥(Algebra.adjoin R ({f} : Set F)) (G0 : Set F) := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hs, ht⟩ := Finset.mem_product.mp hst
      have : (a : F) * (s * (t : F)) = ((a * t : ↥(chartAlgFin R F f)) : F) * s := by
        rw [Subalgebra.coe_mul]; ring
      rw [this]; exact hAs _ s hs
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  refine ⟨G0, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hs, -⟩ := Finset.mem_product.mp hst
    have hsN : s ∈ N := hS ▸ Submodule.subset_span hs
    have := N.smul_mem t hsN
    intro a ha
    obtain ⟨b, hb⟩ := this a ha
    exact ⟨b, by rw [← hb, Algebra.smul_def]; show s * (t : F) * a = (t : F) * s * a; ring⟩
  · intro g hg
    have hgN : g ∈ N := hg
    clear hg
    rw [← hS] at hgN
    induction hgN using Submodule.span_induction with
    | mem s hs => have := hAs 1 s hs; rwa [Subalgebra.coe_one, one_mul] at this
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Algebra.smul_def]; exact hAspan a x hx

end ColonChart

end PenLift

open IntermediateField

namespace PenGenus

set_option maxHeartbeats 3200000 in
theorem exists_genus {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    (f : F) (htf : Transcendental K f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({f} : Set F)) F) :
    ∃ (_ : Nonempty (Place K F)) (_ : FiniteDimensional K ↥(riemannRochSpace (0 : Divisor K F))),
      (∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀) ∧
      (∃ v : Place K F, f ∉ v.toValuationSubring) ∧ (∃ v : Place K F, f⁻¹ ∉ v.toValuationSubring) ∧
      ({v : Place K F | f ∈ v.toValuationSubring} ∪ {v : Place K F | f⁻¹ ∈ v.toValuationSubring} = Set.univ) := by
  classical
  set E := IntermediateField.adjoin K ({f} : Set F) with hE
  haveI : FiniteDimensional ↥E F := hFD
  haveI : Algebra.IsSeparable ↥E F := hsep

  haveI hne : Nonempty (Place K F) := AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional K f htf hFD

  let e : RatFunc K ≃ₐ[K] ↥E := RatFunc.algEquivOfTranscendental f htf
  letI algRF : Algebra (RatFunc K) F := ((algebraMap ↥E F).comp e.toAlgHom.toRingHom).toAlgebra
  letI algRE : Algebra (RatFunc K) ↥E := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc K) ↥E F := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap K F c = algebraMap ↥E F (e (algebraMap K (RatFunc K) c))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply])
  haveI : IsScalarTower K (RatFunc K) ↥E := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap K ↥E c = e (algebraMap K (RatFunc K) c)
    rw [e.commutes])
  haveI : Module.Finite (RatFunc K) ↥E := Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) ↥E) e.surjective
  haveI : FiniteDimensional (RatFunc K) F := Module.Finite.trans ↥E F
  haveI : Algebra.IsSeparable (RatFunc K) ↥E := by
    refine ⟨fun y => ?_⟩
    obtain ⟨r, rfl⟩ := e.surjective y
    change IsSeparable (RatFunc K) (algebraMap (RatFunc K) ↥E r)
    exact isSeparable_algebraMap r
  haveI : Algebra.IsSeparable (RatFunc K) F := Algebra.IsSeparable.trans (RatFunc K) ↥E F

  haveI : Algebra.EssFiniteType K (RatFunc K) := by
    haveI : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
      Algebra.EssFiniteType.of_isLocalization (R := Polynomial K) (S := RatFunc K) (M := nonZeroDivisors (Polynomial K))
    exact Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)
  haveI : Algebra.EssFiniteType K ↥E := Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective
  haveI : Algebra.EssFiniteType ↥E F := inferInstance
  haveI : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K ↥E F
  haveI hL0 : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := AlgebraicCurve.finiteDimensional_lSpace_zero K F

  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨-, -, γ, D₀, hγ⟩ := AlgebraicCurve.RationalFunctionField.stichtenothGenusExists_of_ratFunc_tower K F

  have pole : ∀ g : F, Transcendental K g → ∃ v : Place K F, g ∉ v.toValuationSubring := by
    intro g hg
    by_contra hall
    push Not at hall
    have hmem : ∀ n : ℕ, g ^ n ∈ LSpace (0 : Divisor K F) := by
      intro n v
      show v.adicValuation (g ^ n) ≤ WithZero.exp ((0 : Divisor K F) v)
      rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero, map_pow]
      exact pow_le_one' ((Place.mem_iff_adicValuation_le_one v).mp (hall v)) n
    have hli : LinearIndependent K (fun n : ℕ => (⟨g ^ n, hmem n⟩ : ↥(LSpace (0 : Divisor K F)))) := by
      apply LinearIndependent.of_comp (LSpace (0 : Divisor K F)).subtype
      exact AlgebraicCurve.linearIndependent_pow_of_transcendental hg
    exact Module.Finite.not_linearIndependent_of_infinite _ hli
  have htf' : Transcendental K f⁻¹ := fun halg => htf (IsAlgebraic.inv_iff.mp halg)
  refine ⟨hne, hL0, ⟨γ, D₀, hγ⟩, pole f htf, pole f⁻¹ htf', ?_⟩
  ext v
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact v.toValuationSubring.mem_or_inv_mem f

end PenGenus

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    {ι : Type u} [Fintype ι]

    (𝔪 : ι → Ideal ↥(chartAlgFin R F f)) (h𝔪 : ∀ i, (𝔪 i).IsMaximal) (hinj : Function.Injective 𝔪)
    (hϖ𝔪 : ∀ i, algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔪 i)
    (hf𝔪 : ∀ i, jChartFin R F f ∈ 𝔪 i)
    (I : ι → Ideal ↥(chartAlgFin R F f))
    (hI : ∀ i (a : ↥(chartAlgFin R F f)), a ∈ I i ↔
      ∃ s : ↥(chartAlgFin R F f), s ∉ 𝔪 i ∧ s * a ∈ Ideal.span {jChartFin R F f})
    (hfin : ∀ i, Module.Finite R (↥(chartAlgFin R F f) ⧸ I i))
    (htor : ∀ i (y : ↥(chartAlgFin R F f) ⧸ I i), algebraMap R (↥(chartAlgFin R F f) ⧸ I i) ϖ * y = 0 → y = 0)
    (hle : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → I i ≤ P → P ≤ 𝔪 i)
    (hisol : ∀ i (P : Ideal ↥(chartAlgFin R F f)), P.IsPrime → jChartFin R F f ∈ P →
      algebraMap R ↥(chartAlgFin R F f) ϖ ∈ P → P ≤ 𝔪 i → P = 𝔪 i) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (g : F),
      (∀ 𝔭 : Ideal ↥(chartAlgFin R F f), 𝔭.IsPrime → (∀ i, ¬ I i ≤ 𝔭) →
        ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔭 ∧ g * (c : F) = (b : F)) ∧
      (∀ 𝔭' : Ideal ↥(chartAlgInf R F f), 𝔭'.IsPrime → jInvChartInf R F f ∈ 𝔭' →
        ∃ b c : ↥(chartAlgInf R F f), c ∉ 𝔭' ∧ g * (c : F) = (b : F)) ∧
      (∀ i, ∃ b c : ↥(chartAlgFin R F f), b ∉ 𝔪 i ∧ c ∉ 𝔪 i ∧ g * f ^ n * (c : F) = (b : F)) := by
  classical

  let J : Ideal ↥(chartAlgFin R F f) := ∏ i, I i
  let N0 : ℕ → Submodule R F := fun n =>
    { carrier := {g | ∀ a ∈ J ^ n, ∃ b : ↥(chartAlgFin R F f), g * (a : F) = (b : F)}
      add_mem' := by
        intro x y hx hy a ha
        obtain ⟨b, hb⟩ := hx a ha
        obtain ⟨c, hc⟩ := hy a ha
        exact ⟨b + c, by rw [add_mul, hb, hc, Subalgebra.coe_add]⟩
      zero_mem' := fun a _ => ⟨0, by simp⟩
      smul_mem' := by
        intro r x hx a ha
        obtain ⟨b, hb⟩ := hx a ha
        exact ⟨r • b, by rw [Subalgebra.coe_smul, smul_mul_assoc, hb]⟩
    }
  let N1 : Submodule R F := (chartAlgInf R F f).toSubmodule
  let N01 : Submodule R F := (chartAlgMid R F f).toSubmodule
  have hf0 : (f : F) ≠ 0 := Fact.out
  have hfI : ∀ i, jChartFin R F f ∈ I i :=
    PenLift.mem_of_branchData 𝔪 (fun i => (h𝔪 i).ne_top) (jChartFin R F f) I hI
  have hfinvMid : f⁻¹ ∈ chartAlgMid R F f := subset_chartAlg R F _ (by simp)
  have hfinvInf : f⁻¹ ∈ chartAlgInf R F f := subset_chartAlg R F _ rfl
  have h0 : ∀ n, N0 n ≤ N01 := by
    intro n g hg
    obtain ⟨b, hb⟩ := PenLift.exists_mul_pow_eq_of_forall_mem_prod_pow R F f I hfI n g hg
    have : g = (b : F) * (f⁻¹) ^ (Fintype.card ι * n) := by
      rw [← hb, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hf0), mul_one]
    show g ∈ chartAlgMid R F f
    rw [this]
    exact Subalgebra.mul_mem _ (PenLift.chartAlgFin_le_chartAlgMid R F f b.2) (Subalgebra.pow_mem _ hfinvMid _)
  have h1 : N1 ≤ N01 := fun x hx => PenLift.chartAlgInf_le_chartAlgMid R F f hx
  let S : ℕ → TwoChartCech.Sections (TwoChartCech.Cover.trivial R) :=
    fun n => TwoChartCech.Sections.ofSubmodules (N0 n) N1 N01 (h0 n) h1
  have hmono : ∀ n, N0 n ≤ N0 (n + 1) := by
    intro n g hg a ha
    exact hg a (Ideal.pow_le_pow_right (Nat.le_succ n) ha)

  have hFin : ∀ n, Module.Finite R (S n).H1 := by
    intro n
    have hx : ∀ m ∈ N0 n, f * m ∈ N0 n := fun m hm a ha => by
      obtain ⟨b, hb⟩ := hm a ha
      exact ⟨jChartFin R F f * b, by rw [Subalgebra.coe_mul, coe_jChartFin, mul_assoc, hb]⟩
    have hy : ∀ m ∈ N1, f⁻¹ * m ∈ N1 := fun m hm => Subalgebra.mul_mem _ hfinvInf hm
    have hy01 : ∀ m ∈ N01, f⁻¹ * m ∈ N01 := fun m hm => Subalgebra.mul_mem _ hfinvMid hm
    haveI : IsNoetherianRing ↥(chartAlgFin R F f) := by
      haveI := (finiteType_chartAlgFin_and_chartAlgInf R K₀ F f htf hFD hsep).1
      exact Algebra.FiniteType.isNoetherianRing R _
    have hfinP := (finite_polynomial_chartAlgFin_and_chartAlgInf R K₀ F f htf hFD hsep).1
    have hd : jChartFin R F f ^ (Fintype.card ι * n) ∈ J ^ n := by
      rw [pow_mul]; exact Ideal.pow_mem_pow (PenLift.pow_card_mem_prod I _ hfI) n
    obtain ⟨G0, hG0, hspan⟩ := PenLift.exists_finset_span_adjoin_of_colon R F f hfinP (J ^ n)
      (jChartFin R F f ^ (Fintype.card ι * n)) hd (by simp [hf0])
    exact TwoChartCech.Sections.finite_H1_ofSubmodules_of_forall_exists_pow_mul_mem f f⁻¹ (mul_inv_cancel₀ hf0)
      (N0 n) N1 N01 (h0 n) h1 hx hy hy01 G0 (fun x hx => hG0 x hx) (fun g hg => hspan g hg)
      (fun z hz => PenLift.exists_pow_mul_colon_of_mem_chartAlgMid R F f I n hz)
      (fun z hz => PenLift.exists_pow_mul_mem_chartAlgInf_of_mem_chartAlgMid R F f hz)

  have hcd : ∀ n (p : ↥(N0 n) × ↥N1), ((S n).cechDiff p : F) = (p.2 : F) - (p.1 : F) := by
    intro n p
    rw [TwoChartCech.Sections.cechDiff_apply]
    show ((Submodule.inclusion h1 p.2 - Submodule.inclusion (h0 n) p.1 : ↥N01) : F) = _
    rw [Submodule.coe_sub, Submodule.coe_inclusion, Submodule.coe_inclusion]
  have hrange : ∀ n (w : ↥N01), w ∈ LinearMap.range (S n).cechDiff ↔
      ∃ s0 s1 : F, s0 ∈ N0 n ∧ s1 ∈ N1 ∧ (w : F) = s1 - s0 := by
    intro n w
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨(p.1 : F), (p.2 : F), p.1.2, p.2.2, by rw [← hp, hcd]⟩
    · rintro ⟨s0, s1, hs0, hs1, hw⟩
      refine ⟨(⟨s0, hs0⟩, ⟨s1, hs1⟩), Subtype.ext ?_⟩
      rw [hcd, hw]
  have hrmono : ∀ n, LinearMap.range (S n).cechDiff ≤ LinearMap.range (S (n + 1)).cechDiff := by
    intro n w hw
    obtain ⟨s0, s1, hs0, hs1, hw⟩ := (hrange n w).mp hw
    exact (hrange (n + 1) w).mpr ⟨s0, s1, hmono n hs0, hs1, hw⟩
  have hSurj : ∀ n, ∃ φ : (S n).H1 →ₗ[R] (S (n + 1)).H1, Function.Surjective φ ∧
      (Function.Injective φ → ∀ z : F, z ∈ N0 (n + 1) → ∃ z₀ z₁ : F, z₀ ∈ N0 n ∧ z₁ ∈ N1 ∧ z = z₀ + z₁) := by
    intro n
    refine ⟨Submodule.mapQ _ _ LinearMap.id (by simpa only [Submodule.comap_id] using hrmono n), ?_, ?_⟩
    · intro y
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk w, by rw [Submodule.mapQ_apply, LinearMap.id_apply]⟩
    · intro hinjφ z hz

      have hz01 : z ∈ N01 := h0 (n + 1) hz
      have hmem1 : (⟨z, hz01⟩ : ↥N01) ∈ LinearMap.range (S (n + 1)).cechDiff :=
        (hrange (n + 1) _).mpr ⟨-z, 0, (N0 (n + 1)).neg_mem hz, N1.zero_mem, by simp⟩
      have hzero : Submodule.mapQ _ _ LinearMap.id (by simpa only [Submodule.comap_id] using hrmono n) (Submodule.Quotient.mk ⟨z, hz01⟩ : (S n).H1) = 0 := by
        rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]
        exact hmem1
      have hmem0 : (⟨z, hz01⟩ : ↥N01) ∈ LinearMap.range (S n).cechDiff := by
        rw [← Submodule.Quotient.mk_eq_zero]
        apply hinjφ
        rw [hzero, map_zero]
      obtain ⟨s0, s1, hs0, hs1, hw⟩ := (hrange n _).mp hmem0
      refine ⟨-s0, s1, (N0 n).neg_mem hs0, hs1, ?_⟩
      have : (z : F) = s1 - s0 := hw
      rw [this]; ring

  have hTors : Nonempty ι → ∃ N₁ : ℕ, ∀ n, N₁ ≤ n → ∃ k : ℕ, ∀ x : (S n).H1, ϖ ^ k • x = 0 := by
    intro hι
    haveI : Nonempty ι := hι

    have htfK : Transcendental K₀ f := fun h => htf ((IsFractionRing.isAlgebraic_iff R K₀ F).mpr h)
    letI hCurve : IsCurveOver K₀ F := AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable K₀ F f htfK hFD hsep
    obtain ⟨hne, hL0, ⟨γ, D₀, hγ⟩, hpole, hpole', hcover⟩ := PenGenus.exists_genus (K := K₀) f htfK hFD hsep
    haveI := hne
    haveI := hL0
    have h₀ : ∃ v, v ∉ {v : Place K₀ F | f ∈ v.toValuationSubring} := by obtain ⟨v, hv⟩ := hpole; exact ⟨v, hv⟩
    have h₁ : ∃ v, v ∉ {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring} := by obtain ⟨v, hv⟩ := hpole'; exact ⟨v, hv⟩

    have hIne : ∀ i, I i ≠ ⊤ := by
      intro i htop
      obtain ⟨s, hs, hs1⟩ := (hI i 1).mp (htop.symm ▸ Submodule.mem_top)
      rw [mul_one] at hs1
      exact hs ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hf𝔪 i))) hs1)
    obtain ⟨D_K, -, hdeg, -, hdict⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.exists_divisor_degree_pos_lSpaceOn_nsmul_le_of_branchData
        R ϖ hϖ K₀ F f htf hFD hsep 𝔪 h𝔪 hϖ𝔪 hf𝔪 I hI hIne htor hle

    obtain ⟨N, hN⟩ := AlgebraicCurve.exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt
      hγ hcover h₀ h₁ D_K hdeg
    refine ⟨N, fun n hn => ?_⟩
    haveI hsub := hN n hn
    obtain ⟨ha, hb, hc⟩ := hdict n

    have key : ∀ z : ↥N01, ∃ k : ℕ, (ϖ ^ k • z) ∈ LinearMap.range (S n).cechDiff := by
      intro z
      have hz : (z : F) ∈ lSpaceOn ({v : Place K₀ F | f ∈ v.toValuationSubring} ∩ {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring})
          ((n : ℤ) • D_K) := hb ⟨(z : F), z.2⟩
      have hsplit : (z : F) ∈ lSpaceOn {v : Place K₀ F | f ∈ v.toValuationSubring} ((n : ℤ) • D_K) ⊔
          lSpaceOn {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring} ((n : ℤ) • D_K) := by
        have h0 : (Submodule.Quotient.mk ⟨(z : F), hz⟩ : cechH1 {v : Place K₀ F | f ∈ v.toValuationSubring}
            {v : Place K₀ F | f⁻¹ ∈ v.toValuationSubring} ((n : ℤ) • D_K)) = 0 := Subsingleton.elim _ _
        exact (mem_range_cechDiff_iff _).mp ((Submodule.Quotient.mk_eq_zero _).mp h0)
      obtain ⟨u₀, hu₀, u₁, hu₁, hsum⟩ := Submodule.mem_sup.mp hsplit
      obtain ⟨k₀, hk₀⟩ := ha u₀ hu₀
      obtain ⟨k₁, b₁, hb₁⟩ := hc u₁ hu₁
      refine ⟨k₀ + k₁, ?_⟩

      have hm0 : algebraMap R F ϖ ^ (k₀ + k₁) * u₀ ∈ N0 n := by
        intro a haJ
        obtain ⟨b, hb'⟩ := hk₀ a haJ
        refine ⟨algebraMap R _ ϖ ^ k₁ * b, ?_⟩
        rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, ← hb']
        ring
      have hm1 : algebraMap R F ϖ ^ (k₀ + k₁) * u₁ ∈ N1 := by
        show algebraMap R F ϖ ^ (k₀ + k₁) * u₁ ∈ (chartAlgInf R F f).toSubmodule
        have : algebraMap R F ϖ ^ (k₀ + k₁) * u₁ = algebraMap R F ϖ ^ k₀ * (b₁ : F) := by rw [← hb₁]; ring
        rw [this]
        exact (chartAlgInf R F f).mul_mem (pow_mem ((chartAlgInf R F f).algebraMap_mem ϖ) k₀) b₁.2
      refine ⟨(⟨-(algebraMap R F ϖ ^ (k₀ + k₁) * u₀), neg_mem hm0⟩, ⟨algebraMap R F ϖ ^ (k₀ + k₁) * u₁, hm1⟩), ?_⟩
      apply Subtype.ext
      rw [TwoChartCech.Sections.cechDiff_apply]
      show algebraMap R F ϖ ^ (k₀ + k₁) * u₁ - -(algebraMap R F ϖ ^ (k₀ + k₁) * u₀) = ((ϖ ^ (k₀ + k₁) • z : ↥N01) : F)
      rw [Submodule.coe_smul, Algebra.smul_def, map_pow, ← hsum]
      ring

    obtain ⟨s, hs⟩ := (hFin n).fg_top
    have hgen : ∀ x : (S n).H1, ∃ k : ℕ, ϖ ^ k • x = 0 := by
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H z =>
        obtain ⟨k, hk⟩ := key z
        exact ⟨k, by rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).mpr hk]⟩
    choose kf hkf using hgen
    refine ⟨s.sup kf, fun x => ?_⟩
    have hx : x ∈ Submodule.span R (s : Set (S n).H1) := by rw [hs]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      have hle : kf y ≤ s.sup kf := Finset.le_sup hy
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, add_comm, pow_add, mul_smul, hkf y, smul_zero]
    | zero => exact smul_zero _
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul r y _ hy => rw [smul_comm, hy, smul_zero]
  by_cases hι : Nonempty ι
  · choose φ hφ using hSurj
    obtain ⟨N₁, hN₁⟩ := hTors hι
    obtain ⟨n₀, hn₀⟩ := Module.exists_forall_bijective_of_forall_surjective_of_forall_smul_pow_eq_zero ϖ hϖ
      (fun n => (S n).H1) φ (fun n => (hφ n).1) N₁ (fun n _ => hFin n) hN₁
    have hsplit := (hφ n₀).2 (hn₀ n₀ le_rfl).1

    have hRestr : ∃ g₀ : F, g₀ ∈ N0 (n₀ + 1) ∧ ∀ i, ∃ s c : ↥(chartAlgFin R F f), s ∉ 𝔪 i ∧ c ∈ I i ∧
        (g₀ * f ^ (n₀ + 1) - 1) * (s : F) = (c : F) := by
      haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
      haveI : IsFractionRing ↥(chartAlgFin R F f) F := isFractionRing_chartAlg R K₀ F {f}
      haveI : IsNoetherianRing ↥(chartAlgFin R F f) := by
        haveI := (finiteType_chartAlgFin_and_chartAlgInf R K₀ F f htf hFD hsep).1
        exact Algebra.FiniteType.isNoetherianRing R _
      have hf0A : ∀ _ : ι, jChartFin R F f ≠ 0 := fun _ h => hf0 (congrArg Subtype.val h)
      obtain ⟨-, honto, -⟩ := IsFractionRing.exists_pow_mul_mem_colon_and_surjective_restrict_of_branchData (F := F)
        𝔪 h𝔪 hinj (fun _ => jChartFin R F f) hf𝔪 hf0A I hI hle n₀
      obtain ⟨g₀, hg₀, hD⟩ := honto (fun _ => 1)
      refine ⟨g₀, fun a ha => hg₀ a ha, fun i => ?_⟩
      obtain ⟨s, c, hs, hc, h⟩ := hD i
      refine ⟨s, c, hs, hc, ?_⟩
      simpa using h
    obtain ⟨g₀, hg₀, hg₀D⟩ := hRestr
    obtain ⟨g₁, a', hg₁, ha', hsum⟩ := hsplit g₀ hg₀

    refine ⟨n₀ + 1, Nat.succ_le_succ (Nat.zero_le _), a', ?_, ?_, ?_⟩
    · intro 𝔭 h𝔭 hoff
      have ha' : a' ∈ N0 (n₀ + 1) := by
        have : a' = g₀ - g₁ := by rw [hsum]; ring
        rw [this]; exact (N0 (n₀ + 1)).sub_mem hg₀ (hmono n₀ hg₁)
      have hJ : ¬ J ≤ 𝔭 := fun hle' => by
        obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_le h𝔭).mp hle'
        exact hoff i hi
      obtain ⟨a, haJ, ha𝔭⟩ := Set.not_subset.mp hJ
      have hapow : a ^ (n₀ + 1) ∈ J ^ (n₀ + 1) := Ideal.pow_mem_pow haJ _
      obtain ⟨b, hb⟩ := ha' _ hapow
      refine ⟨b, a ^ (n₀ + 1), fun h => ha𝔭 (h𝔭.mem_of_pow_mem _ h), ?_⟩
      simpa using hb
    · intro 𝔭' h𝔭' _
      exact ⟨⟨a', ha'⟩, 1, fun h => h𝔭'.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
    · intro i
      haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
      haveI : IsFractionRing ↥(chartAlgFin R F f) F := isFractionRing_chartAlg R K₀ F {f}
      haveI : IsNoetherianRing ↥(chartAlgFin R F f) := by
        haveI := (finiteType_chartAlgFin_and_chartAlgInf R K₀ F f htf hFD hsep).1
        exact Algebra.FiniteType.isNoetherianRing R _
      have hf0A : ∀ _ : ι, jChartFin R F f ≠ 0 := fun _ h => hf0 (congrArg Subtype.val h)
      obtain ⟨-, -, hker⟩ := IsFractionRing.exists_pow_mul_mem_colon_and_surjective_restrict_of_branchData (F := F)
        𝔪 h𝔪 hinj (fun _ => jChartFin R F f) hf𝔪 hf0A I hI hle n₀
      have hg₁' : ∀ a ∈ (∏ i, I i) ^ (n₀ + 1), ∃ b : ↥(chartAlgFin R F f),
          g₁ * algebraMap _ F a = algebraMap _ F b := fun a ha => hmono n₀ hg₁ a ha
      obtain ⟨s', c', hs', hc', h1'⟩ := ((hker g₁ hg₁').mpr (fun a ha => hg₁ a ha)) i
      obtain ⟨s, c, hs, hc, h0'⟩ := hg₀D i
      have hIm : I i ≤ 𝔪 i := fun a ha => by
        obtain ⟨σ, hσ, hσa⟩ := (hI i a).mp ha
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hσa
        have : σ * a ∈ 𝔪 i := by rw [← hr]; exact Ideal.mul_mem_left _ _ (hf𝔪 i)
        exact ((h𝔪 i).isPrime.mem_or_mem this).resolve_left hσ
      refine ⟨s * s' + (c * s' - c' * s), s * s', ?_, ?_, ?_⟩
      · intro hb
        have hcs : c * s' - c' * s ∈ 𝔪 i :=
          hIm ((I i).sub_mem (Ideal.mul_mem_right _ _ hc) (Ideal.mul_mem_right _ _ hc'))
        have : s * s' ∈ 𝔪 i := by
          have := (𝔪 i).sub_mem hb hcs
          rwa [add_sub_cancel_right] at this
        exact ((h𝔪 i).isPrime.mem_or_mem this).elim hs hs'
      · exact fun h => ((h𝔪 i).isPrime.mem_or_mem h).elim hs hs'
      · have ha'eq : a' = g₀ - g₁ := by rw [hsum]; ring
        rw [ha'eq]
        simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_sub] at h0' h1' ⊢
        have h0'' : (g₀ * f ^ (n₀ + 1) - 1) * (s : F) = (c : F) := by simpa using h0'
        have h1'' : g₁ * f ^ (n₀ + 1) * (s' : F) = (c' : F) := by simpa using h1'
        linear_combination (s' : F) * h0'' - (s : F) * h1''
  · refine ⟨1, le_rfl, 1, ?_, ?_, ?_⟩
    · intro 𝔭 h𝔭 _; exact ⟨1, 1, fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
    · intro 𝔭' h𝔭' _; exact ⟨1, 1, fun h => h𝔭'.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
    · intro i; exact (hι ⟨i⟩).elim

end S_AlgebraicCurve_TwoChartIntegralModel_exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_forall_mem_localization_chartAlg_and_mul_pow_jChartFin_isUnit_of_branchData (solution)
