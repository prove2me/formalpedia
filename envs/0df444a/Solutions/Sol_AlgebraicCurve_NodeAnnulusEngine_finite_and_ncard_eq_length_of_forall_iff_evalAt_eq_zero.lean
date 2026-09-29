-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.finite_and_ncard_eq_length_of_forall_iff_evalAt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0f92e92b-69a2-5561-a728-17f258c45aaa

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_finiteDimensional_fractionRing_quotient_of_not_mem
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero
import Theorems.Thm_IsLocalRing_finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal
import Theorems.Thm_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_ncard_eq_length_of_forall_iff_evalAt_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))

    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥) (h𝔭ϖ : (⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀) ∉ 𝔭) :
    {P : Place L F | P ∈ S ∧ ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭}.Finite ∧
    (({P : Place L F | P ∈ S ∧ ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭}.ncard : ℕ) : ℕ∞) =
      Module.length ↥𝒩₀ (↥𝒩₀ ⧸ (𝔭 ⊔ Ideal.span {(⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀)})) := by
  classical

  obtain ⟨hRdom, hRloc, -⟩ := UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE
  haveI := hRloc
  have hπu : ¬ IsUnit π := hπ.not_isUnit
  have hπEu : ¬ IsUnit (π ^ E) := fun h => hπu (isUnit_pow_iff (by omega) |>.mp h)
  set ϖN : ↥𝒩₀ := ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ with hϖN
  let i : ↥C →+* ↥𝒩₀ := ((algebraMap L F).comp C.subtype).codRestrict 𝒩₀ (fun c => hCmem c c.2)
  let iA : ↥C →+* ↥A := C.subtype.codRestrict A (fun c => hC c c.2)
  letI algCN : Algebra ↥C ↥𝒩₀ := i.toAlgebra
  have hCalg : ∀ c : ↥C, ((algebraMap ↥C ↥𝒩₀ c : ↥𝒩₀) : F) = algebraMap L F (c : L) := fun _ => rfl
  have hCA : ∀ c : ↥C, algebraMap ↥C L c ∈ A := fun c => hC c c.2

  have hϖA : iA ϖ ∈ maximalIdeal ↥A := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
  have hϖC0 : ϖ ≠ 0 := fun h => hϖ0 (by rw [h]; rfl)
  have hϖCu : ¬ IsUnit ϖ := fun h => (mem_maximalIdeal _).mp hϖA (h.map iA)

  have hprimeC : ∀ P : Ideal ↥C, P.IsPrime → ϖ ∈ P → P = maximalIdeal ↥C := fun P hP hϖP =>
    IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime (fun h => hϖC0 (Ideal.mem_bot.mp (h ▸ hϖP))) hP)
  have hcomapA : (maximalIdeal ↥A).comap iA = maximalIdeal ↥C :=
    hprimeC _ (Ideal.IsPrime.comap _) hϖA
  have hCAmax : ∀ c : ↥C, (⟨algebraMap ↥C L c, hCA c⟩ : ↥A) ∈ maximalIdeal ↥A ↔ c ∈ maximalIdeal ↥C := fun c => by
    rw [← hcomapA, Ideal.mem_comap]; rfl
  have hmC : maximalIdeal ↥C = Ideal.span {ϖ} := by
    ext d
    rw [← hcomapA, Ideal.mem_comap, ← IsLocalRing.residue_eq_zero_iff, Ideal.mem_span_singleton]
    exact (hϖ d).trans ⟨fun ⟨d', hd'⟩ => ⟨d', hd'⟩, fun ⟨d', hd'⟩ => ⟨d', hd'⟩⟩

  have hϖNm : ϖN ∈ maximalIdeal ↥𝒩₀ := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ϖN) = const (π ^ E) π := by
      rw [hϖN, ← hσπ, hconst]
    have h2 : IsUnit (const (π ^ E) π) := h1 ▸ (hu.map _).map ι
    have h3 : const (π ^ E) π ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := by
      rw [UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair hπEu]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hπu))
    exact (mem_maximalIdeal _).mp h3 h2
  have hcomapN : (maximalIdeal ↥𝒩₀).comap i = maximalIdeal ↥C :=
    hprimeC _ (Ideal.IsPrime.comap _) hϖNm
  have hdimN := IsLocalRing.eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two ι
    (UVCrossingModel.ringKrullDim_le_two π hπ E hE)

  haveI : Nontrivial (↥𝒩₀ ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹_›)
  haveI : IsLocalRing (↥𝒩₀ ⧸ 𝔭) := IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective
  have hmD : (maximalIdeal (↥𝒩₀ ⧸ 𝔭)).comap (Ideal.Quotient.mk 𝔭) = maximalIdeal ↥𝒩₀ := by
    haveI := IsLocalRing.maximalIdeal.isMaximal (↥𝒩₀ ⧸ 𝔭)
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmemD : ∀ x : ↥𝒩₀, Ideal.Quotient.mk 𝔭 x ∈ maximalIdeal (↥𝒩₀ ⧸ 𝔭) ↔ x ∈ maximalIdeal ↥𝒩₀ := fun x => by
    rw [← Ideal.mem_comap, hmD]
  have hDmax : ∀ c : ↥C, algebraMap ↥C (↥𝒩₀ ⧸ 𝔭) c ∈ maximalIdeal (↥𝒩₀ ⧸ 𝔭) ↔ c ∈ maximalIdeal ↥C := fun c => by
    rw [← hcomapN, Ideal.mem_comap, ← hmemD]; rfl
  have hDres : ∀ d : ↥𝒩₀ ⧸ 𝔭, ∃ c : ↥C, d - algebraMap ↥C (↥𝒩₀ ⧸ 𝔭) c ∈ maximalIdeal (↥𝒩₀ ⧸ 𝔭) := by
    intro d
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨o, ho⟩ := hres g
    refine ⟨o, ?_⟩
    rw [← mem_nonunits_iff, ← mem_maximalIdeal] at ho
    have : algebraMap ↥C (↥𝒩₀ ⧸ 𝔭) o = Ideal.Quotient.mk 𝔭 (i o) := rfl
    rw [this, ← map_sub, hmemD]
    exact ho
  have hDdim : Ring.DimensionLEOne (↥𝒩₀ ⧸ 𝔭) := by
    refine ⟨fun {p} hp0 hpp => ?_⟩
    have hP : (p.comap (Ideal.Quotient.mk 𝔭)).IsPrime := Ideal.IsPrime.comap _
    have h𝔭P : 𝔭 ≤ p.comap (Ideal.Quotient.mk 𝔭) := fun x hx => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact p.zero_mem
    have hne : 𝔭 ≠ p.comap (Ideal.Quotient.mk 𝔭) := by
      intro h
      apply hp0
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective p, ← h, Ideal.map_quotient_self]
    have hPm : p.comap (Ideal.Quotient.mk 𝔭) = maximalIdeal ↥𝒩₀ := by
      by_contra hPm
      exact h𝔭0 (hdimN 𝔭 _ inferInstance hP hPm (lt_of_le_of_ne h𝔭P hne))
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective
        (hPm ▸ IsLocalRing.maximalIdeal.isMaximal ↥𝒩₀ : (p.comap (Ideal.Quotient.mk 𝔭)).IsMaximal) with h | h
    · rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
      exact absurd h hpp.ne_top
    · rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
      exact h
  have hDnf : maximalIdeal (↥𝒩₀ ⧸ 𝔭) ≠ ⊥ := by
    intro h
    have : Ideal.Quotient.mk 𝔭 ϖN ∈ maximalIdeal (↥𝒩₀ ⧸ 𝔭) := (hmemD ϖN).mpr hϖNm
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact h𝔭ϖ this
  have hinjCD : Function.Injective (algebraMap ↥C (↥𝒩₀ ⧸ 𝔭)) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker
    haveI : (RingHom.ker (algebraMap ↥C (↥𝒩₀ ⧸ 𝔭))).IsPrime := RingHom.ker_isPrime _
    have hmax := Ring.DimensionLEOne.maximalOfPrime hker this
    have hϖk : ϖ ∈ RingHom.ker (algebraMap ↥C (↥𝒩₀ ⧸ 𝔭)) := by
      rw [IsLocalRing.eq_maximalIdeal hmax, hmC]; exact Ideal.mem_span_singleton_self ϖ
    rw [RingHom.mem_ker] at hϖk
    exact h𝔭ϖ (Ideal.Quotient.eq_zero_iff_mem.mp hϖk)

  have hfaith : FaithfulSMul ↥C (FractionRing (↥𝒩₀ ⧸ 𝔭)) := (faithfulSMul_iff_algebraMap_injective ↥C (FractionRing (↥𝒩₀ ⧸ 𝔭))).mpr (by
    rw [IsScalarTower.algebraMap_eq ↥C (↥𝒩₀ ⧸ 𝔭) (FractionRing (↥𝒩₀ ⧸ 𝔭))]
    exact (IsFractionRing.injective (↥𝒩₀ ⧸ 𝔭) (FractionRing (↥𝒩₀ ⧸ 𝔭))).comp hinjCD)
  letI algKκ : Algebra (FractionRing ↥C) (FractionRing (↥𝒩₀ ⧸ 𝔭)) := @FractionRing.liftAlgebra ↥C _ (FractionRing (↥𝒩₀ ⧸ 𝔭)) _ _ hfaith
  haveI : IsScalarTower ↥C (FractionRing ↥C) (FractionRing (↥𝒩₀ ⧸ 𝔭)) := @FractionRing.isScalarTower_liftAlgebra ↥C _ (FractionRing (↥𝒩₀ ⧸ 𝔭)) _ _ hfaith
  haveI hK : FiniteDimensional (FractionRing ↥C) (FractionRing (↥𝒩₀ ⧸ 𝔭)) :=
    AlgebraicCurve.NodeAnnulusEngine.finiteDimensional_fractionRing_quotient_of_not_mem 𝒩₀ hgen C hCalg ϖ hϖCu hϖC0
      hld 𝔭 h𝔭0 h𝔭ϖ (FractionRing ↥C) (FractionRing (↥𝒩₀ ⧸ 𝔭))
  haveI : CharZero ↥C := (C.subtype).charZero
  haveI : CharZero (FractionRing ↥C) := charZero_of_injective_algebraMap (IsFractionRing.injective ↥C (FractionRing ↥C))
  haveI : Algebra.IsIntegral (FractionRing ↥C) (FractionRing (↥𝒩₀ ⧸ 𝔭)) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (FractionRing ↥C) (FractionRing (↥𝒩₀ ⧸ 𝔭)) := Algebra.IsSeparable.of_integral _ _
  haveI : Algebra.IsAlgebraic ↥C L := by
    refine ⟨fun x => ?_⟩
    rcases A.mem_or_inv_mem x with hx | hx
    · exact halg x hx
    · exact IsAlgebraic.inv_iff.mp (halg _ hx)

  haveI : FaithfulSMul ↥C L := (faithfulSMul_iff_algebraMap_injective ↥C L).mpr Subtype.coe_injective
  letI algKL : Algebra (FractionRing ↥C) L := FractionRing.liftAlgebra ↥C L
  haveI : IsScalarTower ↥C (FractionRing ↥C) L := FractionRing.isScalarTower_liftAlgebra ↥C L
  haveI : Algebra.IsAlgebraic (FractionRing ↥C) L :=
    ⟨fun x => IsAlgebraic.extendScalars (IsFractionRing.injective ↥C (FractionRing ↥C))
      (Algebra.IsAlgebraic.isAlgebraic x)⟩
  obtain ⟨hfinT, hcardT⟩ := IsLocalRing.finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal
    (C := ↥C) (FractionRing ↥C) (L := L) A hCA hCAmax (D := ↥𝒩₀ ⧸ 𝔭) hDmax hDres hDdim hDnf (FractionRing (↥𝒩₀ ⧸ 𝔭))
  obtain ⟨e⟩ := AlgebraicCurve.NodeAnnulusEngine.nonempty_equiv_ringHom_quotient_of_forall_iff_evalAt_eq_zero
    A S hrat 𝒩₀ hS hgen C hC hCmem ϖ hϖ hϖ0 halg hld hrk hres π hπ σ hσπ E hE ι hconst 𝔭 h𝔭0 h𝔭ϖ
  let e' : {φ : (↥𝒩₀ ⧸ 𝔭) →+* ↥A //
        ∀ c : ↥C, φ (Ideal.Quotient.mk 𝔭 ⟨algebraMap L F (c : L), hCmem c c.2⟩) = ⟨(c : L), hC c c.2⟩} ≃
      {φ : (↥𝒩₀ ⧸ 𝔭) →+* ↥A // ∀ c : ↥C, φ (algebraMap ↥C (↥𝒩₀ ⧸ 𝔭) c) = ⟨algebraMap ↥C L c, hCA c⟩} :=
    Equiv.subtypeEquivRight (fun φ => Iff.rfl)
  have hcard : Nat.card {P : Place L F // P ∈ S ∧ ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭} =
      Nat.card {φ : (↥𝒩₀ ⧸ 𝔭) →+* ↥A // ∀ c : ↥C, φ (algebraMap ↥C (↥𝒩₀ ⧸ 𝔭) c) = ⟨algebraMap ↥C L c, hCA c⟩} :=
    Nat.card_congr (e.trans e')
  haveI hfinP : Finite {P : Place L F // P ∈ S ∧ ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭} :=
    Finite.of_equiv _ (e.trans e').symm

  have hmCD : (maximalIdeal ↥C).map (algebraMap ↥C (↥𝒩₀ ⧸ 𝔭)) =
      (Ideal.span {ϖN}).map (Ideal.Quotient.mkₐ ↥𝒩₀ 𝔭) := by
    rw [hmC, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    rfl
  have hlen : Module.length (↥𝒩₀ ⧸ 𝔭) ((↥𝒩₀ ⧸ 𝔭) ⧸ (maximalIdeal ↥C).map (algebraMap ↥C (↥𝒩₀ ⧸ 𝔭))) =
      Module.length ↥𝒩₀ (↥𝒩₀ ⧸ (𝔭 ⊔ Ideal.span {ϖN})) := by
    rw [hmCD, ← Module.length_eq_of_surjective (S := ↥𝒩₀) (R := ↥𝒩₀ ⧸ 𝔭)
      (M := (↥𝒩₀ ⧸ 𝔭) ⧸ (Ideal.span {ϖN}).map (Ideal.Quotient.mkₐ ↥𝒩₀ 𝔭)) Ideal.Quotient.mk_surjective,
      (DoubleQuot.quotQuotEquivQuotSupₐ ↥𝒩₀ 𝔭 (Ideal.span {ϖN})).toLinearEquiv.length_eq]
  refine ⟨Set.finite_coe_iff.mp hfinP, ?_⟩
  rw [← Nat.card_coe_set_eq]
  have hcard' : Nat.card ↑{P : Place L F | P ∈ S ∧ ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭} =
      Nat.card {φ : (↥𝒩₀ ⧸ 𝔭) →+* ↥A // ∀ c : ↥C, φ (algebraMap ↥C (↥𝒩₀ ⧸ 𝔭) c) = ⟨algebraMap ↥C L c, hCA c⟩} :=
    hcard
  rw [hcard', hcardT, hlen]

end S_AlgebraicCurve_NodeAnnulusEngine_finite_and_ncard_eq_length_of_forall_iff_evalAt_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_ncard_eq_length_of_forall_iff_evalAt_eq_zero (solution)
