-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f4d750f4-672f-5083-9f24-811c8ab7aff2

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

open KaehlerDifferential AlgebraicCurve

theorem solution
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
    [CharZero K] [Algebra.IsAlgebraic K K'] [IsAlgClosed K'] [Algebra.IsIntegral F F']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [AlgebraicCurve.IsCurveOver K' F']
    (hfg' : ∃ x : F', Transcendental K' x ∧ FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (ω : Ω[F⁄K]) (hω : KaehlerDifferential.map K K' F F' ω ∈ AlgebraicCurve.regularDifferentials K' F')
    (v : AlgebraicCurve.Place K F) :
    ∃ c ∈ v.toValuationSubring, ∃ t ∈ v.toValuationSubring, ω = c • KaehlerDifferential.D K F t := by
  classical

  haveI hperf : PerfectField K' := IsAlgClosed.perfectField K'
  haveI hperfK : PerfectField K := PerfectField.ofCharZero
  haveI hsepKK : Algebra.IsSeparable K K' := inferInstance
  obtain ⟨x', hx', hfdx'⟩ := hfg'
  haveI := hfdx'
  haveI hEFT : Algebra.EssFiniteType K' F' := essFiniteType_of_transcendental_of_finiteDimensional hx' hfdx'
  haveI hDCG : ∀ w : Place K' F', w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI hNT : Nontrivial Ω[F'⁄K'] :=
    Module.nontrivial_of_finrank_eq_succ (IsCurveOver.kaehler_free_rank_one (K := K') (F := F')).2
  have hcharF : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

  obtain ⟨t, ht1, -⟩ := v.exists_ord_eq_one_and_dCoord_eq
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at ht1
    exact zero_ne_one ht1
  have htt : Transcendental K t := by
    intro halg
    have := v.ord_eq_zero_of_isAlgebraic halg
    omega
  have htmem : t ∈ v.toValuationSubring := (v.mem_iff_ord_nonneg ht0).mpr (by omega)
  obtain ⟨x, hx, hfdx⟩ := hfg
  haveI := hfdx
  haveI hfdt : FiniteDimensional ↥(IntermediateField.adjoin K ({t} : Set F)) F := finiteDimensional_adjoin_of_transcendental x htt
  haveI : PerfectField ↥(IntermediateField.adjoin K ({t} : Set F)) := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({t} : Set F)) F := inferInstance
  obtain ⟨c, hc, -⟩ := KaehlerDifferential.exists_unique_smul_D_of_transcendental K t htt ω
  refine ⟨c, ?_, t, htmem, hc⟩
  by_cases hc0 : c = 0
  · rw [hc0]; exact zero_mem _

  have hplace : ∃ w : Place K' F', w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring := by
    set O := v.toValuationSubring with hOdef
    set φ : F →+* F' := algebraMap F F' with hφdef

    set A : LocalSubring F' := LocalSubring.map φ O.toLocalSubring with hAdef
    obtain ⟨W, hWA⟩ := A.exists_le_valuationSubring
    obtain ⟨hAW, hlocAW⟩ := LocalSubring.le_def.mp hWA
    have hsub : ∀ y ∈ O, φ y ∈ W := fun y hy => hAW (Subring.mem_map.mpr ⟨y, hy, rfl⟩)

    have unit_of_inv_mem : ∀ (S : Subring F') (a : F') (ha : a ∈ S), a ≠ 0 → a⁻¹ ∈ S → IsUnit (⟨a, ha⟩ : S) :=
      fun S a ha ha0 hai => ⟨⟨⟨a, ha⟩, ⟨a⁻¹, hai⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩
    have inv_mem_of_unit : ∀ (S : Subring F') (a : F') (ha : a ∈ S), IsUnit (⟨a, ha⟩ : S) → a⁻¹ ∈ S := by
      intro S a ha hu
      obtain ⟨u, hu⟩ := hu
      by_cases ha0 : a = 0
      · rw [ha0, inv_zero]; exact S.zero_mem
      have h1 : ((u⁻¹ : Sˣ) : S).1 = a⁻¹ := by
        have h2 : a * ((u⁻¹ : Sˣ) : S).1 = 1 := by
          have := congrArg (fun z : S => (z : F')) u.mul_inv
          simpa [hu] using this
        exact (eq_inv_of_mul_eq_one_right h2)
      rw [← h1]; exact ((u⁻¹ : Sˣ) : S).2
    have hcomap : W.comap φ = O := by
      ext y
      refine ⟨fun hy => ?_, fun hy => hsub y hy⟩
      by_contra hyO
      have hy0 : y ≠ 0 := by rintro rfl; exact hyO O.zero_mem
      have hyinv : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hyO

      have hAy : φ y⁻¹ ∈ A.toSubring := Subring.mem_map.mpr ⟨y⁻¹, hyinv, rfl⟩
      have hWunit : IsUnit (Subring.inclusion hAW ⟨φ y⁻¹, hAy⟩) := by
        refine unit_of_inv_mem W.toSubring (φ y⁻¹) (hAW hAy) (by simpa using hy0) ?_
        rw [map_inv₀, inv_inv]; exact hy

      have hAunit : IsUnit (⟨φ y⁻¹, hAy⟩ : A.toSubring) := hlocAW.map_nonunit _ hWunit
      have hinvA : (φ y⁻¹)⁻¹ ∈ A.toSubring := inv_mem_of_unit A.toSubring _ hAy hAunit
      rw [map_inv₀, inv_inv] at hinvA
      obtain ⟨z, hz, hzy⟩ := Subring.mem_map.mp hinvA
      have : z = y := φ.injective hzy
      exact hyO (this ▸ hz)

    have hKW : ∀ a : K', algebraMap K' F' a ∈ W := by

      have hKmem : ∀ k : K, algebraMap K F' k ∈ W := fun k => by
        rw [IsScalarTower.algebraMap_apply K F F']
        exact hsub _ (v.algebraMap_mem' k)
      intro a
      set ψ : K →+* W := (algebraMap K F').codRestrict W.toSubring hKmem with hψ
      have hcompψ : (algebraMap W F').comp ψ = algebraMap K F' := RingHom.ext fun k => rfl
      have hint : IsIntegral W (algebraMap K' F' a) := by
        obtain ⟨p, hp, hpa⟩ := (Algebra.IsIntegral.isIntegral (R := K) a)
        refine ⟨p.map ψ, hp.map ψ, ?_⟩
        rw [Polynomial.eval₂_map, hcompψ]
        have := congrArg (algebraMap K' F') hpa
        rwa [map_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq] at this
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := F')).mp hint
      rw [← hy]
      exact y.2
    have hWtop : W ≠ ⊤ := by
      intro h
      apply v.ne_top'
      rw [← hOdef, ← hcomap, h]
      rfl
    haveI hPID : IsPrincipalIdealRing W := ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin x' W hKW hWtop
    exact ⟨⟨W, hKW, hWtop, hPID⟩, hcomap⟩
  obtain ⟨w, hw⟩ := hplace
  suffices hup : algebraMap F F' c ∈ w.toValuationSubring by
    have : c ∈ w.toValuationSubring.comap (algebraMap F F') := hup
    rwa [hw] at this

  have hord : ∀ f : F, w.ord (algebraMap F F' f) = v.ord f :=
    Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top hgen v w hw
  set c' : F' := algebraMap F F' c with hc'def
  set t' : F' := algebraMap F F' t with ht'def
  have ht'1 : w.ord t' = 1 := (hord t).trans ht1

  have hmap : KaehlerDifferential.map K K' F F' ω = c' • KaehlerDifferential.D K' F' t' := by
    rw [hc, LinearMap.map_smul_of_tower, KaehlerDifferential.map_D, hc'def, ht'def, algebraMap_smul]

  obtain ⟨f', hf'mem, hf'⟩ := hω w
  obtain ⟨π, hπ1, hπd⟩ := w.exists_ord_eq_one_and_dCoord_eq

  set d : F' := w.differentialCoeff (KaehlerDifferential.D K' F' t') with hddef
  have hdt : KaehlerDifferential.D K' F' t' = d • w.dCoord := (w.differentialCoeff_smul_dCoord _).symm

  have mkUnit : ∀ y : F', y ≠ 0 → w.ord y = 0 → ∃ u : w.toValuationSubringˣ, ((u : w.toValuationSubring) : F') = y := by
    intro y hy0 hy
    have hymem : y ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg hy0).mpr (by omega)
    have hyinv : y⁻¹ ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg (inv_ne_zero hy0)).mpr (by rw [Place.ord_inv]; omega)
    exact ⟨⟨⟨y, hymem⟩, ⟨y⁻¹, hyinv⟩, Subtype.ext (mul_inv_cancel₀ hy0), Subtype.ext (inv_mul_cancel₀ hy0)⟩, rfl⟩
  have hdunit : ∃ u : w.toValuationSubringˣ, ((u : w.toValuationSubring) : F') = d := by
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [Place.ord_zero] at hπ1
      exact zero_ne_one hπ1
    have ht'0 : t' ≠ 0 := by
      rintro h
      rw [h, Place.ord_zero] at ht'1
      exact zero_ne_one ht'1

    set e : F' := t' * π⁻¹ with hedef
    have he0 : e ≠ 0 := mul_ne_zero ht'0 (inv_ne_zero hπ0)
    have horde : w.ord e = 0 := by
      rw [hedef, w.ord_mul ht'0 (inv_ne_zero hπ0), Place.ord_inv, ht'1, hπ1]; norm_num
    obtain ⟨eU, heU⟩ := mkUnit e he0 horde
    have hte : t' = e * π := by rw [hedef, mul_assoc, inv_mul_cancel₀ hπ0, mul_one]

    set g : F' := w.differentialCoeff (KaehlerDifferential.D K' F' e) with hgdef
    have hge : KaehlerDifferential.D K' F' e = g • w.dCoord := (w.differentialCoeff_smul_dCoord _).symm
    have hgmem : g ∈ w.toValuationSubring := by
      rcases localUnitDerivativeRegular_of_isCurveOver w e he0 horde with h | h
      · rw [hgdef, h]; exact zero_mem _
      · by_cases hg0 : g = 0
        · rw [hg0]; exact zero_mem _
        · exact (w.mem_iff_ord_nonneg hg0).mpr h

    have hd : d = e + π * g := by
      apply w.differentialCoeff_unique
      rw [hte, Derivation.leibniz, hge, ← hπd, smul_smul, ← add_smul, add_comm]

    have hπmem : π ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg hπ0).mpr (by omega)
    have hemem : e ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg he0).mpr (by omega)
    have heinv : e⁻¹ ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg (inv_ne_zero he0)).mpr (by rw [Place.ord_inv]; omega)
    have hm : (⟨e⁻¹ * (π * g), mul_mem heinv (mul_mem hπmem hgmem)⟩ : w.toValuationSubring) ∈
        IsLocalRing.maximalIdeal w.toValuationSubring := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu⟩ := hu
      have h0 := w.ord_coe_unit u
      rw [hu] at h0
      change w.ord (e⁻¹ * (π * g)) = 0 at h0
      by_cases hg0 : g = 0
      ·
        apply u.ne_zero
        rw [hu]
        apply Subtype.ext
        simp [hg0]
      · rw [w.ord_mul (inv_ne_zero he0) (mul_ne_zero hπ0 hg0), w.ord_mul hπ0 hg0, Place.ord_inv, horde, hπ1] at h0
        have := (w.mem_iff_ord_nonneg hg0).mp hgmem
        omega
    have hunit1 : IsUnit ((1 : w.toValuationSubring) + ⟨e⁻¹ * (π * g), mul_mem heinv (mul_mem hπmem hgmem)⟩) := by
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(⟨e⁻¹ * (π * g), mul_mem heinv (mul_mem hπmem hgmem)⟩ : w.toValuationSubring))
        (by rw [← IsLocalRing.mem_maximalIdeal]; exact neg_mem hm)
      simpa using this
    obtain ⟨u1, hu1⟩ := hunit1
    refine ⟨eU * u1, ?_⟩
    rw [Units.val_mul, MulMemClass.coe_mul, hu1, heU, hd]
    push_cast
    field_simp

  have hcoef : f' = c' * d := by
    have h1 : w.differentialCoeff (KaehlerDifferential.map K K' F F' ω) = f' := w.differentialCoeff_unique hf'
    have h2 : w.differentialCoeff (KaehlerDifferential.map K K' F F' ω) = c' * d :=
      w.differentialCoeff_unique (by rw [hmap, hdt, smul_smul])
    rw [← h1, h2]
  obtain ⟨dU, hdU⟩ := hdunit
  have hd0 : d ≠ 0 := by
    rw [← hdU]
    exact fun h => dU.ne_zero (Subtype.ext h)
  have hdinv : d⁻¹ ∈ w.toValuationSubring := by
    refine (w.mem_iff_ord_nonneg (inv_ne_zero hd0)).mpr ?_
    rw [Place.ord_inv, ← hdU, w.ord_coe_unit, neg_zero]
  have : c' = f' * d⁻¹ := by
    rw [hcoef, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
  rw [this]
  exact mul_mem hf'mem hdinv

end S_AlgebraicCurve_exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension (solution)
