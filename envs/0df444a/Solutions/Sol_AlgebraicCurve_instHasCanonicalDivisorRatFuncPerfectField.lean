-- Prove2me | solution 1 for AlgebraicCurve.instHasCanonicalDivisorRatFuncPerfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/05de7966-77b9-5809-a832-e5be3d3b6c52

import Mathlib
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver
p2m_open "AlgebraicCurve.IsCurveOver"
variable {K F}
end IsCurveOver
namespace Place
p2m_export "AlgebraicCurve.Place" "dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul ext deg adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ofHeightOneSpectrum toValuationSubring uniformizer ord_uniformizer uniformizer_ne_zero isEquiv_adicValuation_of_valuationSubring_eq ord_eq_zero_iff_adicValuation_eq_one ord_ofHeightOneSpectrum_ne_zero_iff ord_neg mem_of_ord_nonneg ord_nonneg_of_mem"
p2m_open "AlgebraicCurve.Place~algebraMap_ne_zero"
variable {K F}
variable (v : Place K F)
end Place
variable {K F}
variable (K F)

def OrdDifferentialWellDefined : Prop :=
  ∀ (v : Place K F) (π π' : F), v.ord π = 1 → v.ord π' = 1 →
    ∃ u : F, v.ord u = 0 ∧
      KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π
end AlgebraicCurve
namespace ModularCurve
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve"
end ModularCurve
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"
variable (K F : Type*) [Field K] [Field F] [Algebra K F]
end AlgebraicCurve
namespace ModularCurve
end ModularCurve
end

section

set_option autoImplicit false

noncomputable section

p2m_open "IsDedekindDomain WithZero Module IsLocalRing Module.IsLocalRing KaehlerDifferential Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

open scoped Polynomial

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)]

abbrev dX : Ω[(RatFunc K)⁄K] := KaehlerDifferential.D K (RatFunc K) RatFunc.X

theorem aeval_ratFuncX_eq_algebraMap (q : K[X]) :
    aeval (RatFunc.X : RatFunc K) q = algebraMap K[X] (RatFunc K) q := by
  rw [← RatFunc.algebraMap_X,
    show algebraMap K[X] (RatFunc K) X = IsScalarTower.toAlgHom K K[X] (RatFunc K) X from rfl,
    aeval_algHom_apply, aeval_X_left_apply]
  rfl

theorem D_algebraMap_polynomial (q : K[X]) :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) q)
      = algebraMap K[X] (RatFunc K) q.derivative • dX K := by
  rw [← aeval_ratFuncX_eq_algebraMap K q, (D K (RatFunc K)).map_aeval q RatFunc.X,
    aeval_ratFuncX_eq_algebraMap K q.derivative]

theorem denom_sq_smul_D_eq (f : RatFunc K) :
    (algebraMap K[X] (RatFunc K) f.denom) ^ 2 • KaehlerDifferential.D K (RatFunc K) f
      = algebraMap K[X] (RatFunc K)
          (f.num.derivative * f.denom - f.num * f.denom.derivative) • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hDf : KaehlerDifferential.D K (RatFunc K) f
      = ((algebraMap K[X] (RatFunc K) f.denom)⁻¹ ^ 2) •
        (algebraMap K[X] (RatFunc K) f.denom • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
          - algebraMap K[X] (RatFunc K) f.num
              • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom)) := by
    conv_lhs => rw [← f.num_div_denom, (D K (RatFunc K)).leibniz_div]
  rw [hDf, smul_smul, ← mul_pow, mul_inv_cancel₀ hd, one_pow, one_smul,
    D_algebraMap_polynomial K f.num, D_algebraMap_polynomial K f.denom,
    smul_smul, smul_smul, ← sub_smul]
  push_cast
  ring_nf

theorem span_dX_eq_top :
    Submodule.span (RatFunc K) {dX K} = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero

  have hsq : ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
        * (algebraMap K[X] (RatFunc K) f.denom) ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hd)
  refine Submodule.mem_span_singleton.mpr ⟨((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
    * algebraMap K[X] (RatFunc K)
        (f.num.derivative * f.denom - f.num * f.denom.derivative), ?_⟩
  rw [mul_smul, ← denom_sq_smul_D_eq K f, smul_smul, hsq, one_smul]

theorem dX_ne_zero [Nontrivial Ω[(RatFunc K)⁄K]] : dX K ≠ 0 := by
  intro h0
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(RatFunc K)⁄K])
  have hω_mem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hω_mem
  exact hω hω_mem

theorem not_dvd_derivative_of_sq_not_dvd {p : K[X]} (hp : Irreducible p) (hsep : p.Separable)
    {q : K[X]} (hpq : p ∣ q) (hpq2 : ¬ p ^ 2 ∣ q) : ¬ p ∣ q.derivative := by
  obtain ⟨m, rfl⟩ := hpq
  have hpm : ¬ p ∣ m := fun ⟨r, hr⟩ => hpq2 ⟨r, by rw [hr]; ring⟩
  intro hpdvd
  rw [derivative_mul] at hpdvd
  have hpdvd' : p ∣ p.derivative * m := by
    have := dvd_sub hpdvd (dvd_mul_right p m.derivative)
    rwa [add_sub_cancel_right] at this
  rcases hp.prime.dvd_mul.mp hpdvd' with hpp' | hpm'
  ·
    exact hp.not_isUnit (hsep.isUnit_of_dvd' dvd_rfl hpp')
  · exact hpm hpm'

variable {K}

theorem not_dvd_derivative_of_ord_eq_one {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {q : K[X]} (hq : q ≠ 0)
    (hord : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 1) :
    ¬ p ∣ q.derivative := by
  have hwmem : ∀ {r : K[X]}, r ≠ 0 →
      ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) ≠ 0 ↔ p ∣ r) := fun {r} hr => by
    rw [Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hr,
      hwp, Ideal.mem_span_singleton]
  have hordp : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 1 :=
    ord_ofHeightOneSpectrum_of_span w hp.ne_zero hwp
  refine not_dvd_derivative_of_sq_not_dvd K hp hsep
    ((hwmem hq).mp (hord ▸ one_ne_zero)) ?_

  rintro ⟨r, rfl⟩
  have hr : r ≠ 0 := fun h => hq (by simp [h])
  have : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) (p ^ 2 * r)) ≥ 2 := by
    have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
    have hr0 : algebraMap K[X] (RatFunc K) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hr
    rw [map_mul, map_pow,
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_mul (pow_ne_zero 2 hp0) hr0,
      ← zpow_natCast, (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_zpow,
      hordp, mul_one]
    have : 0 ≤ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) :=
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_nonneg_of_mem
        (algebraMap_mem_ofHeightOneSpectrum K w r)
    omega
  omega

section NumDenom

variable {w : HeightOneSpectrum K[X]}

local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

private theorem uniformizer_ne_zero'_PFFRTP1DC : (v).uniformizer ≠ 0 :=
  (v).uniformizer_ne_zero

theorem ord_algebraMap_denom_uniformizer_eq_zero {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    (v).ord (algebraMap K[X] (RatFunc K) (v).uniformizer.denom) = 0 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'_PFFRTP1DC
  by_contra hne

  have hpd : p ∣ π.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ π.num := fun hpn =>
    hp.not_isUnit (π.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (v).ord (algebraMap K[X] (RatFunc K) π.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hπne)).mp h)
  have hordd : 0 < (v).ord (algebraMap K[X] (RatFunc K) π.denom) :=
    lt_of_le_of_ne ((v).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)) (Ne.symm hne)

  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : (v).ord π = 1 := (v).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, hordn] at hordπ
  omega

theorem ord_algebraMap_num_uniformizer_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) :
    (v).ord (algebraMap K[X] (RatFunc K) (v).uniformizer.num) = 1 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'_PFFRTP1DC
  have hnum0 : algebraMap K[X] (RatFunc K) π.num ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (RatFunc.num_ne_zero hπne)
  have hden0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero
  have hordπ : (v).ord π = 1 := (v).ord_uniformizer
  rw [← π.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, ord_algebraMap_denom_uniformizer_eq_zero hp hwp] at hordπ
  omega

theorem not_dvd_num'denom_sub_numdenom' {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    ¬ p ∣ ((v).uniformizer.num.derivative * (v).uniformizer.denom
            - (v).uniformizer.num * (v).uniformizer.denom.derivative) := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'_PFFRTP1DC
  have hpn' : ¬ p ∣ π.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hπne)
      (ord_algebraMap_num_uniformizer_eq_one hp hwp)
  have hpd : ¬ p ∣ π.denom := fun hpd => by
    have := ord_algebraMap_denom_uniformizer_eq_zero (w := w) hp hwp
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      π.denom_ne_zero).mpr hpd this
  have hpn : p ∣ π.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hπne)).mp ?_
    rw [ord_algebraMap_num_uniformizer_eq_one hp hwp]; exact one_ne_zero
  intro hdvd

  have hpnd' : p ∣ π.num * π.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ π.num.derivative * π.denom := by
    have := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at this
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

end NumDenom

section PerPlace

variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable {w : HeightOneSpectrum K[X]}

local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

theorem ord_differentialCoeff_dX_ofHeightOneSpectrum {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable) :
    (v).ord ((v).differentialCoeff (dX K)) = 0 := by
  set π := (v).uniformizer with hπ
  have hπne : π ≠ 0 := uniformizer_ne_zero'_PFFRTP1DC
  set ξ : K[X] := π.num.derivative * π.denom - π.num * π.denom.derivative with hξ
  have hd0 : algebraMap K[X] (RatFunc K) π.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr π.denom_ne_zero

  have hcoord : (v).dCoord
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2) • dX K := by
    rw [div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K π, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hd0), one_smul]
    rfl

  have hξ0 : ξ ≠ 0 := by
    intro h; rw [hξ] at h
    exact not_dvd_num'denom_sub_numdenom' hp hwp hsep (h ▸ dvd_zero p)
  have hcoeff0 : algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2 ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (pow_ne_zero 2 hd0)

  have hcoeff : (v).differentialCoeff (dX K)
      = (algebraMap K[X] (RatFunc K) ξ / (algebraMap K[X] (RatFunc K) π.denom) ^ 2)⁻¹ := by
    refine (v).differentialCoeff_unique ?_
    rw [hcoord, smul_smul, inv_mul_cancel₀ hcoeff0, one_smul]

  have hordξ : (v).ord (algebraMap K[X] (RatFunc K) ξ) = 0 := by
    by_contra h
    refine not_dvd_num'denom_sub_numdenom' hp hwp hsep ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  rw [hcoeff, (v).ord_inv, div_eq_mul_inv,
    (v).ord_mul ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hξ0)
      (inv_ne_zero (pow_ne_zero 2 hd0)),
    hordξ, (v).ord_inv, ← zpow_natCast, (v).ord_zpow,
    ord_algebraMap_denom_uniformizer_eq_zero hp hwp]
  ring
end PerPlace
section Discharge
variable (K)
variable [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end Discharge
section Gates
variable (K)
variable [CharZero K] [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Gates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end

section

set_option autoImplicit false

noncomputable section

p2m_open "IsDedekindDomain WithZero Module IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

open scoped Polynomial

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"

variable {K : Type*} [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] [DecidableEq (RatFunc K)]

variable (K)
section InftyVanish
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end InftyVanish
section NamedSubrow
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end NamedSubrow
section MOneReduction
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
end MOneReduction
section ComposedEngine
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
end ComposedEngine
section UnitFinite
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]

def P1DifferentialCoeffUnitFinite {ω₀ : Ω[(RatFunc K)⁄K]} (_hω₀ : ω₀ ≠ 0) : Prop :=
  ∀ v : Place K (RatFunc K), v ≠ placeInfty K → v.ord (v.differentialCoeff ω₀) = 0

variable {K}

end UnitFinite
section Gates
variable {K}
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
end Gates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end

section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul ext deg adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ofHeightOneSpectrum toValuationSubring uniformizer ord_uniformizer uniformizer_ne_zero isEquiv_adicValuation_of_valuationSubring_eq ord_eq_zero_iff_adicValuation_eq_one ord_ofHeightOneSpectrum_ne_zero_iff ord_neg mem_of_ord_nonneg ord_nonneg_of_mem"
p2m_open "AlgebraicCurve.Place~algebraMap_ne_zero"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
section OfHeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]
end OfHeightOneSpectrum
end Place
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "exists_irreducible_span algebraMap_mem_ofHeightOneSpectrum placeInfty placeInfty_toValuationSubring deg_placeInfty eq_ofHeightOneSpectrum_or_eq_placeInfty ord_ofHeightOneSpectrum_of_span ord_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]
section PlaceInfty
variable [DecidableEq (RatFunc K)]

theorem inftyValuation_isEquiv_adicValuation :
    (RatFunc.inftyValuation K).IsEquiv (placeInfty K).adicValuation :=
  (placeInfty K).isEquiv_adicValuation_of_valuationSubring_eq rfl
end PlaceInfty
variable {K}
section ResidueDegree
variable (K)
end ResidueDegree
section DegInfty
variable (K) [DecidableEq (RatFunc K)]

theorem exists_sub_algebraMap_intDegree_neg {x : RatFunc K}
    (hx : RatFunc.inftyValuation K x ≤ 1) :
    ∃ c : K, x - algebraMap K (RatFunc K) c = 0 ∨
      (x - algebraMap K (RatFunc K) c).intDegree < 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, Or.inl (by simp)⟩
  have hdeg : x.intDegree ≤ 0 := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hx0,
      show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hx
    exact hx
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden0 : x.denom ≠ 0 := x.denom_ne_zero
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, Or.inr (by simpa using hlt)⟩

  have hndeg : x.num.natDegree = x.denom.natDegree := by
    have h2 := heq
    rw [RatFunc.intDegree, sub_eq_zero] at h2
    exact_mod_cast h2
  set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnum0)
      (Polynomial.leadingCoeff_ne_zero.mpr hden0)
  refine ⟨c, ?_⟩
  have hsub : x - algebraMap K (RatFunc K) c
      = algebraMap K[X] (RatFunc K) (x.num - Polynomial.C c * x.denom)
        / algebraMap K[X] (RatFunc K) x.denom := by
    rw [map_sub, map_mul, sub_div, x.num_div_denom, mul_div_assoc,
      div_self ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
      mul_one, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  rcases eq_or_ne (x.num - Polynomial.C c * x.denom) 0 with hzero | hnz
  · exact Or.inl (by rw [hsub, hzero, map_zero, zero_div])
  refine Or.inr ?_
  rw [hsub, RatFunc.intDegree_div ((map_ne_zero_iff _
      (IsFractionRing.injective K[X] (RatFunc K))).mpr hnz)
    ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_neg]

  have hCdeg : (Polynomial.C c * x.denom).degree = x.denom.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hc0, zero_add]
  have hdegeq : x.num.degree = (Polynomial.C c * x.denom).degree := by
    rw [hCdeg, Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_eq_natDegree hden0,
      hndeg]
  have hlc : x.num.leadingCoeff = (Polynomial.C c * x.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
      div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hden0)]
  have hlt := Polynomial.degree_sub_lt hdegeq hnum0 hlc
  rw [hdegeq, hCdeg] at hlt
  exact_mod_cast Polynomial.natDegree_lt_natDegree hnz hlt
end DegInfty
end RationalFunctionField
end AlgebraicCurve
end

section

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

section SubsingletonCriterion

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
end SubsingletonCriterion
namespace Place
p2m_export "AlgebraicCurve.Place" "dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul ext deg adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ofHeightOneSpectrum toValuationSubring uniformizer ord_uniformizer uniformizer_ne_zero isEquiv_adicValuation_of_valuationSubring_eq ord_eq_zero_iff_adicValuation_eq_one ord_ofHeightOneSpectrum_ne_zero_iff ord_neg mem_of_ord_nonneg ord_nonneg_of_mem"
p2m_open "AlgebraicCurve.Place~algebraMap_ne_zero"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
end Place
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "exists_irreducible_span algebraMap_mem_ofHeightOneSpectrum placeInfty placeInfty_toValuationSubring deg_placeInfty eq_ofHeightOneSpectrum_or_eq_placeInfty ord_ofHeightOneSpectrum_of_span ord_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]
section PlaceInfty
variable [DecidableEq (RatFunc K)]

theorem ord_placeInfty_eq_zero_of_intDegree_eq_zero {f : RatFunc K} (hf : f ≠ 0)
    (h : f.intDegree = 0) : (placeInfty K).ord f = 0 := by
  rw [(placeInfty K).ord_eq_zero_iff_adicValuation_eq_one hf,
    ← (inftyValuation_isEquiv_adicValuation K).eq_one_iff_eq_one,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, h]
  rfl

theorem ord_placeInfty_eq_intDegree_mul {f : RatFunc K} (hf : f ≠ 0) :
    (placeInfty K).ord f = f.intDegree * (placeInfty K).ord (RatFunc.X) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)

  have hpoly : ∀ q : K[X], q ≠ 0 →
      (placeInfty K).ord (algebraMap K[X] (RatFunc K) q)
        = (q.natDegree : ℤ) * (placeInfty K).ord (RatFunc.X) := by
    intro q hq
    have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq
    have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
    have hXpow : (RatFunc.X : RatFunc K) ^ q.natDegree ≠ 0 := pow_ne_zero _ hX

    have hXpoly : (RatFunc.X : RatFunc K) ^ q.natDegree
        = algebraMap K[X] (RatFunc K) (Polynomial.X ^ q.natDegree) := by
      rw [map_pow, RatFunc.algebraMap_X]
    have hdeg : (algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree).intDegree = 0 := by
      rw [RatFunc.intDegree_div hq' hXpow, RatFunc.intDegree_polynomial, hXpoly,
        RatFunc.intDegree_polynomial, natDegree_X_pow, sub_self]
    have hne : algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree ≠ 0 :=
      div_ne_zero hq' hXpow
    have h0 := ord_placeInfty_eq_zero_of_intDegree_eq_zero K hne hdeg
    have hsplit : algebraMap K[X] (RatFunc K) q
        = (algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree)
          * RatFunc.X ^ q.natDegree :=
      (div_mul_cancel₀ _ hXpow).symm
    rw [hsplit, (placeInfty K).ord_mul hne hXpow, h0, zero_add, ← zpow_natCast,
      (placeInfty K).ord_zpow]
  have hnum' : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.num_ne_zero hf)
  have hden' : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr f.denom_ne_zero
  rw [show f = algebraMap K[X] (RatFunc K) f.num * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ by
      rw [← div_eq_mul_inv, f.num_div_denom],
    (placeInfty K).ord_mul hnum' (inv_ne_zero hden'), (placeInfty K).ord_inv,
    hpoly _ (RatFunc.num_ne_zero hf), hpoly _ f.denom_ne_zero, ← div_eq_mul_inv,
    RatFunc.intDegree_div hnum' hden', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]
  ring

theorem ord_placeInfty_X : (placeInfty K).ord (RatFunc.X : RatFunc K) = -1 := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero

  have hneg : (placeInfty K).ord (RatFunc.X : RatFunc K) < 0 := by
    by_contra h
    have hmem : (RatFunc.X : RatFunc K) ∈ (placeInfty K).toValuationSubring :=
      (placeInfty K).mem_of_ord_nonneg hX (not_lt.mp h)
    rw [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
      RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hX,
      RatFunc.intDegree_X, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hmem
    omega

  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (placeInfty K).toValuationSubring
  have hπ0 : (π : RatFunc K) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hdvd : (placeInfty K).ord (RatFunc.X : RatFunc K) ∣ 1 := by
    rw [← (placeInfty K).ord_coe_irreducible hπ, ord_placeInfty_eq_intDegree_mul K hπ0]
    exact Dvd.intro_left _ rfl
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h <;> omega
end PlaceInfty
section Principal
variable {K}
end Principal
end RationalFunctionField
namespace Place
p2m_export "AlgebraicCurve.Place" "dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul ext deg adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ofHeightOneSpectrum toValuationSubring uniformizer ord_uniformizer uniformizer_ne_zero isEquiv_adicValuation_of_valuationSubring_eq ord_eq_zero_iff_adicValuation_eq_one ord_ofHeightOneSpectrum_ne_zero_iff ord_neg mem_of_ord_nonneg ord_nonneg_of_mem"
p2m_open "AlgebraicCurve.Place~algebraMap_ne_zero"
section Congr
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F')
variable (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include he
end Congr
end Place
namespace Pic0
p2m_open "AlgebraicCurve.Pic0"
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include e he
end Pic0
end AlgebraicCurve
namespace ModularCurve
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve IntermediateField"
end ModularCurve
end

section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem canonicalDivisorOf_eq_of_forall [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : ∀ v : Place K F, D v = v.ordDifferential ω) :
    canonicalDivisorOf hω = D :=
  Finsupp.ext fun v => by rw [canonicalDivisorOf_apply hω v, ← hD v]

end Uniqueness

section Profile

variable (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)]

theorem exists_smul_dX_eq (ω : Ω[(RatFunc K)⁄K]) : ∃ c : RatFunc K, c • dX K = ω := by
  have hmem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  exact Submodule.mem_span_singleton.mp hmem

section ProfileValues

variable [CharZero K] [DecidableEq (RatFunc K)]
end ProfileValues
section Instance
variable [CharZero K]
end Instance
section ExactDivisor
variable [CharZero K] [DecidableEq (RatFunc K)]
end ExactDivisor
end Profile
section RatDiamond
end RatDiamond
end AlgebraicCurve
namespace ModularCurve
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve IntermediateField"
end ModularCurve
section AxiomAudit
end AxiomAudit
end

section

set_option autoImplicit false

noncomputable section

p2m_open "IsDedekindDomain WithZero Module IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul ext deg adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ofHeightOneSpectrum toValuationSubring uniformizer ord_uniformizer uniformizer_ne_zero isEquiv_adicValuation_of_valuationSubring_eq ord_eq_zero_iff_adicValuation_eq_one ord_ofHeightOneSpectrum_ne_zero_iff ord_neg mem_of_ord_nonneg ord_nonneg_of_mem"
p2m_open "AlgebraicCurve.Place~algebraMap_ne_zero"

variable (v : Place K F)
end Place
namespace Place
p2m_export "AlgebraicCurve.Place" "dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul ext deg adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ofHeightOneSpectrum toValuationSubring uniformizer ord_uniformizer uniformizer_ne_zero isEquiv_adicValuation_of_valuationSubring_eq ord_eq_zero_iff_adicValuation_eq_one ord_ofHeightOneSpectrum_ne_zero_iff ord_neg mem_of_ord_nonneg ord_nonneg_of_mem"
p2m_open "AlgebraicCurve.Place~algebraMap_ne_zero"
variable (v : Place K F)
end Place
namespace Place p2m_export "AlgebraicCurve.Place" "dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul ext deg adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ofHeightOneSpectrum toValuationSubring uniformizer ord_uniformizer uniformizer_ne_zero isEquiv_adicValuation_of_valuationSubring_eq ord_eq_zero_iff_adicValuation_eq_one ord_ofHeightOneSpectrum_ne_zero_iff ord_neg mem_of_ord_nonneg ord_nonneg_of_mem" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.differentialCoeff_ne_zero (v : Place K F) [v.DCoordGenerates]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : v.differentialCoeff ω ≠ 0 := fun h =>
  hω (by rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul])
end Place
p2m_export "AlgebraicCurve" "Place.differentialCoeff_ne_zero"
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]
variable (K F)
variable {K F}
variable (K F)
variable {K F}
variable (K F)
variable {K F}
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end
end

section

set_option autoImplicit false

noncomputable section

p2m_open "IsDedekindDomain WithZero Module IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

open scoped Polynomial
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] [DecidableEq (RatFunc K)]

theorem D_ratFuncX_eq_neg_X_sq_smul_D_inv :
    KaehlerDifferential.D K (RatFunc K) RatFunc.X
      = (-(RatFunc.X : RatFunc K) ^ 2) •
          KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ :=
  (KaehlerDifferential.D K (RatFunc K)).leibniz_of_mul_eq_one
    (mul_inv_cancel₀ RatFunc.X_ne_zero)

theorem ord_placeInfty_X_inv : (placeInfty K).ord (RatFunc.X : RatFunc K)⁻¹ = 1 := by
  rw [(placeInfty K).ord_inv, ord_placeInfty_X, neg_neg]

theorem ord_placeInfty_X_pow (n : ℕ) :
    (placeInfty K).ord ((RatFunc.X : RatFunc K) ^ n) = -(n : ℤ) := by
  rw [show ((RatFunc.X : RatFunc K) ^ n) = (RatFunc.X : RatFunc K) ^ (n : ℤ) from
    (zpow_natCast _ n).symm, (placeInfty K).ord_zpow, ord_placeInfty_X]
  ring
section NonVanishing
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem D_ratFuncX_inv_ne_zero (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := by
  obtain ⟨u, -, hueq⟩ :=
    hwd (placeInfty K) (RatFunc.X : RatFunc K)⁻¹ (placeInfty K).uniformizer
      (ord_placeInfty_X_inv K) (placeInfty K).ord_uniformizer
  intro h0
  refine (placeInfty K).dCoord_ne_zero ?_
  show KaehlerDifferential.D K (RatFunc K) (placeInfty K).uniformizer = 0
  rw [hueq, h0, smul_zero]
end NonVanishing
section DifferentialCoeff
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem differentialCoeff_placeInfty_D_X_eq :
    (placeInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      = (-(RatFunc.X : RatFunc K) ^ 2) *
          (placeInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹) := by
  rw [D_ratFuncX_eq_neg_X_sq_smul_D_inv, (placeInfty K).differentialCoeff_smul]

theorem ord_differentialCoeff_placeInfty_D_X_inv_eq_zero
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (placeInfty K).ord
        ((placeInfty K).differentialCoeff
          (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)) = 0 := by
  obtain ⟨u, hu0, hueq⟩ :=
    hwd (placeInfty K) (placeInfty K).uniformizer (RatFunc.X : RatFunc K)⁻¹
      (placeInfty K).ord_uniformizer (ord_placeInfty_X_inv K)
  rw [(placeInfty K).differentialCoeff_unique
    (show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹
        = u • (placeInfty K).dCoord from hueq), hu0]
end DifferentialCoeff
section OrdDifferential
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

theorem ordDifferential_placeInfty_D_ratFuncX
    (hwd : OrdDifferentialWellDefined K (RatFunc K)) :
    (placeInfty K).ordDifferential
        (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)) = -2 := by
  rw [Place.ordDifferential, differentialCoeff_placeInfty_D_X_eq K, neg_mul,
    (placeInfty K).ord_neg,
    (placeInfty K).ord_mul (pow_ne_zero 2 RatFunc.X_ne_zero)
      ((placeInfty K).differentialCoeff_ne_zero (D_ratFuncX_inv_ne_zero K hwd)),
    ord_placeInfty_X_pow K 2, ord_differentialCoeff_placeInfty_D_X_inv_eq_zero K hwd]
  norm_num
end OrdDifferential
section Factorisation
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Factorisation
section NamedSubrow
end NamedSubrow
section Bridge
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Bridge
section Gates
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end Gates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

section

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
namespace Place
p2m_export "AlgebraicCurve.Place" "dCoord DCoordGenerates dCoord_ne_zero differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul ordDifferential ordDifferential_smul ext deg adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ofHeightOneSpectrum toValuationSubring uniformizer ord_uniformizer uniformizer_ne_zero isEquiv_adicValuation_of_valuationSubring_eq ord_eq_zero_iff_adicValuation_eq_one ord_ofHeightOneSpectrum_ne_zero_iff ord_neg mem_of_ord_nonneg ord_nonneg_of_mem"
p2m_open "AlgebraicCurve.Place~algebraMap_ne_zero AlgebraicCurve"

section Ultrametric

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_add_eq_left {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by

  have hfv := v.adicValuation_ne_zero hf
  have hgv := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← exp_log hfv, ← exp_log hgv]
    have hlog : log (v.adicValuation g) < log (v.adicValuation f) := by
      simp only [ord] at h
      omega
    exact lt_of_le_of_ne (exp_le_exp.mpr hlog.le)
      fun hcon => hlog.ne (exp_injective hcon)
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ (ne_of_lt hlt).symm
  rw [max_eq_left hlt.le] at h1
  simp only [ord, h1]

p2m_export "AlgebraicCurve.Place" "ord_add_eq_left"
end Ultrametric

section SumLeFinrank

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

end SumLeFinrank
end AlgebraicCurve.Place
namespace ModularCurve
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve"
section RationalFunctionFieldInfty
end RationalFunctionFieldInfty
section Tower
variable (p : ℕ) [NeZero p]
end Tower
section Degree
variable (p : ℕ) [NeZero p]
end Degree
section Restriction
variable {p : ℕ} [NeZero p]
end Restriction
section Assembly
variable {p : ℕ} [NeZero p]
end Assembly
end ModularCurve
end

section

set_option autoImplicit false

noncomputable section

p2m_open "IsDedekindDomain WithZero Module IsLocalRing Module.IsLocalRing KaehlerDifferential Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

open scoped Polynomial

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"

section WronskianBound

variable {K : Type*} [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)]

theorem natDegree_numDenomWronskian_lt {n d : K[X]} (hn : n ≠ 0) (hd : d ≠ 0)
    (hW : n.derivative * d - n * d.derivative ≠ 0) :
    (n.derivative * d - n * d.derivative).natDegree < n.natDegree + d.natDegree := by
  have hdeg : (n.derivative * d - n * d.derivative).degree < (n * d).degree := by
    rw [Polynomial.degree_mul]
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_right (Polynomial.degree_ne_bot.mpr hd)]
      exact Polynomial.degree_derivative_lt hn
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_left (Polynomial.degree_ne_bot.mpr hn)]
      exact Polynomial.degree_derivative_lt hd
  have h2 := Polynomial.natDegree_lt_natDegree hW hdeg
  rwa [Polynomial.natDegree_mul hn hd] at h2

end WronskianBound

section DXCoeff

variable (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)]

def ratFuncDXCoeff (f : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
    / (algebraMap K[X] (RatFunc K) f.denom) ^ 2

theorem ratFuncDXCoeff_def (f : RatFunc K) :
    ratFuncDXCoeff K f
      = algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
        / (algebraMap K[X] (RatFunc K) f.denom) ^ 2 := rfl

theorem D_eq_ratFuncDXCoeff_smul_dX (f : RatFunc K) :
    KaehlerDifferential.D K (RatFunc K) f = ratFuncDXCoeff K f • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [ratFuncDXCoeff_def, div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K f,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hd), one_smul]

theorem wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero {f : RatFunc K}
    (h : ratFuncDXCoeff K f ≠ 0) :
    f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := by
  intro h0
  exact h (by rw [ratFuncDXCoeff_def, h0, map_zero, zero_div])

end DXCoeff

section FinitePlaces

variable {K : Type*} [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
variable {w : HeightOneSpectrum K[X]}

local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w

theorem ord_algebraMap_denom_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : (v).ord f = 1) :
    (v).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne

  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (v).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < (v).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne ((v).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)

  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, hordn] at hord
  omega

theorem ord_algebraMap_num_eq_one_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : (v).ord f = 1) :
    (v).ord (algebraMap K[X] (RatFunc K) f.num) = 1 := by
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have h := hord
  rw [← f.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord] at h
  omega

theorem not_dvd_wronskian_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : (v).ord f = 1) :
    ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) := by
  have hpn' : ¬ p ∣ f.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hf)
      (ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord)
  have hpd : ¬ p ∣ f.denom := fun hpd => by
    have h0 := ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mpr hpd h0
  have hpn : p ∣ f.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hf)).mp ?_
    rw [ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord]
    exact one_ne_zero
  intro hdvd

  have hpnd' : p ∣ f.num * f.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ f.num.derivative * f.denom := by
    have h1 := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at h1
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

theorem ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : (v).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ (v).ord (ratFuncDXCoeff K f) = 0 := by
  have hW : ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) :=
    not_dvd_wronskian_of_ord_eq_one hp hwp hsep hf hord
  have hξ0 : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := fun h =>
    hW (h ▸ dvd_zero p)
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hξ0' : algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hξ0

  have hordξ : (v).ord (algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative)) = 0 := by
    by_contra h
    refine hW ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  refine ⟨div_ne_zero hξ0' (pow_ne_zero 2 hd0), ?_⟩
  rw [ratFuncDXCoeff_def, div_eq_mul_inv,
    (v).ord_mul hξ0' (inv_ne_zero (pow_ne_zero 2 hd0)), (v).ord_inv, hordξ,
    ← zpow_natCast, (v).ord_zpow,
    ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord]
  ring

end FinitePlaces

section PlaceInftySide

variable {K : Type*} [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] [DecidableEq (RatFunc K)]

theorem ord_placeInfty_ratFuncDXCoeff_ge {g : RatFunc K} (hg : g ≠ 0)
    (hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0) :
    (placeInfty K).ord g + 1 ≤ (placeInfty K).ord (ratFuncDXCoeff K g) := by
  have hn0 : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hd0 : g.denom ≠ 0 := g.denom_ne_zero
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := RatFunc.algebraMap_ne_zero hd0

  have hdeg : (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree
      < g.num.natDegree + g.denom.natDegree :=
    natDegree_numDenomWronskian_lt hn0 hd0 hW

  have hcoeff : (placeInfty K).ord (ratFuncDXCoeff K g)
      = 2 * (g.denom.natDegree : ℤ)
        - (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree := by
    rw [ratFuncDXCoeff_def, ord_placeInfty (div_ne_zero hW' (pow_ne_zero 2 hd')),
      RatFunc.intDegree_div hW' (pow_ne_zero 2 hd'), RatFunc.intDegree_polynomial,
      ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_pow]
    push_cast
    ring

  have hgord : (placeInfty K).ord g = (g.denom.natDegree : ℤ) - g.num.natDegree := by
    rw [ord_placeInfty hg, RatFunc.intDegree]
    ring
  rw [hcoeff, hgord]
  omega

theorem exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero {g : RatFunc K}
    (hg : g ≠ 0) (hord : (placeInfty K).ord g = 0) :
    ∃ e : RatFunc K, (e = 0 ∨ 2 ≤ (placeInfty K).ord e) ∧
      KaehlerDifferential.D K (RatFunc K) g = e • dX K := by

  have hmem : RatFunc.inftyValuation K g ≤ 1 := by
    have h1 : g ∈ (placeInfty K).toValuationSubring :=
      (placeInfty K).mem_of_ord_nonneg hg hord.symm.le
    rwa [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff] at h1

  obtain ⟨c, hc⟩ := exists_sub_algebraMap_intDegree_neg K hmem

  have hDg : KaehlerDifferential.D K (RatFunc K) g
      = KaehlerDifferential.D K (RatFunc K) (g - algebraMap K (RatFunc K) c) := by
    rw [map_sub, Derivation.map_algebraMap (KaehlerDifferential.D K (RatFunc K)) c, sub_zero]
  rcases hc with hc0 | hcneg
  ·
    exact ⟨0, Or.inl rfl, by rw [hDg, hc0, map_zero, zero_smul]⟩
  ·
    have hg₁0 : g - algebraMap K (RatFunc K) c ≠ 0 := by
      intro h0
      rw [h0] at hcneg
      simp at hcneg
    refine ⟨ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c), ?_,
      by rw [hDg, D_eq_ratFuncDXCoeff_smul_dX]⟩
    rcases eq_or_ne (ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c)) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      have hW := wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K h0
      have hge := ord_placeInfty_ratFuncDXCoeff_ge hg₁0 hW
      have hord₁ : 1 ≤ (placeInfty K).ord (g - algebraMap K (RatFunc K) c) := by
        rw [ord_placeInfty hg₁0]
        omega
      omega

theorem exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one {h : RatFunc K}
    (hh : h ≠ 0) (hord : (placeInfty K).ord h = -1) :
    ∃ b : RatFunc K, b ≠ 0 ∧ (placeInfty K).ord b = 0 ∧
      KaehlerDifferential.D K (RatFunc K) h = b • dX K := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hXinv : (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := inv_ne_zero hX

  have hg0 : h * (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := mul_ne_zero hh hXinv
  have hordg : (placeInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹) = 0 := by
    rw [(placeInfty K).ord_mul hh hXinv, (placeInfty K).ord_inv, ord_placeInfty_X, hord]
    ring
  obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg0 hordg

  have hh_eq : h = h * (RatFunc.X : RatFunc K)⁻¹ * RatFunc.X := by
    rw [mul_assoc, inv_mul_cancel₀ hX, mul_one]
  have hDh : KaehlerDifferential.D K (RatFunc K) h
      = (h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e) • dX K := by
    conv_lhs => rw [hh_eq]
    rw [Derivation.leibniz, hDe, smul_smul,
      show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) = dX K from rfl,
      ← add_smul]
  rcases he with rfl | he2
  ·
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * 0, ?_, ?_, hDh⟩
    · rw [mul_zero, add_zero]
      exact hg0
    · rw [mul_zero, add_zero]
      exact hordg
  ·
    have he0 : e ≠ 0 := by
      intro h0
      rw [h0, (placeInfty K).ord_zero] at he2
      omega
    have hXe0 : (RatFunc.X : RatFunc K) * e ≠ 0 := mul_ne_zero hX he0
    have hlt : (placeInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹)
        < (placeInfty K).ord ((RatFunc.X : RatFunc K) * e) := by
      rw [hordg, (placeInfty K).ord_mul hX he0, ord_placeInfty_X]
      omega
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e, ?_, ?_, hDh⟩
    ·
      intro hsum
      have hXe_eq : (RatFunc.X : RatFunc K) * e = -(h * (RatFunc.X : RatFunc K)⁻¹) := by
        linear_combination hsum
      rw [hXe_eq, (placeInfty K).ord_neg] at hlt
      exact lt_irrefl _ hlt
    · rw [(placeInfty K).ord_add_eq_left hg0 hXe0 hlt]
      exact hordg

theorem exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one {f : RatFunc K}
    (hf : f ≠ 0) (hord : (placeInfty K).ord f = 1) :
    ∃ e : RatFunc K, e ≠ 0 ∧ (placeInfty K).ord e = 2 ∧
      KaehlerDifferential.D K (RatFunc K) f = e • dX K := by

  have hf' : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hord' : (placeInfty K).ord f⁻¹ = -1 := by
    rw [(placeInfty K).ord_inv, hord]
  obtain ⟨b, hb0, hbord, hDb⟩ := exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one hf' hord'
  refine ⟨-(f ^ 2 * b), neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hf) hb0), ?_, ?_⟩
  · rw [(placeInfty K).ord_neg, (placeInfty K).ord_mul (pow_ne_zero 2 hf) hb0, hbord,
      add_zero, ← zpow_natCast, (placeInfty K).ord_zpow, hord]
    norm_num
  ·
    conv_lhs => rw [← inv_inv f]
    rw [(KaehlerDifferential.D K (RatFunc K)).leibniz_inv f⁻¹, hDb, inv_inv, smul_smul,
      neg_mul]

end PlaceInftySide

section Glue

variable {K : Type*} [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)]

theorem exists_ord_zero_smul_of_smul_dX_eq {v : Place K (RatFunc K)} {π π' c c' : RatFunc K}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hord : v.ord c' = v.ord c)
    (hD : KaehlerDifferential.D K (RatFunc K) π = c • dX K)
    (hD' : KaehlerDifferential.D K (RatFunc K) π' = c' • dX K) :
    ∃ u : RatFunc K, v.ord u = 0 ∧
      KaehlerDifferential.D K (RatFunc K) π' = u • KaehlerDifferential.D K (RatFunc K) π := by
  refine ⟨c' / c, ?_, ?_⟩
  · rw [div_eq_mul_inv, v.ord_mul hc' (inv_ne_zero hc), v.ord_inv, hord]
    ring
  · rw [hD, hD', smul_smul, div_mul_cancel₀ _ hc]

end Glue
section ConsumerGates
variable (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ConsumerGates
section NonVacuity
variable (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
end NonVacuity
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

section

set_option autoImplicit false

noncomputable section

p2m_open "IsDedekindDomain WithZero Module IsLocalRing Module.IsLocalRing KaehlerDifferential Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

open scoped Polynomial

p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"

theorem ordDifferentialWellDefined_ratFunc_of_perfectField (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [PerfectField K] :
    OrdDifferentialWellDefined K (RatFunc K) := by
  classical
  intro v π π' hπ hπ'

  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ
    exact zero_ne_one hπ
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hπ'
    exact zero_ne_one hπ'

  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·

    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨h1ne, h1ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp) hπ0 hπ
    obtain ⟨h2ne, h2ord⟩ :=
      ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp) hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq h1ne h2ne (h2ord.trans h1ord.symm)
      (D_eq_ratFuncDXCoeff_smul_dX K π) (D_eq_ratFuncDXCoeff_smul_dX K π')
  ·
    obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ0 hπ
    obtain ⟨e', he'0, he'ord, hDe'⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hπ'0 hπ'
    exact exists_ord_zero_smul_of_smul_dX_eq he0 he'0 (he'ord.trans heord.symm) hDe hDe'

section ConsumerGates
variable (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] [CharZero K] [DecidableEq (RatFunc K)]
variable [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
end ConsumerGates
end AlgebraicCurve
section AxiomAudit
end AxiomAudit
end

section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.placeInfty IsCurveOver"
p2m_open "AlgebraicCurve"

scoped instance instNonemptyPlaceRatFuncLaneB (K : Type*) [Field K] : Nonempty (Place K (RatFunc K)) :=
  ⟨by classical exact RationalFunctionField.placeInfty K⟩

theorem genus_eq_degree_div {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] [Nontrivial Ω[F⁄K]] :
    ∃ (ω₀ : Ω[F⁄K]) (hω₀ : ω₀ ≠ 0),
      genus K F = (Divisor.degree (canonicalDivisorOf hω₀) + 2).toNat / 2 := by
  have hne : ∃ ω : Ω[F⁄K], ω ≠ 0 := exists_ne 0
  refine ⟨hne.choose, hne.choose_spec, ?_⟩
  rw [genus, dif_pos hne]

open scoped Polynomial
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"

section PerfectDCoord

variable (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] [PerfectField K]

theorem exists_ne_zero_smul_dX_of_uniformizer (v : Place K (RatFunc K)) :
    ∃ c : RatFunc K, c ≠ 0 ∧
      KaehlerDifferential.D K (RatFunc K) v.uniformizer = c • dX K := by
  classical
  have hord : v.ord v.uniformizer = 1 := v.ord_uniformizer
  have hpi0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨hne, -⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
      (PerfectField.separable_of_irreducible hp) hpi0 hord
    exact ⟨ratFuncDXCoeff K _, hne, D_eq_ratFuncDXCoeff_smul_dX K _⟩
  ·
    obtain ⟨e, he0, -, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hpi0 hord
    exact ⟨e, he0, hDe⟩

namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "exists_irreducible_span algebraMap_mem_ofHeightOneSpectrum placeInfty placeInfty_toValuationSubring deg_placeInfty eq_ofHeightOneSpectrum_or_eq_placeInfty ord_ofHeightOneSpectrum_of_span ord_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField"

scoped instance (priority := low) instDCoordGeneratesPerfectField (v : Place K (RatFunc K)) :
    v.DCoordGenerates := by
  obtain ⟨c, hc0, hDc⟩ := exists_ne_zero_smul_dX_of_uniformizer K v
  refine ⟨?_⟩
  have hdc : v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer := rfl
  rw [hdc, hDc, eq_top_iff, ← span_dX_eq_top K, Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_span_singleton.mpr
    ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"
end PerfectDCoord
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"
section Profile
variable (K : Type*) [Field K] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
section PerfectProfileValues
variable [PerfectField K] [DecidableEq (RatFunc K)]

theorem p1DifferentialCoeffUnitFinite_dX_of_perfectField :
    P1DifferentialCoeffUnitFinite K (dX_ne_zero K) := by
  intro v hvinf
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    exact ord_differentialCoeff_dX_ofHeightOneSpectrum hp hwp
      (PerfectField.separable_of_irreducible hp)
  · exact absurd rfl hvinf

theorem ordDifferential_dX_of_ne_placeInfty_of_perfectField {v : Place K (RatFunc K)}
    (hv : v ≠ placeInfty K) : v.ordDifferential (dX K) = 0 := by
  rw [Place.ordDifferential]
  exact p1DifferentialCoeffUnitFinite_dX_of_perfectField K v hv

theorem ordDifferential_dX_placeInfty_of_perfectField :
    (placeInfty K).ordDifferential (dX K) = -2 :=
  ordDifferential_placeInfty_D_ratFuncX K
    (ordDifferentialWellDefined_ratFunc_of_perfectField K)

theorem exists_divisor_smul_dX_of_perfectField {c : RatFunc K} (hc : c ≠ 0) :
    ∃ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ordDifferential (c • dX K)) ∧
        Divisor.degree D = -2 := by
  obtain ⟨Dc, hDc, hDcdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := RatFunc K) c hc
  refine ⟨Dc + Finsupp.single (placeInfty K) (-2), fun v => ?_, ?_⟩
  ·
    rw [Finsupp.add_apply, hDc v,
      v.ordDifferential_smul hc (v.differentialCoeff_ne_zero (dX_ne_zero K))]
    rcases eq_or_ne v (placeInfty K) with rfl | hne
    · rw [ordDifferential_dX_placeInfty_of_perfectField K, Finsupp.single_eq_same]
    · rw [ordDifferential_dX_of_ne_placeInfty_of_perfectField K hne,
        Finsupp.single_eq_of_ne hne]
  ·
    rw [map_add, hDcdeg, zero_add, Divisor.degree_single, deg_placeInfty K, Nat.cast_one,
      mul_one]

end PerfectProfileValues
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"

section PerfectInstance

variable [PerfectField K]

scoped instance instHasCanonicalDivisorRatFuncPerfectField_s17 :
    HasCanonicalDivisor (K := K) (F := RatFunc K) where
  exists_divisor ω hω := by
    classical
    obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hω hc.symm
    obtain ⟨D, hD, -⟩ := exists_divisor_smul_dX_of_perfectField K hc0
    refine ⟨D, fun v => ?_⟩
    rw [← hc]
    exact hD v

theorem degree_canonicalDivisorOf_ratFunc_of_perfectField_s17 {ω : Ω[(RatFunc K)⁄K]}
    (hω : ω ≠ 0) : Divisor.degree (canonicalDivisorOf hω) = -2 := by
  classical
  obtain ⟨c, hc⟩ := exists_smul_dX_eq K ω
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hω hc.symm
  obtain ⟨D, hD, hDdeg⟩ := exists_divisor_smul_dX_of_perfectField K hc0
  have heq : canonicalDivisorOf hω = D := by
    refine canonicalDivisorOf_eq_of_forall hω fun v => ?_
    rw [← hc]
    exact hD v
  rw [heq, hDdeg]

theorem genus_ratFunc_eq_zero_of_perfectField_s17 : genus K (RatFunc K) = 0 := by
  obtain ⟨ω₀, hω₀, hgen⟩ := genus_eq_degree_div (K := K) (F := RatFunc K)
  rw [hgen, degree_canonicalDivisorOf_ratFunc_of_perfectField_s17 K hω₀]
  norm_num
end PerfectInstance
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"
section PerfectExactDivisor
variable [PerfectField K] [DecidableEq (RatFunc K)]
end PerfectExactDivisor
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"
section CharZeroRoutes
variable [CharZero K]
end CharZeroRoutes
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"
end Profile
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"
section FiniteFieldReadings
end FiniteFieldReadings
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve"
section AxiomAudit
end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.AlgebraicCurve"

theorem solution (K : Type*) [Field K] [PerfectField K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] : AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K) :=
  AlgebraicCurve.instHasCanonicalDivisorRatFuncPerfectField_s17 K

theorem solution_degree (K : Type*) [Field K] [PerfectField K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    {ω : Ω[RatFunc K⁄K]} (hω : ω ≠ 0) : AlgebraicCurve.Divisor.degree (AlgebraicCurve.canonicalDivisorOf hω) = -2 :=
  AlgebraicCurve.degree_canonicalDivisorOf_ratFunc_of_perfectField_s17 K hω

theorem solution_genus (K : Type*) [Field K] [PerfectField K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)] :
    AlgebraicCurve.genus K (RatFunc K) = 0 :=
  AlgebraicCurve.genus_ratFunc_eq_zero_of_perfectField_s17 K

end
end
end
end
end
end
end
end
end
end S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField
end P2MW
export P2MW.S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField (solution)
