-- Prove2me | solution 1 for AlgebraicCurve.Place.ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7b561334-19fa-5881-8eed-c12741542f1b

import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
set_option autoImplicit false
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero.AlgebraicCurve KaehlerDifferential"
namespace FtameBuild

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem pullbackDiff_smul' (φ : F →ₐ[K] F') (g : F) (ω : Ω[F⁄K]) :
    pullbackDiff φ (g • ω) = φ g • pullbackDiff φ ω := by
  letI : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  show (KaehlerDifferential.map K K F F') (g • ω) = φ g • (KaehlerDifferential.map K K F F') ω
  rw [map_smul]
  exact (algebraMap_smul F' g _).symm

private theorem ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w' : Place K F') : 0 < Place.ramificationIndexAlong φ w' := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w'.ramificationIndex_pos (F := F)

private theorem ordDiff_pullbackDiff_of_local (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w' : Place K F') {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    (hspan : ∃ g : F, ω = g • D K F (w'.restrictAlong φ hφ).uniformizer_alt)
    (hadd : ∀ (a : F') (η : Ω[F'⁄K]), a ≠ 0 → η ≠ 0 →
      w'.ordDiff (a • η) = w'.ord a + w'.ordDiff η)
    (hDt : D K F' (φ (w'.restrictAlong φ hφ).uniformizer_alt) ≠ 0)
    (hR6a : w'.ordDiff (D K F' (φ (w'.restrictAlong φ hφ).uniformizer_alt))
      = (Place.ramificationIndexAlong φ w' : ℤ) - 1) :
    w'.ordDiff (pullbackDiff φ ω)
      = (Place.ramificationIndexAlong φ w' : ℤ) * (w'.restrictAlong φ hφ).ordDiff ω
        + ((Place.ramificationIndexAlong φ w' : ℤ) - 1) := by
  set w := w'.restrictAlong φ hφ with hw
  set t := w.uniformizer_alt with ht
  have hrep : ω = Place.diffCoeff t ω • D K F t := (Place.diffCoeff_smul_D hspan).symm
  set g := Place.diffCoeff t ω with hg
  have hg0 : g ≠ 0 := by
    intro h0
    apply hω
    rw [hrep, h0, zero_smul]
  have hφg : φ g ≠ 0 := (map_ne_zero φ).mpr hg0
  have hpull : pullbackDiff φ ω = φ g • D K F' (φ t) := by
    conv_lhs => rw [hrep]
    rw [pullbackDiff_smul', pullbackDiff_D]
  rw [hpull, hadd (φ g) _ hφg hDt, hR6a, Place.ord_restrictAlong φ hφ w' g, Place.ordDiff_def]

section Discharge

variable [PerfectField K]

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w' : Place K F')

omit [PerfectField K] in

private theorem ord_phi_uniformizer :
    w'.ord (φ (w'.restrictAlong φ hφ).uniformizer_alt) = (Place.ramificationIndexAlong φ w' : ℤ) := by
  rw [Place.ord_restrictAlong φ hφ w',
    (w'.restrictAlong φ hφ).ord_uniformizer_alt (w'.restrictAlong φ hφ).exists_ord_eq_one, mul_one]

omit [PerfectField K] in
private theorem ord_phi_uniformizer_ne_zero :
    w'.ord (φ (w'.restrictAlong φ hφ).uniformizer_alt) ≠ 0 := by
  rw [ord_phi_uniformizer φ hφ w']
  exact_mod_cast (ramificationIndexAlong_pos φ hφ w').ne'

private theorem hadd (x : F') [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F'] :
    ∀ (a : F') (η : Ω[F'⁄K]), a ≠ 0 → η ≠ 0 → w'.ordDiff (a • η) = w'.ord a + w'.ordDiff η := by
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F')) F' :=
    Algebra.IsAlgebraic.of_finite _ _
  exact fun _ _ ha hη => Place.ordDiff_smul_of_perfectField x w' ha hη

private theorem hspan (x₀ : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (ω : Ω[F⁄K]) : ∃ g : F, ω = g • D K F (w'.restrictAlong φ hφ).uniformizer_alt := by
  set w := w'.restrictAlong φ hφ
  set t := w.uniformizer_alt
  have ht1 : w.ord t = 1 := w.ord_uniformizer_alt w.exists_ord_eq_one
  have htr : Transcendental K t := w.transcendental_of_ord_ne_zero (ht1 ▸ one_ne_zero)
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F :=
    Place.isSeparable_adjoin_of_ord_eq_one x₀ w ht1
  exact (KaehlerDifferential.exists_unique_smul_D_of_transcendental K t htr ω).exists

omit [PerfectField K] in

private theorem ord_algebraMap_eq_zero {c : K} (hc : c ≠ 0) :
    w'.ord (algebraMap K F' c) = 0 := by
  have hne : algebraMap K F' c ≠ 0 := (map_ne_zero _).mpr hc
  have h1 : 0 ≤ w'.ord (algebraMap K F' c) :=
    (Place.mem_iff_ord_nonneg _ hne).mp (w'.algebraMap_mem' c)
  have h2 : 0 ≤ w'.ord (algebraMap K F' c)⁻¹ := by
    rw [show (algebraMap K F' c)⁻¹ = algebraMap K F' c⁻¹ from (map_inv₀ _ c).symm]
    exact (Place.mem_iff_ord_nonneg _ ((map_ne_zero _).mpr (inv_ne_zero hc))).mp
      (w'.algebraMap_mem' c⁻¹)
  rw [Place.ord_inv] at h2
  omega

omit [PerfectField K] in

private theorem diffCoeff_eq_of_eq_smul {t : F'} (hDt : D K F' t ≠ 0) {ω : Ω[F'⁄K]} {g : F'}
    (h : ω = g • D K F' t) : Place.diffCoeff t ω = g := by
  have h1 : Place.diffCoeff t ω • D K F' t = ω := Place.diffCoeff_smul_D ⟨g, h⟩
  have h2 : (Place.diffCoeff t ω - g) • D K F' t = 0 := by
    rw [sub_smul, h1, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hDt

private theorem exists_good_coeff (x : F')
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F']
    (he : ((Place.ramificationIndexAlong φ w' : ℕ) : K) ≠ 0) :
    ∃ g₀ : F', g₀ ≠ 0 ∧
      D K F' (φ (w'.restrictAlong φ hφ).uniformizer_alt) = g₀ • D K F' w'.uniformizer_alt ∧
      w'.ord g₀ = (Place.ramificationIndexAlong φ w' : ℤ) - 1 := by
  classical
  set e := Place.ramificationIndexAlong φ w' with hedef
  have hepos : 0 < e := ramificationIndexAlong_pos φ hφ w'
  set s := φ (w'.restrictAlong φ hφ).uniformizer_alt with hsdef
  have hords : w'.ord s = (e : ℤ) := ord_phi_uniformizer φ hφ w'
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hords
    omega
  set u := w'.uniformizer_alt with hudef
  have hu1 : w'.ord u = 1 := w'.ord_uniformizer_alt w'.exists_ord_eq_one
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hu1
    exact one_ne_zero hu1.symm
  have hupow : u ^ (e : ℕ) ≠ 0 := pow_ne_zero _ hune
  have hordupow : w'.ord (u ^ (e : ℕ)) = (e : ℤ) := by
    rw [show u ^ (e : ℕ) = u ^ ((e : ℕ) : ℤ) from (zpow_natCast u e).symm,
      Place.ord_zpow, hu1, mul_one]

  set c : F' := s / u ^ (e : ℕ) with hcdef
  have hcne : c ≠ 0 := div_ne_zero hsne hupow
  have hordc : w'.ord c = 0 := by
    rw [hcdef, div_eq_mul_inv, w'.ord_mul hsne (inv_ne_zero hupow), Place.ord_inv,
      hordupow, hords]
    ring
  have hs_eq : s = c * u ^ (e : ℕ) := (div_mul_cancel₀ s hupow).symm

  have heF : ((e : ℕ) : F') ≠ 0 := by
    rw [show ((e : ℕ) : F') = algebraMap K F' ((e : ℕ) : K) from (map_natCast _ e).symm]
    exact (map_ne_zero _).mpr he
  have hordeF : w'.ord ((e : ℕ) : F') = 0 := by
    rw [show ((e : ℕ) : F') = algebraMap K F' ((e : ℕ) : K) from (map_natCast _ e).symm]
    exact ord_algebraMap_eq_zero w' he

  have htr : Transcendental K u := w'.transcendental_of_ord_ne_zero (by rw [hu1]; exact one_ne_zero)
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({u} : Set F')) F' :=
    Place.isSeparable_adjoin_of_ord_eq_one x w' hu1
  have hDu : D K F' u ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K u htr
  set cv := Place.diffCoeff u (D K F' c) with hcvdef
  have hDc : D K F' c = cv • D K F' u :=
    (Place.diffCoeff_smul_D
      ((KaehlerDifferential.exists_unique_smul_D_of_transcendental K u htr (D K F' c)).exists)).symm
  have hcv0 : 0 ≤ w'.ord cv :=
    Place.ord_diffCoeff_D_nonneg_of_isSeparable x w' hu1 (le_of_eq hordc.symm)

  have hmain : s = c * u ^ (e : ℕ) := hs_eq
  have hD : D K F' s = (c * ((e : ℕ) : F') * u ^ ((e : ℕ) - 1) + u ^ (e : ℕ) * cv) • D K F' u := by
    conv_lhs => rw [hs_eq]
    rw [Derivation.leibniz, Derivation.leibniz_pow, hDc]
    rw [← Nat.cast_smul_eq_nsmul F' e (u ^ ((e : ℕ) - 1) • D K F' u)]
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]

  have hmne : c * ((e : ℕ) : F') * u ^ ((e : ℕ) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcne heF) (pow_ne_zero _ hune)
  have hordmain : w'.ord (c * ((e : ℕ) : F') * u ^ ((e : ℕ) - 1)) = (e : ℤ) - 1 := by
    rw [w'.ord_mul (mul_ne_zero hcne heF) (pow_ne_zero _ hune),
      w'.ord_mul hcne heF, hordc, hordeF,
      show u ^ ((e : ℕ) - 1) = u ^ (((e : ℕ) - 1 : ℕ) : ℤ) from (zpow_natCast u _).symm,
      Place.ord_zpow, hu1, mul_one]
    have : (((e : ℕ) - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
    omega
  refine ⟨c * ((e : ℕ) : F') * u ^ ((e : ℕ) - 1) + u ^ (e : ℕ) * cv, ?_, hD, ?_⟩
  ·
    by_cases hcv : cv = 0
    · rw [hcv, mul_zero, add_zero]
      exact hmne
    · intro h0
      have h1 : c * ((e : ℕ) : F') * u ^ ((e : ℕ) - 1) = -(u ^ (e : ℕ) * cv) := by
        linear_combination h0
      have h2 : w'.ord (c * ((e : ℕ) : F') * u ^ ((e : ℕ) - 1))
          = w'.ord (u ^ (e : ℕ) * cv) := by
        rw [h1, show -(u ^ (e : ℕ) * cv) = (-1 : F') * (u ^ (e : ℕ) * cv) by ring,
          w'.ord_mul (by norm_num) (mul_ne_zero hupow hcv),
          show w'.ord (-1 : F') = 0 from by
            rw [show (-1 : F') = algebraMap K F' (-1) from by rw [map_neg, map_one]]
            exact ord_algebraMap_eq_zero w' (by norm_num), zero_add]
      rw [hordmain, w'.ord_mul hupow hcv, hordupow] at h2
      omega
  ·
    by_cases hcv : cv = 0
    · rw [hcv, mul_zero, add_zero, hordmain]
    · have hord2 : w'.ord (u ^ (e : ℕ) * cv) = (e : ℤ) + w'.ord cv := by
        rw [w'.ord_mul hupow hcv, hordupow]
      have hlt : w'.ord (c * ((e : ℕ) : F') * u ^ ((e : ℕ) - 1))
          < w'.ord (u ^ (e : ℕ) * cv) := by
        rw [hordmain, hord2]
        omega
      rw [Place.ord_add_eq_of_lt w' hmne (mul_ne_zero hupow hcv) hlt, hordmain]

private theorem hDt_of_tame (x : F')
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F']
    (he : ((Place.ramificationIndexAlong φ w' : ℕ) : K) ≠ 0) :
    D K F' (φ (w'.restrictAlong φ hφ).uniformizer_alt) ≠ 0 := by
  obtain ⟨g₀, hg₀, hDeq, -⟩ := exists_good_coeff φ hφ w' x he
  have hu1 : w'.ord w'.uniformizer_alt = 1 := w'.ord_uniformizer_alt w'.exists_ord_eq_one
  have htr : Transcendental K w'.uniformizer_alt :=
    w'.transcendental_of_ord_ne_zero (by rw [hu1]; exact one_ne_zero)
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin K ({w'.uniformizer_alt} : Set F')) F' :=
    Place.isSeparable_adjoin_of_ord_eq_one x w' hu1
  have hDu : D K F' w'.uniformizer_alt ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental K _ htr
  rw [hDeq]
  exact smul_ne_zero hg₀ hDu

private theorem hR6a_of_tame (x : F')
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F']
    (he : ((Place.ramificationIndexAlong φ w' : ℕ) : K) ≠ 0) :
    w'.ordDiff (D K F' (φ (w'.restrictAlong φ hφ).uniformizer_alt))
      = (Place.ramificationIndexAlong φ w' : ℤ) - 1 := by
  obtain ⟨g₀, -, hDeq, hord⟩ := exists_good_coeff φ hφ w' x he
  have hu1 : w'.ord w'.uniformizer_alt = 1 := w'.ord_uniformizer_alt w'.exists_ord_eq_one
  have htr : Transcendental K w'.uniformizer_alt :=
    w'.transcendental_of_ord_ne_zero (by rw [hu1]; exact one_ne_zero)
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin K ({w'.uniformizer_alt} : Set F')) F' :=
    Place.isSeparable_adjoin_of_ord_eq_one x w' hu1
  have hDu : D K F' w'.uniformizer_alt ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental K _ htr
  rw [Place.ordDiff_def, diffCoeff_eq_of_eq_smul hDu hDeq, hord]

end Discharge

end FtameBuild

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place.diffCoeff Place.diffCoeff_smul_D Place.ordDiff_def pullbackDiff pullbackDiff_D Place Place.ord_zero Place.ord_inv Place.ord_zpow Place.algebraMap_mem' algebraAlong isScalarTower_along isIntegral_along Place.ramificationIndexAlong Place.ord_restrictAlong Place.ordDiff_smul_of_perfectField Place.isSeparable_adjoin_of_ord_eq_one Place.ord_diffCoeff_D_nonneg_of_isSeparable Place.ord_add_eq_of_lt Place.mem_iff_ord_nonneg" namespace Place p2m_export "AlgebraicCurve.Place" "diffCoeff diffCoeff_smul_D ordDiff ordDiff_def ord_uniformizer_alt uniformizer_alt ord ord_zero ord_mul ord_inv ord_zpow algebraMap_mem' restrictAlong ramificationIndexAlong ord_restrictAlong ramificationIndex_pos ordDiff_smul_of_perfectField exists_ord_eq_one transcendental_of_ord_ne_zero isSeparable_adjoin_of_ord_eq_one ord_diffCoeff_D_nonneg_of_isSeparable ord_add_eq_of_lt mem_iff_ord_nonneg" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

private theorem AlgebraicCurve.Place.solution_impl
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [PerfectField K]
    (x₀ : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (x : F') [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w' : Place K F') {ω : Ω[F⁄K]}
    (hω : ω ≠ 0)
    (he : ((Place.ramificationIndexAlong φ w' : ℕ) : K) ≠ 0) :
    w'.ordDiff (pullbackDiff φ ω)
      = (Place.ramificationIndexAlong φ w' : ℤ) * (w'.restrictAlong φ hφ).ordDiff ω
        + ((Place.ramificationIndexAlong φ w' : ℤ) - 1) :=
  FtameBuild.ordDiff_pullbackDiff_of_local φ hφ w' hω (FtameBuild.hspan φ hφ w' x₀ ω)
    (FtameBuild.hadd w' x) (FtameBuild.hDt_of_tame φ hφ w' x he)
    (FtameBuild.hR6a_of_tame φ hφ w' x he)

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [PerfectField K]
    (x₀ : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (x : F') [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w' : Place K F') {ω : Ω[F⁄K]}
    (hω : ω ≠ 0)
    (he : ((Place.ramificationIndexAlong φ w' : ℕ) : K) ≠ 0) :
    w'.ordDiff (pullbackDiff φ ω)
      = (Place.ramificationIndexAlong φ w' : ℤ) * (w'.restrictAlong φ hφ).ordDiff ω
        + ((Place.ramificationIndexAlong φ w' : ℤ) - 1) :=
  AlgebraicCurve.Place.solution_impl x₀ x φ hφ w' hω he

end S_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero (solution)
