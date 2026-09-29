-- Prove2me | solution 1 for AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_mul_pullbackAlong_restrictAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c2335a99-8f0c-583a-9250-80bd8d769331

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_kaehlerD_ne_zero_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_D_eq_smul_D_of_ord_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_mul_pullbackAlong_restrictAlong
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open KaehlerDifferential AlgebraicCurve

noncomputable section

namespace ResPullbackE107

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {f : F} (hf : f ≠ 0) (hmem : f ∈ v.toValuationSubring)
    (hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) : 0 < v.ord f := by
  have h0 : 0 ≤ v.ord f := ord_nonneg_of_mem v hmem
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
    rw [← h, zpow_zero, mul_one] at hu
    have : (⟨f, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [this] at hmax
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax u.isUnit

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) {f : F} (h : 0 < v.ord f) (hmem : f ∈ v.toValuationSubring) :
    (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  change v.ord f = 0 at this
  omega

theorem mk_mem_maximalIdeal_iff (v : Place K F) {f : F} (hmem : f ∈ v.toValuationSubring) :
    (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ f = 0 ∨ 0 < v.ord f := by
  constructor
  · intro h
    rcases eq_or_ne f 0 with rfl | hf
    · exact Or.inl rfl
    · exact Or.inr (ord_pos_of_mem_maximalIdeal v hf hmem h)
  · rintro (rfl | h)
    · have : (⟨(0 : F), hmem⟩ : v.toValuationSubring) = 0 := Subtype.ext rfl
      rw [this]; exact Ideal.zero_mem _
    · exact mem_maximalIdeal_of_ord_pos v h hmem

theorem hasValue_iff_sub (v : Place K F) (g : F) (a : K) :
    v.HasValue g a ↔ ∃ h : g ∈ v.toValuationSubring, (g - algebraMap K F a = 0 ∨ 0 < v.ord (g - algebraMap K F a)) := by
  have hmemA : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  constructor
  · rintro ⟨hg, hres⟩
    refine ⟨hg, ?_⟩
    rw [← mk_mem_maximalIdeal_iff v (sub_mem hg hmemA), ← IsLocalRing.residue_eq_zero_iff]
    have : (⟨g - algebraMap K F a, sub_mem hg hmemA⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring a := Subtype.ext rfl
    rw [this, map_sub, hres, v.residue_algebraMap, sub_self]
  · rintro ⟨hg, h⟩
    refine ⟨hg, ?_⟩
    rw [← mk_mem_maximalIdeal_iff v (sub_mem hg hmemA), ← IsLocalRing.residue_eq_zero_iff] at h
    have : (⟨g - algebraMap K F a, sub_mem hg hmemA⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring a := Subtype.ext rfl
    rw [this, map_sub, sub_eq_zero, v.residue_algebraMap] at h
    exact h

theorem hasValue_algebraMap_add (v : Place K F) (a : K) {m : F} (hm : m ∈ v.toValuationSubring)
    (hmax : m = 0 ∨ 0 < v.ord m) : v.HasValue (algebraMap K F a + m) a := by
  rw [hasValue_iff_sub]
  refine ⟨add_mem (v.algebraMap_mem' a) hm, ?_⟩
  rw [add_sub_cancel_left]
  exact hmax

theorem hasValue_map {F' : Type*} [Field F'] [Algebra K F'] (φ : F →ₐ[K] F') (v : Place K F) (w : Place K F')
    (hmem : ∀ f : F, f ∈ v.toValuationSubring ↔ φ f ∈ w.toValuationSubring)
    (hord : ∀ f : F, f ≠ 0 → (0 < v.ord f ↔ 0 < w.ord (φ f)))
    {g : F} {a : K} (hv : v.HasValue g a) : w.HasValue (φ g) a := by
  rw [hasValue_iff_sub] at hv ⊢
  obtain ⟨hg, h⟩ := hv
  refine ⟨(hmem g).mp hg, ?_⟩
  have hφ : φ g - algebraMap K F' a = φ (g - algebraMap K F a) := by rw [map_sub, AlgHom.commutes]
  rw [hφ]
  rcases h with h | h
  · left; rw [h, map_zero]
  · right
    have hne : g - algebraMap K F a ≠ 0 := fun h0 => by rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
    exact (hord _ hne).mp h

theorem exists_coeff [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (ω : Ω[F⁄K]) : ∃ c : F, ω = c • D K F t := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (D K F t) hDt).mp IsCurveOver.finrank_kaehler ω
  exact ⟨c, hc.symm⟩

end ResPullbackE107

end

open ResPullbackE107 KaehlerDifferential in

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [PerfectField K]
    {x : F} (htr : Transcendental K x) (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    {x' : F'} (htr' : Transcendental K x') (hfd' : FiniteDimensional ↥(IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F') (ω : Ω[F⁄K]) :
    ((w.restrictAlong φ hφ).IsRegularAt ω → w.IsRegularAt (AlgebraicCurve.Differential.pullbackAlong φ ω)) ∧
    ((w.restrictAlong φ hφ).HasSimplePoleAt ω → w.HasSimplePoleAt (AlgebraicCurve.Differential.pullbackAlong φ ω)) ∧
    (∀ r : K, (w.restrictAlong φ hφ).HasSimpleResidue ω r →
      w.HasSimpleResidue (AlgebraicCurve.Differential.pullbackAlong φ ω) ((w.ramificationIndexAlong φ : K) * r)) := by
  classical
  haveI : IsCurveOver K F' := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr' hfd'
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K ({x'} : Set F')) F' := hfd'
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({x'} : Set F')) F' := Algebra.IsAlgebraic.of_finite _ _

  set v : Place K F := w.restrictAlong φ hφ with hvdef
  set e : ℕ := w.ramificationIndexAlong φ with hedef
  set t : F := v.uniformizer with htdef
  set t' : F' := w.uniformizer with ht'def
  have ht : v.ord t = 1 := v.ord_uniformizer
  have ht' : w.ord t' = 1 := w.ord_uniformizer
  have ht0 : t ≠ 0 := v.uniformizer_ne_zero
  have ht'0 : t' ≠ 0 := w.uniformizer_ne_zero
  have hdc : v.dCoord = D K F t := v.dCoord_eq
  have hdc' : w.dCoord = D K F' t' := w.dCoord_eq
  have ht'mem : t' ∈ w.toValuationSubring := w.uniformizer_mem_toValuationSubring
  have hDt' : D K F' t' ≠ 0 := AlgebraicCurve.Place.kaehlerD_ne_zero_of_ord_eq_one x' w ht'

  have hmemφ : ∀ f : F, f ∈ v.toValuationSubring ↔ φ f ∈ w.toValuationSubring := fun f => Iff.rfl
  have hordφ : ∀ f : F, w.ord (φ f) = (e : ℤ) * v.ord f := fun f => Place.ord_restrictAlong φ hφ w f
  have he : 0 < e := by
    letI := algebraAlong φ
    haveI := isIntegral_along φ hφ
    exact w.ramificationIndex_pos (F := F)
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hordφ' : ∀ f : F, f ≠ 0 → (0 < v.ord f ↔ 0 < w.ord (φ f)) := by
    intro f _
    rw [hordφ, mul_pos_iff_of_pos_left heZ]

  have hφt0 : φ t ≠ 0 := (map_ne_zero_iff _ hφinj).mpr ht0
  have hφt_ord : w.ord (φ t) = e := by rw [hordφ, ht, mul_one]
  obtain ⟨uU, huU⟩ := w.exists_unit_mul_zpow hφt0 w.irreducible_mk_uniformizer
  set u : F' := ((uU : w.toValuationSubring) : F') with hudef
  have hu_mem : u ∈ w.toValuationSubring := (uU : w.toValuationSubring).2
  have hu0 : u ≠ 0 := by
    intro h0
    have : (uU : w.toValuationSubring) = 0 := Subtype.ext h0
    exact uU.ne_zero this
  have hu_ord : w.ord u = 0 := w.ord_coe_unit uU
  have huinv_mem : u⁻¹ ∈ w.toValuationSubring :=
    mem_of_ord_nonneg w (by rw [w.ord_inv, hu_ord, neg_zero])
  have hφt : φ t = u * t' ^ e := by
    rw [hφt_ord, zpow_natCast] at huU
    exact huU
  have hpow : t' ^ e = t' ^ (e - 1) * t' := by rw [← pow_succ, Nat.sub_add_cancel he]

  obtain ⟨u', hu'⟩ := exists_coeff hDt' (D K F' u)
  have hu'_ord : 0 ≤ w.ord u' :=
    AlgebraicCurve.Place.ord_nonneg_of_D_eq_smul_D_of_ord_eq_one x' w ht' (by rw [hu_ord]) hu'
  have hu'_mem : u' ∈ w.toValuationSubring := mem_of_ord_nonneg w hu'_ord

  set c : F' := t' ^ (e - 1) * ((e : F') * u + t' * u') with hcdef
  have hc_mem : c ∈ w.toValuationSubring :=
    mul_mem (pow_mem ht'mem _) (add_mem (mul_mem (natCast_mem _ e) hu_mem) (mul_mem ht'mem hu'_mem))
  have hDφt : D K F' (φ t) = c • D K F' t' := by
    rw [hφt, Derivation.leibniz, Derivation.leibniz_pow, hu', smul_smul, ← Nat.cast_smul_eq_nsmul F' e, smul_smul,
      smul_smul, ← add_smul, hcdef]
    congr 1
    rw [hpow]
    ring
  have hmaster : ∀ f : F, AlgebraicCurve.Differential.pullbackAlong φ (f • v.dCoord) = (φ f * c) • w.dCoord := by
    intro f
    rw [hdc, AlgebraicCurve.Differential.pullbackAlong_smul, AlgebraicCurve.Differential.pullbackAlong_D, hDφt,
      smul_smul, hdc']

  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨φ f * c, mul_mem ((hmemφ f).mp hf) hc_mem, hmaster f⟩
  · rintro ⟨f, htf, rfl⟩
    refine ⟨φ f * c, ?_, hmaster f⟩
    have eq : t' * (φ f * c) = u⁻¹ * φ (t * f) * ((e : F') * u + t' * u') := by
      rw [map_mul, hφt, hcdef, hpow]
      field_simp
    rw [eq]
    exact mul_mem (mul_mem huinv_mem ((hmemφ _).mp htf)) (add_mem (mul_mem (natCast_mem _ e) hu_mem) (mul_mem ht'mem hu'_mem))
  · rintro r ⟨f, rfl, hval⟩
    refine ⟨φ f * c, hmaster f, ?_⟩

    have eq : t' * (φ f * c) = φ (t * f) * (algebraMap K F' (e : K) + t' * u' * u⁻¹) := by
      rw [map_mul, hφt, hcdef, hpow, map_natCast]
      field_simp
    have hv' : w.HasValue (φ (t * f)) r := hasValue_map φ v w hmemφ hordφ' hval
    have hm_mem : t' * u' * u⁻¹ ∈ w.toValuationSubring := mul_mem (mul_mem ht'mem hu'_mem) huinv_mem
    have hm : t' * u' * u⁻¹ = 0 ∨ 0 < w.ord (t' * u' * u⁻¹) := by
      by_cases h0 : u' = 0
      · left; rw [h0, mul_zero, zero_mul]
      · right
        rw [w.ord_mul (mul_ne_zero ht'0 h0) (inv_ne_zero hu0), w.ord_mul ht'0 h0, ht', w.ord_inv, hu_ord]
        omega
    have h2 : w.HasValue (algebraMap K F' (e : K) + t' * u' * u⁻¹) (e : K) := hasValue_algebraMap_add w (e : K) hm_mem hm
    rw [eq, mul_comm ((w.ramificationIndexAlong φ : ℕ) : K) r]
    exact hv'.mul h2

end S_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_mul_pullbackAlong_restrictAlong
end P2MW
export P2MW.S_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_mul_pullbackAlong_restrictAlong (solution)
