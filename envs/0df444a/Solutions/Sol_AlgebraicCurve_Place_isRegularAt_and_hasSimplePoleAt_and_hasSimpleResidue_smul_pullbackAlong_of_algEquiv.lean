-- Prove2me | solution 1 for AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_smul_pullbackAlong_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3ac21c60-7afb-5a61-885e-4bf4d12e0a4a

import Mathlib
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_kaehlerD_ne_zero_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_D_eq_smul_D_of_ord_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_smul_pullbackAlong_of_algEquiv
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open KaehlerDifferential AlgebraicCurve

noncomputable section

namespace CartierLocalPen12

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

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  let u : v.toValuationSubringˣ :=
    ⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  exact v.ord_coe_unit u

theorem coeff_unique {t : F} (hDt : D K F t ≠ 0) {g g' : F} (h : g • D K F t = g' • D K F t) : g = g' := by
  have h' : (g - g') • D K F t = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h' with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hDt

theorem exists_coeff [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (ω : Ω[F⁄K]) : ∃ c : F, ω = c • D K F t := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (D K F t) hDt).mp IsCurveOver.finrank_kaehler ω
  exact ⟨c, hc.symm⟩

noncomputable def deriv [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (h : F) : F :=
  (exists_coeff hDt (D K F h)).choose

theorem D_eq_deriv_smul [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (h : F) :
    D K F h = deriv hDt h • D K F t :=
  (exists_coeff hDt (D K F h)).choose_spec

theorem deriv_eq_of_D_eq [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) {h g : F} (hg : D K F h = g • D K F t) :
    deriv hDt h = g :=
  coeff_unique hDt ((D_eq_deriv_smul hDt h).symm.trans hg)

theorem deriv_add [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (h h' : F) :
    deriv hDt (h + h') = deriv hDt h + deriv hDt h' :=
  deriv_eq_of_D_eq hDt (by rw [map_add, D_eq_deriv_smul hDt h, D_eq_deriv_smul hDt h', add_smul])

theorem deriv_zero [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) : deriv hDt (0 : F) = 0 :=
  deriv_eq_of_D_eq hDt (by rw [map_zero, zero_smul])

theorem deriv_sum [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → F) :
    deriv hDt (∑ i ∈ s, f i) = ∑ i ∈ s, deriv hDt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, deriv_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, deriv_add, ih]

theorem deriv_pow_char_mul [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP F p] {t : F} (hDt : D K F t ≠ 0)
    (a h : F) : deriv hDt (a ^ p * h) = a ^ p * deriv hDt h := by
  apply deriv_eq_of_D_eq hDt
  have hDap : D K F (a ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F p, CharP.cast_eq_zero F p, zero_smul]
  rw [Derivation.leibniz, hDap, smul_zero, add_zero, D_eq_deriv_smul hDt h, smul_smul]

theorem deriv_natCast_mul [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP F p] {t : F} (hDt : D K F t ≠ 0)
    (m : ℕ) (h : F) : deriv hDt ((m : F) * h) = m * deriv hDt h := by
  have hm : ((m : F)) ^ p = m := by rw [← frobenius_def, map_natCast]
  rw [← hm, deriv_pow_char_mul p hDt, hm]

theorem deriv_t_pow [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (n : ℕ) :
    deriv hDt (t ^ n) = n * t ^ (n - 1) := by
  apply deriv_eq_of_D_eq hDt
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F n, smul_smul]

theorem deriv_iterate_pow_char_mul_t_pow [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP F p] {t : F} (hDt : D K F t ≠ 0)
    (a : F) (k n : ℕ) :
    (deriv hDt)^[k] (a ^ p * t ^ n) = a ^ p * ((Nat.descFactorial n k : F) * t ^ (n - k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, deriv_pow_char_mul p hDt, deriv_natCast_mul p hDt,
      deriv_t_pow hDt, Nat.descFactorial_succ, Nat.sub_sub, Nat.cast_mul]
    ring

theorem iterate_deriv_sum [IsCurveOver K F] {t : F} (hDt : D K F t ≠ 0) (k : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → F) : (deriv hDt)^[k] (∑ i ∈ s, f i) = ∑ i ∈ s, (deriv hDt)^[k] (f i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, deriv_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Function.iterate_succ_apply' (deriv hDt)]

theorem ord_iterate_deriv_nonneg [IsCurveOver K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) (hDt : D K F t ≠ 0) (k : ℕ) {h : F}
    (hh : 0 ≤ v.ord h) : 0 ≤ v.ord ((deriv hDt)^[k] h) := by
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact AlgebraicCurve.Place.ord_nonneg_of_D_eq_smul_D_of_ord_eq_one x v ht ih (D_eq_deriv_smul hDt _)

end CartierLocalPen12

namespace DiaTransportPen12

theorem hasValue_smul {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F) (v : Place K F)
    {x : F} {a : K} (h : v.HasValue x a) : (g • v).HasValue (g • x) (SemilinearAut.baseAut g a) := by
  obtain ⟨hx, hres⟩ := h
  have hmem : g • x ∈ (g • v).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g x v.toValuationSubring hx
  refine ⟨hmem, ?_⟩
  have key : IsLocalRing.residue (g • v).toValuationSubring
      (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨x, hx⟩) =
      SemilinearAut.smulResidueRingEquiv g v (IsLocalRing.residue v.toValuationSubring ⟨x, hx⟩) := by
    rw [SemilinearAut.smulResidueRingEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  have hx' : (⟨g • x, hmem⟩ : (g • v).toValuationSubring) =
      SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨x, hx⟩ := rfl
  rw [hx', key, hres, SemilinearAut.smulResidueRingEquiv_algebraMap]

theorem smul_mem_smul {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F) (v : Place K F)
    {x : F} (hx : x ∈ v.toValuationSubring) : g • x ∈ (g • v).toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.smul_mem_pointwise_smul g x v.toValuationSubring hx

end DiaTransportPen12

end

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    (σ : F ≃ₐ[K] F) (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    (v.IsRegularAt ω →
        (AlgebraicCurve.SemilinearAut.ofAlgAut σ • v).IsRegularAt (AlgebraicCurve.Differential.pullbackAlong σ.toAlgHom ω)) ∧
    (v.HasSimplePoleAt ω →
        (AlgebraicCurve.SemilinearAut.ofAlgAut σ • v).HasSimplePoleAt (AlgebraicCurve.Differential.pullbackAlong σ.toAlgHom ω)) ∧
    (∀ r : K, v.HasSimpleResidue ω r →
        (AlgebraicCurve.SemilinearAut.ofAlgAut σ • v).HasSimpleResidue (AlgebraicCurve.Differential.pullbackAlong σ.toAlgHom ω) r) := by
  classical
  haveI : AlgebraicCurve.IsCurveOver K F := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  haveI := hfd
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
  set g : SemilinearAut K F := SemilinearAut.ofAlgAut σ with hgdef
  set w := g • v with hwdef
  set t := v.uniformizer with htdef
  set t' := w.uniformizer with ht'def
  have ht : v.ord t = 1 := v.ord_uniformizer
  have ht' : w.ord t' = 1 := w.ord_uniformizer
  have ht0 : t ≠ 0 := v.uniformizer_ne_zero
  have ht'0 : t' ≠ 0 := w.uniformizer_ne_zero
  have hdc : v.dCoord = D K F t := v.dCoord_eq
  have hdc' : w.dCoord = D K F t' := w.dCoord_eq
  have hDt' : D K F t' ≠ 0 := AlgebraicCurve.Place.kaehlerD_ne_zero_of_ord_eq_one x w ht'
  have ht'mem : t' ∈ w.toValuationSubring := CartierLocalPen12.mem_of_ord_nonneg w (by rw [ht']; exact zero_le_one)

  have hσΩ : ∀ f h : F, Differential.pullbackAlong σ.toAlgHom (f • D K F h) = (g • f) • D K F (g • h) := by
    intro f h
    rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_D]
    rfl
  have hgt0 : g • t ≠ 0 := by
    intro h0; apply ht0
    have := congrArg (fun y => g⁻¹ • y) h0
    simpa using this
  have hσt_ord : w.ord (g • t) = 1 := by rw [hwdef, AlgebraicCurve.SemilinearAut.ord_smul]; exact ht
  set u : F := (g • t) * t'⁻¹ with hudef
  have hu0 : u ≠ 0 := mul_ne_zero hgt0 (inv_ne_zero ht'0)
  have hu_ord : w.ord u = 0 := by rw [hudef, w.ord_mul hgt0 (inv_ne_zero ht'0), w.ord_inv, hσt_ord, ht']; ring
  have hu_mem : u ∈ w.toValuationSubring := CartierLocalPen12.mem_of_ord_nonneg w (by rw [hu_ord])
  have huinv_mem : u⁻¹ ∈ w.toValuationSubring := CartierLocalPen12.mem_of_ord_nonneg w (by rw [w.ord_inv, hu_ord, neg_zero])
  have hgt : g • t = u * t' := by rw [hudef, mul_assoc, inv_mul_cancel₀ ht'0, mul_one]
  obtain ⟨u', hu'⟩ := CartierLocalPen12.exists_coeff hDt' (D K F u)
  have hu'_ord : 0 ≤ w.ord u' :=
    AlgebraicCurve.Place.ord_nonneg_of_D_eq_smul_D_of_ord_eq_one x w ht' (by rw [hu_ord]) hu'
  have hu'_mem : u' ∈ w.toValuationSubring := CartierLocalPen12.mem_of_ord_nonneg w hu'_ord
  set c : F := u + t' * u' with hcdef
  have hDgt : D K F (g • t) = c • D K F t' := by
    rw [hgt, Derivation.leibniz, hu', smul_smul, ← add_smul, hcdef, add_comm, mul_comm t' u']
  have hc_mem : c ∈ w.toValuationSubring := add_mem hu_mem (mul_mem ht'mem hu'_mem)
  have hmaster : ∀ f : F, Differential.pullbackAlong σ.toAlgHom (f • v.dCoord) = ((g • f) * c) • w.dCoord := by
    intro f
    rw [hdc, hσΩ, hDgt, smul_smul, hdc']
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨(g • f) * c, mul_mem (DiaTransportPen12.smul_mem_smul g v hf) hc_mem, hmaster f⟩
  · rintro ⟨f, htf, rfl⟩
    refine ⟨(g • f) * c, ?_, hmaster f⟩
    have e : t' * ((g • f) * c) = u⁻¹ * (g • (t * f)) * c := by
      rw [smul_mul', hgt]
      field_simp
      try ring
    rw [e]
    exact mul_mem (mul_mem huinv_mem (DiaTransportPen12.smul_mem_smul g v htf)) hc_mem
  · rintro r ⟨f, rfl, hval⟩
    refine ⟨(g • f) * c, hmaster f, ?_⟩
    have hv' : w.HasValue (g • (t * f)) r := by
      have h := DiaTransportPen12.hasValue_smul g v hval
      have hb : SemilinearAut.baseAut g r = r := by rw [hgdef, SemilinearAut.baseAut_ofAlgAut]; rfl
      rwa [hb] at h
    have e : t' * ((g • f) * c) = (g • (t * f)) * (1 + t' * u' * u⁻¹) := by
      rw [smul_mul', hgt, hcdef]
      field_simp
      try ring
    rw [e]
    obtain ⟨hm1, hr1⟩ := hv'
    have hm2 : (1 + t' * u' * u⁻¹ : F) ∈ w.toValuationSubring :=
      add_mem (one_mem _) (mul_mem (mul_mem ht'mem hu'_mem) huinv_mem)
    refine ⟨mul_mem hm1 hm2, ?_⟩
    have hmax : (⟨t' * u' * u⁻¹, mul_mem (mul_mem ht'mem hu'_mem) huinv_mem⟩ : w.toValuationSubring) ∈
        IsLocalRing.maximalIdeal w.toValuationSubring := by
      by_cases h0 : u' = 0
      · have : (⟨t' * u' * u⁻¹, mul_mem (mul_mem ht'mem hu'_mem) huinv_mem⟩ : w.toValuationSubring) = 0 :=
          Subtype.ext (by simp [h0])
        rw [this]; exact Ideal.zero_mem _
      · refine CartierLocalPen12.mem_maximalIdeal_of_ord_pos w ?_ _
        rw [w.ord_mul (mul_ne_zero ht'0 h0) (inv_ne_zero hu0), w.ord_mul ht'0 h0, ht', w.ord_inv, hu_ord]
        omega
    have hres2 : IsLocalRing.residue w.toValuationSubring ⟨1 + t' * u' * u⁻¹, hm2⟩ = 1 := by
      have : (⟨1 + t' * u' * u⁻¹, hm2⟩ : w.toValuationSubring) = 1 + ⟨t' * u' * u⁻¹, mul_mem (mul_mem ht'mem hu'_mem) huinv_mem⟩ :=
        Subtype.ext rfl
      rw [this, map_add, map_one, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, add_zero]
    have hmul : (⟨g • (t * f) * (1 + t' * u' * u⁻¹), mul_mem hm1 hm2⟩ : w.toValuationSubring) =
        ⟨g • (t * f), hm1⟩ * ⟨1 + t' * u' * u⁻¹, hm2⟩ := Subtype.ext rfl
    rw [hmul, map_mul, hr1, hres2, mul_one]

end S_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_smul_pullbackAlong_of_algEquiv
end P2MW
export P2MW.S_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_smul_pullbackAlong_of_algEquiv (solution)
