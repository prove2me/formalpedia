-- Prove2me | solution 1 for AlgebraicCurve.Place.ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3da02fa2-d19b-5a9a-8bd7-9df20b262ac7

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C.AlgebraicCurve Polynomial"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.deg_eq_one_of_isAlgClosed Place Place.ext HasPrincipalDivisors Place.smul_toValuationSubring Place.ord_smul Place.ramificationIndex Place.restrict_toValuationSubring Place.mem_fiber Place.sum_ramificationIndex_mul_inertiaDeg Place.deg_eq_one_iff_surjective_algebraMap_residueField"
namespace KummerRam
p2m_open "AlgebraicCurve"

section Ord

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] (w : Place K L)

theorem ord_nonneg_of_mem {f : L} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : w.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : w.toValuationSubring) : L) * ((π : L) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, w.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {f : L} (hf : f ≠ 0) (h : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

theorem ord_eq_zero_of_isUnit {f : L} (hf : f ∈ w.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : w.toValuationSubring)) : w.ord f = 0 :=
  w.ord_coe_unit hu.unit

theorem isUnit_of_ord_eq_zero {f : L} (hf0 : f ≠ 0) (hf : f ∈ w.toValuationSubring) (h : w.ord f = 0) :
    IsUnit (⟨f, hf⟩ : w.toValuationSubring) := by
  have hinv : f⁻¹ ∈ w.toValuationSubring :=
    mem_of_ord_nonneg w (inv_ne_zero hf0) (by rw [w.ord_inv]; omega)
  exact ⟨⟨⟨f, hf⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩

theorem ord_pos_of_mem_maximalIdeal {f : L} (hf0 : f ≠ 0) (hf : f ∈ w.toValuationSubring)
    (hm : (⟨f, hf⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring) : 0 < w.ord f := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  have h0 := ord_nonneg_of_mem w hf
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd (isUnit_of_ord_eq_zero w hf0 hf h.symm) hm

theorem min_ord_le_ord_add {f g : L} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (w.ord f) (w.ord g) ≤ w.ord (f + g) := by
  wlog hle : w.ord f ≤ w.ord g generalizing f g
  · rw [min_comm, add_comm]
    exact this hg hf (by rwa [add_comm]) (le_of_not_ge hle)
  rw [min_eq_left hle]
  have hq : g / f ∈ w.toValuationSubring :=
    mem_of_ord_nonneg w (div_ne_zero hg hf) (by rw [div_eq_mul_inv, w.ord_mul hg (inv_ne_zero hf), w.ord_inv]; omega)
  have h1 : (1 : L) + g / f ∈ w.toValuationSubring := add_mem (one_mem _) hq
  have hne : (1 : L) + g / f ≠ 0 := by
    intro h0
    apply hfg
    have : f * (1 + g / f) = f + g := by field_simp
    rw [← this, h0, mul_zero]
  have h2 := ord_nonneg_of_mem w h1
  have e : f + g = f * (1 + g / f) := by field_simp
  rw [e, w.ord_mul hf hne]
  omega

theorem ord_neg (f : L) : w.ord (-f) = w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have h1 : w.ord (-1 : L) = 0 := by
    have := w.ord_mul (neg_ne_zero.mpr (one_ne_zero' L)) (neg_ne_zero.mpr (one_ne_zero' L))
    rw [neg_one_mul, neg_neg, w.ord_one] at this
    omega
  rw [show -f = (-1) * f by ring, w.ord_mul (neg_ne_zero.mpr one_ne_zero) hf, h1, zero_add]

theorem ord_algebraMap_base (c : K) : w.ord (algebraMap K L c) = 0 := by
  have h1 := ord_nonneg_of_mem w (w.algebraMap_mem' c)
  have h2 := ord_nonneg_of_mem w (w.algebraMap_mem' c⁻¹)
  rw [map_inv₀, w.ord_inv] at h2
  omega

theorem exists_ord_eq_one : ∃ π : L, π ≠ 0 ∧ w.ord π = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  refine ⟨(π : L), ?_, w.ord_coe_irreducible hπ⟩
  simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero

end Ord

section Aut

variable {K : Type*} [Field K]
  {F : Type*} [Field F] [Algebra K F]
  {F' : Type*} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

abbrev toKAut (σ : F' ≃ₐ[F] F') : F' ≃ₐ[K] F' := σ.restrictScalars K

def resHom : (F' ≃ₐ[F] F') →* (F' ≃ₐ[K] F') where
  toFun := toKAut
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

scoped instance placeAction : MulAction (F' ≃ₐ[F] F') (Place K F') := MulAction.compHom _ (resHom (K := K))

private theorem _root_.AlgebraicCurve.KummerRam.smul_def (σ : F' ≃ₐ[F] F') (w : Place K F') : σ • w = (toKAut (K := K) σ) • w := rfl

p2m_export "AlgebraicCurve.KummerRam" "smul_def"
theorem ord_smul_eq_of_smul_eq {σ : F' ≃ₐ[F] F'} {w : Place K F'} (h : σ • w = w) (f : F') :
    w.ord (σ f) = w.ord f := by
  have h1 := Place.ord_smul (toKAut (K := K) σ) w f
  rw [← smul_def, h] at h1
  exact h1

variable [Algebra.IsIntegral F F']

theorem restrict_smul (σ : F' ≃ₐ[F] F') (w : Place K F') :
    (σ • w).restrict F = w.restrict F := by
  apply Place.ext
  ext f
  rw [Place.restrict_toValuationSubring, Place.restrict_toValuationSubring, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, smul_def, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have e : (toKAut (K := K) σ)⁻¹ (algebraMap F F' f) = algebraMap F F' f := σ.symm.commutes f
  rw [e]

omit [Algebra.IsIntegral F F'] in
theorem ramificationIndex_smul (σ : F' ≃ₐ[F] F') (w : Place K F') :
    (σ • w).ramificationIndex F = w.ramificationIndex F := by
  unfold Place.ramificationIndex
  congr 1
  ext m
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => exists_congr fun f => and_congr_right fun _ => ?_
  have h1 := Place.ord_smul (toKAut (K := K) σ) w (algebraMap F F' f)
  have e : (toKAut (K := K) σ) (algebraMap F F' f) = algebraMap F F' f := σ.commutes f
  rw [e, ← smul_def] at h1
  rw [h1]

omit [Algebra.IsIntegral F F'] in

theorem ord_sub_pos_of_smul_eq {σ : F' ≃ₐ[F] F'} {w : Place K F'} (h : σ • w = w)
    (hdeg : w.deg = 1) {z : F'} (hz0 : z ≠ 0) (hz : w.ord z = 0) (hne : z - σ z ≠ 0) :
    0 < w.ord (z - σ z) := by
  have hsurj := (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField w).mp hdeg
  have hzO : z ∈ w.toValuationSubring := mem_of_ord_nonneg w hz0 (by omega)
  obtain ⟨c, hc⟩ := hsurj (IsLocalRing.residue w.toValuationSubring ⟨z, hzO⟩)

  have hcO : algebraMap K F' c ∈ w.toValuationSubring := w.algebraMap_mem' c
  have htm : (⟨z, hzO⟩ - ⟨algebraMap K F' c, hcO⟩ : w.toValuationSubring) ∈
      IsLocalRing.maximalIdeal w.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc]
    rfl
  set t : F' := z - algebraMap K F' c with ht
  have htO : t ∈ w.toValuationSubring := sub_mem hzO hcO
  have hσc : σ (algebraMap K F' c) = algebraMap K F' c := by
    rw [IsScalarTower.algebraMap_apply K F F', σ.commutes]
  have hzt : z - σ z = t - σ t := by rw [ht, map_sub, hσc]; ring
  by_cases ht0 : t = 0
  · exfalso; apply hne; rw [hzt, ht0, map_zero, sub_zero]
  have htpos : 0 < w.ord t := by
    refine ord_pos_of_mem_maximalIdeal w ht0 htO ?_
    convert htm using 1
    rfl
  have hσt : 0 < w.ord (σ t) := by rw [ord_smul_eq_of_smul_eq h]; exact htpos
  have hσt0 : σ t ≠ 0 := by rw [map_ne_zero_iff _ σ.injective]; exact ht0
  rw [hzt]
  have hne' : t - σ t ≠ 0 := by rw [← hzt]; exact hne
  have := min_ord_le_ord_add w ht0 (neg_ne_zero.mpr hσt0) (by rw [← sub_eq_add_neg]; exact hne')
  rw [ord_neg, ← sub_eq_add_neg] at this
  exact lt_of_lt_of_le (lt_min htpos hσt) this

end Aut

section Kummer

variable {K : Type*} [Field K] [IsAlgClosed K]
  {F : Type*} [Field F] [Algebra K F]
  {F' : Type*} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

theorem exists_eq_algebraMap_of_pow_eq_one {x : F'} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) :
    ∃ ζ : K, algebraMap K F' ζ = x := by
  have hint : IsIntegral K x := by
    refine ⟨X ^ m - 1, monic_X_pow_sub_C 1 hm.ne', ?_⟩
    simp [hx]
  have hirr := minpoly.irreducible hint
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K hirr
  obtain ⟨ζ, hζ⟩ := minpoly.mem_range_of_degree_eq_one K x hdeg
  exact ⟨ζ, hζ⟩

variable (n : ℕ) (b : F) [FiniteDimensional F F'] [IsSplittingField F F' (X ^ n - C b)]

omit [FiniteDimensional F F'] in
include n b in
theorem exists_root (hn : 0 < n) : ∃ a : F', a ^ n = algebraMap F F' b := by
  have hsplit := IsSplittingField.splits F' (X ^ n - C b : F[X])
  have hdeg : (map (algebraMap F F') (X ^ n - C b : F[X])).degree ≠ 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, degree_X_pow_sub_C hn]; exact_mod_cast hn.ne'
  obtain ⟨a, ha⟩ := hsplit.exists_eval_eq_zero hdeg
  refine ⟨a, ?_⟩
  rw [eval_map, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at ha
  exact ha

omit [Algebra K F] [IsScalarTower K F F'] [FiniteDimensional F F'] [IsSplittingField F F' (X ^ n - C b)] in

theorem exists_apply_eq_mul (hn : 0 < n) (hb : b ≠ 0) {a : F'} (ha : a ^ n = algebraMap F F' b)
    (σ : F' ≃ₐ[F] F') : ∃ ζ : K, ζ ^ n = 1 ∧ σ a = algebraMap K F' ζ * a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero_iff _ (algebraMap F F').injective] at ha
    exact hb ha
  have hx : (σ a * a⁻¹) ^ n = 1 := by
    rw [mul_pow, ← map_pow, ha, σ.commutes, inv_pow, ha, mul_inv_cancel₀]
    rw [map_ne_zero_iff _ (algebraMap F F').injective]; exact hb
  obtain ⟨ζ, hζ⟩ := exists_eq_algebraMap_of_pow_eq_one (K := K) hn hx
  refine ⟨ζ, ?_, ?_⟩
  · apply (algebraMap K F').injective
    rw [map_pow, hζ, hx, map_one]
  · rw [hζ, inv_mul_cancel_right₀ ha0]

omit [FiniteDimensional F F'] in

theorem algEquiv_eq_of_apply_root_eq (K : Type*) [Field K] [IsAlgClosed K] [Algebra K F] [Algebra K F']
    [IsScalarTower K F F'] (hn : 0 < n) (hb : b ≠ 0) {a : F'} (ha : a ^ n = algebraMap F F' b)
    {σ τ : F' ≃ₐ[F] F'} (h : σ a = τ a) : σ = τ := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero_iff _ (algebraMap F F').injective] at ha
    exact hb ha
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ Algebra.adjoin F ((X ^ n - C b : F[X]).rootSet F') := by
    rw [IsSplittingField.adjoin_rootSet]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [mem_rootSet] at hy
    obtain ⟨-, hy⟩ := hy
    rw [map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hy

    have hq : (y * a⁻¹) ^ n = 1 := by
      rw [mul_pow, hy, inv_pow, ha, mul_inv_cancel₀]
      rw [map_ne_zero_iff _ (algebraMap F F').injective]; exact hb
    obtain ⟨ζ, hζ⟩ := exists_eq_algebraMap_of_pow_eq_one (K := K) hn hq
    have hy' : y = algebraMap F F' (algebraMap K F ζ) * a := by
      rw [← IsScalarTower.algebraMap_apply, hζ, inv_mul_cancel_right₀ ha0]
    rw [hy', map_mul, map_mul, σ.commutes, τ.commutes, h]
  | algebraMap r => rw [σ.commutes, τ.commutes]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

end Kummer

section Main

variable {K : Type*} [Field K] [IsAlgClosed K]
  {F : Type*} [Field F] [Algebra K F]
  {F' : Type*} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [IsCurveOver K F']
  (n : ℕ) (b : F) [FiniteDimensional F F'] [IsSplittingField F F' (X ^ n - C b)]

include n b in
theorem main (hn : (n : K) ≠ 0) (hb : b ≠ 0) (hdeg : Module.finrank F F' = n) (w : Place K F') :
    w.ramificationIndex F = n / Nat.gcd n ((w.restrict F).ord b).natAbs := by
  classical
  haveI : HasPrincipalDivisors K F' := IsCurveOver.hasPrincipalDivisors
  have hn0 : 0 < n := by rw [← hdeg]; exact Module.finrank_pos
  have hnF : (n : F) ≠ 0 := by
    intro h; apply hn
    apply (algebraMap K F).injective
    rw [map_natCast, h, map_zero]
  obtain ⟨a, ha⟩ := exists_root (F' := F') n b hn0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0.ne', eq_comm, map_eq_zero_iff _ (algebraMap F F').injective] at ha
    exact hb ha

  set v := w.restrict F with hv
  set d : ℤ := v.ord b with hd
  set e : ℕ := w.ramificationIndex F with he
  set g : ℕ := Nat.gcd n d.natAbs with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hn0
  have hgn : g ∣ n := Nat.gcd_dvd_left _ _
  have hgd : g ∣ d.natAbs := Nat.gcd_dvd_right _ _
  set n' : ℕ := n / g with hn'
  set d₁ : ℕ := d.natAbs / g with hd₁
  have hnn' : n = g * n' := (Nat.mul_div_cancel' hgn).symm
  have hdd₁ : d.natAbs = g * d₁ := (Nat.mul_div_cancel' hgd).symm
  have hcop : Nat.Coprime n' d₁ := by
    rw [hn', hd₁, hg]; exact Nat.coprime_div_gcd_div_gcd hg0
  have hepos : 0 < e := w.ramificationIndex_pos (F := F)

  have hord : (n : ℤ) * w.ord a = e * d := by
    have h1 : w.ord (a ^ n) = (n : ℤ) * w.ord a := by rw [← zpow_natCast, w.ord_zpow]
    rw [← h1, ha, w.ord_restrict (F := F) b]
  have hdvd : n' ∣ e := by
    have h1 : (n : ℤ) ∣ (e : ℤ) * d := ⟨w.ord a, hord.symm⟩
    have h2 : n ∣ e * d.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h1
      rwa [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at this
    rw [hnn', hdd₁, mul_left_comm] at h2
    exact hcop.dvd_of_dvd_mul_right (Nat.dvd_of_mul_dvd_mul_left hg0 h2)

  haveI : IsGalois F F' := IsGalois.of_separable_splitting_field (p := X ^ n - C b)
    (separable_X_pow_sub_C b hnF hb)
  have hcardG : Nat.card (F' ≃ₐ[F] F') = n := by
    rw [IsGalois.card_aut_eq_finrank, hdeg]

  have hf1 : ∀ w' : Place K F', w'.inertiaDeg F = 1 := by
    intro w'
    have h1 := w'.deg_restrict_mul_inertiaDeg (F := F)
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed w'] at h1
    exact Nat.eq_one_of_mul_eq_one_left h1

  set G := F' ≃ₐ[F] F'
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcardG]; exact hn0.ne')
  haveI : Finite (MulAction.orbit G w) := Finite.Set.finite_range (fun m : G => m • w)
  have hos : Nat.card (MulAction.orbit G w) * Nat.card (MulAction.stabilizer G w) = n := by
    rw [← hcardG, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G w),
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

  have horb_sub : ∀ w' ∈ MulAction.orbit G w, w' ∈ v.fiber F' := by
    rintro w' ⟨σ, rfl⟩
    rw [Place.mem_fiber, hv]
    exact restrict_smul (K := K) σ w
  haveI : Fintype (MulAction.orbit G w) := Fintype.ofFinite _
  have hsum := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg (K := K) (F := F) (F' := F') v
  rw [hdeg] at hsum
  have hle1 : (Nat.card (MulAction.orbit G w) : ℤ) * e ≤ n := by
    rw [← hsum]
    have hsub : (MulAction.orbit G w).toFinset ⊆ v.fiber F' := by
      intro w' hw'; exact horb_sub w' (Set.mem_toFinset.mp hw')
    have hterm : ∀ w' ∈ (MulAction.orbit G w).toFinset,
        ((w'.ramificationIndex F : ℤ) * (w'.inertiaDeg F : ℤ)) = (e : ℤ) := by
      intro w' hw'
      obtain ⟨σ, rfl⟩ := Set.mem_toFinset.mp hw'
      show (((σ • w).ramificationIndex F : ℕ) : ℤ) * (((σ • w).inertiaDeg F : ℕ) : ℤ) = e
      rw [hf1, ramificationIndex_smul (K := K) σ w, Nat.cast_one, mul_one]
    calc (Nat.card (MulAction.orbit G w) : ℤ) * e
        = ∑ w' ∈ (MulAction.orbit G w).toFinset, (e : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_toFinset]
      _ = ∑ w' ∈ (MulAction.orbit G w).toFinset, ((w'.ramificationIndex F : ℤ) * (w'.inertiaDeg F : ℤ)) :=
          (Finset.sum_congr rfl hterm).symm
      _ ≤ ∑ w' ∈ v.fiber F', ((w'.ramificationIndex F : ℤ) * (w'.inertiaDeg F : ℤ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro w' _ _; positivity
  have hle2 : e ≤ Nat.card (MulAction.stabilizer G w) := by
    haveI : Nonempty (MulAction.orbit G w) := ⟨⟨w, MulAction.mem_orbit_self w⟩⟩
    have hpos : 0 < Nat.card (MulAction.orbit G w) := Nat.card_pos
    have : (Nat.card (MulAction.orbit G w)) * e ≤ Nat.card (MulAction.orbit G w) * Nat.card (MulAction.stabilizer G w) := by
      rw [hos]; exact_mod_cast hle1
    exact Nat.le_of_mul_le_mul_left this hpos

  have hn'0 : 0 < n' := Nat.div_pos (Nat.le_of_dvd hn0 hgn) hg0
  obtain ⟨π, hπ0, hπ1⟩ := exists_ord_eq_one v
  obtain ⟨d', hd'⟩ : (g : ℤ) ∣ d := Int.natCast_dvd.mpr hgd
  have horda : (n' : ℤ) * w.ord a = e * d' := by
    have h1 := hord
    rw [hnn', hd', Nat.cast_mul] at h1
    have hg0' : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
    apply mul_left_cancel₀ hg0'
    linarith [h1]
  have hπ' : algebraMap F F' π ≠ 0 := by rw [map_ne_zero_iff _ (algebraMap F F').injective]; exact hπ0
  have hordπ : w.ord (algebraMap F F' π) = e := by
    rw [w.ord_restrict (F := F), ← hv, hπ1, mul_one]
  set y : F' := a ^ n' * (algebraMap F F' π) ^ (-d') with hy
  have hy0 : y ≠ 0 := mul_ne_zero (pow_ne_zero _ ha0) (zpow_ne_zero _ hπ')
  have hordy : w.ord y = 0 := by
    rw [hy, w.ord_mul (pow_ne_zero _ ha0) (zpow_ne_zero _ hπ'), ← zpow_natCast, w.ord_zpow, w.ord_zpow, hordπ]
    linarith [horda]
  have hchar : ∀ σ : G, σ ∈ MulAction.stabilizer G w → ∀ ζ : K, σ a = algebraMap K F' ζ * a → ζ ^ n' = 1 := by
    intro σ hσ ζ hζ
    have hσy : σ y = algebraMap K F' (ζ ^ n') * y := by
      rw [hy, map_mul, map_pow, hζ, map_zpow₀, σ.commutes, mul_pow, ← map_pow]
      ring
    by_contra hne1
    have hc : (1 : K) - ζ ^ n' ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
    have hdiff : y - σ y = algebraMap K F' (1 - ζ ^ n') * y := by rw [hσy, map_sub, map_one]; ring
    have hc' : algebraMap K F' (1 - ζ ^ n') ≠ 0 := by rw [map_ne_zero_iff _ (algebraMap K F').injective]; exact hc
    have hne : y - σ y ≠ 0 := by rw [hdiff]; exact mul_ne_zero hc' hy0
    have hpos := ord_sub_pos_of_smul_eq (K := K) (MulAction.mem_stabilizer_iff.mp hσ)
      (IsCurveOver.deg_eq_one_of_isAlgClosed w) hy0 hordy hne
    rw [hdiff, w.ord_mul hc' hy0, ord_algebraMap_base, hordy] at hpos
    exact lt_irrefl _ hpos
  choose χ hχ using fun σ : G => exists_apply_eq_mul (K := K) n b hn0 hb ha σ
  have hinj : Function.Injective χ := fun σ τ h =>
    algEquiv_eq_of_apply_root_eq n b K hn0 hb ha (by rw [(hχ σ).2, (hχ τ).2, h])
  set S := (Polynomial.nthRoots n' (1 : K)).toFinset with hS
  have hmemS : ∀ σ : MulAction.stabilizer G w, χ σ ∈ S := fun σ => by
    rw [hS, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn'0]
    exact hchar σ σ.2 _ (hχ σ).2
  let ι : MulAction.stabilizer G w → S := fun σ => ⟨χ σ, hmemS σ⟩
  have hι : Function.Injective ι := fun σ τ h =>
    Subtype.ext (hinj (congrArg Subtype.val h :))
  have hle3 : Nat.card (MulAction.stabilizer G w) ≤ n' :=
    calc Nat.card (MulAction.stabilizer G w) ≤ Nat.card S := Nat.card_le_card_of_injective ι hι
      _ = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ Multiset.card (Polynomial.nthRoots n' (1 : K)) := Multiset.toFinset_card_le _
      _ ≤ n' := Polynomial.card_nthRoots n' 1

  have hle : e ≤ n' := hle2.trans hle3
  have hge : n' ≤ e := Nat.le_of_dvd hepos hdvd
  show e = n / g
  rw [← hn']
  omega

end Main

end AlgebraicCurve.KummerRam
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C.AlgebraicCurve P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C.AlgebraicCurve.KummerRam"
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C.AlgebraicCurve"

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K]
    {F : Type*} [Field F] [Algebra K F]
    {F' : Type*} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [IsCurveOver K F']
    (n : ℕ) (hn : (n : K) ≠ 0) (b : F) (hb : b ≠ 0)
    [FiniteDimensional F F'] [IsSplittingField F F' (X ^ n - C b)]
    (hdeg : Module.finrank F F' = n)
    (w : Place K F') :
    w.ramificationIndex F = n / Nat.gcd n ((w.restrict F).ord b).natAbs :=
  AlgebraicCurve.KummerRam.main n b hn hb hdeg w

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C.AlgebraicCurve P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C.AlgebraicCurve.KummerRam"

end S_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C
end P2MW
export P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C (solution)
