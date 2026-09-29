-- Prove2me | solution 1 for AlgebraicCurve.exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/477cf5e9-7a3c-59c6-9c49-c5884279fee1

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_sub_eq_ord_eval
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardNormFormula_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Theorems.Thm_AlgebraicCurve_Place_exists_isIntegral_adjoin_eq_top_ord_sub_algebraMap_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval.AlgebraicCurve IsLocalRing KaehlerDifferential Polynomial"
open scoped IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.diffCoeff IsCurveOver IsCurveOver.finrank_kaehler IsCurveOver.finiteResidue Place.mem_restrict_iff Divisor.pushforward_apply Place.min_ord_le_ord_add Place.diffCoeff_smul_D_of_ord_eq_one Place.diffCoeff_smul_D_eq_of_ord_eq_one Place.ord_diffCoeff_D_nonneg_of_perfectField Place.ord_norm_sub_eq_ord_eval Divisor.pushforwardNormFormula_of_isSeparable Place.inertiaDeg_eq_one_of_isRational Place.exists_isIntegral_adjoin_eq_top_ord_sub_algebraMap_eq_one"
namespace DedekindDifferentProof
p2m_open "AlgebraicCurve"

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg Subtype.val hu
    rw [zpow_natCast]; push_cast at h; exact h
  rw [this, v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem ord_eq_zero_of_mem_of_inv_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (hfi : f⁻¹ ∈ v.toValuationSubring) : v.ord f = 0 := by
  have h1 := ord_nonneg_of_mem v hf
  have h2 := ord_nonneg_of_mem v hfi
  rw [v.ord_inv] at h2
  omega

theorem inv_mem_of_ord_eq_zero (v : Place K F) {f : F} (hf : v.ord f = 0) :
    f⁻¹ ∈ v.toValuationSubring :=
  mem_of_ord_nonneg v (by rw [v.ord_inv, hf]; norm_num)

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  by_cases hc : c = 0
  · simp [hc]
  exact ord_eq_zero_of_mem_of_inv_mem v (v.algebraMap_mem' c)
    (by rw [← map_inv₀]; exact v.algebraMap_mem' c⁻¹)

theorem ord_neg (v : Place K F) (a : F) : v.ord (-a) = v.ord a := by
  by_cases ha : a = 0
  · rw [ha, neg_zero]
  rw [neg_eq_neg_one_mul, v.ord_mul (by norm_num) ha,
    show (-1 : F) = algebraMap K F (-1) by simp, ord_algebraMap, zero_add]

theorem ord_pow (v : Place K F) (a : F) (n : ℕ) : v.ord (a ^ n) = n * v.ord a := by
  rw [← zpow_natCast, v.ord_zpow]

theorem ord_add_eq_of_lt (v : Place K F) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : v.ord a < v.ord b) : a + b ≠ 0 ∧ v.ord (a + b) = v.ord a := by
  have hab : a + b ≠ 0 := by
    intro h0
    have : a = -b := eq_neg_of_add_eq_zero_left h0
    rw [this, ord_neg] at h
    exact lt_irrefl _ h
  refine ⟨hab, le_antisymm ?_ ?_⟩
  · by_contra hlt
    push Not at hlt
    have h2 := Place.min_ord_le_ord_add v hab (neg_ne_zero.mpr hb) (by rwa [add_neg_cancel_right])
    rw [add_neg_cancel_right, ord_neg] at h2
    have : min (v.ord (a + b)) (v.ord b) > v.ord a := lt_min hlt h
    omega
  · have h1 := Place.min_ord_le_ord_add v ha hb hab
    rwa [min_eq_left h.le] at h1

theorem ord_add_eq_of_lt' (v : Place K F) {a b : F} (ha : a ≠ 0)
    (h : b = 0 ∨ v.ord a < v.ord b) : a + b ≠ 0 ∧ v.ord (a + b) = v.ord a := by
  rcases h with rfl | h
  · rw [add_zero]; exact ⟨ha, rfl⟩
  by_cases hb : b = 0
  · rw [hb, add_zero]; exact ⟨ha, rfl⟩
  exact ord_add_eq_of_lt v ha hb h

def valSubalgebra (v : Place K F) : Subalgebra K F where
  carrier := v.toValuationSubring
  mul_mem' ha hb := mul_mem ha hb
  add_mem' ha hb := add_mem ha hb
  algebraMap_mem' := v.algebraMap_mem'

theorem mem_valSubalgebra (v : Place K F) {f : F} : f ∈ valSubalgebra v ↔ f ∈ v.toValuationSubring :=
  Iff.rfl

theorem aeval_mem (v : Place K F) {t : F} (ht : t ∈ v.toValuationSubring) (p : K[X]) :
    aeval t p ∈ v.toValuationSubring := by
  rw [← mem_valSubalgebra]
  refine (Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((mem_valSubalgebra v).mpr ht)))
    (Polynomial.aeval_mem_adjoin_singleton K t)

theorem mem_of_isIntegral {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F] (w : Place K F) {b : F}
    (hb : IsIntegral (w.restrict E).toValuationSubring b) : b ∈ w.toValuationSubring := by
  obtain ⟨Q, hQmonic, hQeval⟩ := hb
  refine w.mem_of_eval_monic_eq_zero
    (P := Q.map (algebraMap (w.restrict E).toValuationSubring F))
    (hQmonic.map _) (fun i => ?_) (by rw [Polynomial.eval_map]; exact hQeval)
  rw [Polynomial.coeff_map]
  exact (Q.coeff i).2

end PlaceFacts

section RationalBase

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (t : F)

theorem ord_aeval_eq_zero (w : Place K F) {c₀ : K} (h1 : 1 ≤ w.ord (t - algebraMap K F c₀))
    {p : K[X]} (hp : p.eval c₀ ≠ 0) : aeval t p ≠ 0 ∧ w.ord (aeval t p) = 0 := by
  obtain ⟨q, hq⟩ := (X_sub_C_dvd_sub_C_eval : X - C c₀ ∣ p - C (p.eval c₀))
  have hp' : p = C (p.eval c₀) + (X - C c₀) * q := by rw [← hq]; ring
  have ht0 : t - algebraMap K F c₀ ≠ 0 := by rintro h; simp [h] at h1
  have htmem : t ∈ w.toValuationSubring := by
    have : t = (t - algebraMap K F c₀) + algebraMap K F c₀ := by ring
    rw [this]
    exact add_mem (mem_of_ord_nonneg w (by omega)) (w.algebraMap_mem' c₀)
  have heval : aeval t p = algebraMap K F (p.eval c₀) + (t - algebraMap K F c₀) * aeval t q := by
    conv_lhs => rw [hp']
    simp [map_add, map_mul, map_sub, aeval_X, aeval_C]
  have hc : algebraMap K F (p.eval c₀) ≠ 0 := by
    rwa [map_ne_zero_iff _ (algebraMap K F).injective]
  have h2 : (t - algebraMap K F c₀) * aeval t q = 0 ∨
      w.ord (algebraMap K F (p.eval c₀)) < w.ord ((t - algebraMap K F c₀) * aeval t q) := by
    by_cases hq0 : aeval t q = 0
    · left; rw [hq0, mul_zero]
    right
    rw [ord_algebraMap, w.ord_mul ht0 hq0]
    have := ord_nonneg_of_mem w (aeval_mem w htmem q)
    omega
  have := ord_add_eq_of_lt' w hc h2
  rw [← heval, ord_algebraMap] at this
  exact this

variable (ht : Transcendental K t)
include ht

theorem sub_algebraMap_ne_zero (c : K) : t - algebraMap K F c ≠ 0 := by
  intro h
  apply ht
  rw [sub_eq_zero] at h
  rw [h]; exact isAlgebraic_algebraMap c

theorem aeval_ne_zero {p : K[X]} (hp : p ≠ 0) : aeval t p ≠ 0 := by
  intro h
  exact hp (transcendental_iff_injective.mp ht (by rw [h, map_zero]))

omit [Field F] [Algebra K F] ht in

theorem exists_eq_pow_mul (c₀ : K) {r : K[X]} (hr : r ≠ 0) :
    ∃ (i : ℕ) (r₁ : K[X]), r₁.eval c₀ ≠ 0 ∧ r = (X - C c₀) ^ i * r₁ := by
  obtain ⟨r₁, hr₁, hndvd⟩ := r.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hr c₀
  refine ⟨r.rootMultiplicity c₀, r₁, ?_, hr₁⟩
  rwa [dvd_iff_isRoot, IsRoot.def] at hndvd

theorem exists_repr (c₀ : K) {a : F} (ha : a ∈ IntermediateField.adjoin K ({t} : Set F))
    (ha0 : a ≠ 0) :
    ∃ (n : ℤ) (r₁ s₁ : K[X]), r₁.eval c₀ ≠ 0 ∧ s₁.eval c₀ ≠ 0 ∧
      a * aeval t s₁ = (t - algebraMap K F c₀) ^ n * aeval t r₁ := by
  rw [IntermediateField.mem_adjoin_simple_iff] at ha
  obtain ⟨r, s, hrs⟩ := ha
  have hr0 : r ≠ 0 := by rintro rfl; simp [hrs] at ha0
  have hs0 : aeval t s ≠ 0 := by intro h; rw [h, div_zero] at hrs; exact ha0 hrs
  have hs0' : s ≠ 0 := by rintro rfl; simp at hs0
  obtain ⟨i, r₁, hr₁, hr⟩ := exists_eq_pow_mul c₀ hr0
  obtain ⟨j, s₁, hs₁, hs⟩ := exists_eq_pow_mul c₀ hs0'
  have hst := sub_algebraMap_ne_zero t ht c₀
  refine ⟨(i : ℤ) - j, r₁, s₁, hr₁, hs₁, ?_⟩
  have h1 : a * aeval t s = aeval t r := by
    rw [hrs, div_mul_cancel₀ _ hs0]
  rw [hr, hs] at h1
  simp only [map_mul, map_pow, map_sub, aeval_X, aeval_C] at h1
  rw [zpow_sub₀ hst, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  have hj : (t - algebraMap K F c₀) ^ j ≠ 0 := pow_ne_zero _ hst
  calc a * aeval t s₁ = a * ((t - algebraMap K F c₀) ^ j * aeval t s₁) *
        ((t - algebraMap K F c₀) ^ j)⁻¹ := by field_simp
    _ = (t - algebraMap K F c₀) ^ i * aeval t r₁ * ((t - algebraMap K F c₀) ^ j)⁻¹ := by rw [h1]
    _ = _ := by ring

theorem ord_eq_mul_of_repr (w : Place K F) {c₀ : K} (h1 : 1 ≤ w.ord (t - algebraMap K F c₀))
    {a : F} (ha0 : a ≠ 0) {n : ℤ} {r₁ s₁ : K[X]} (hr₁ : r₁.eval c₀ ≠ 0) (hs₁ : s₁.eval c₀ ≠ 0)
    (h : a * aeval t s₁ = (t - algebraMap K F c₀) ^ n * aeval t r₁) :
    w.ord a = n * w.ord (t - algebraMap K F c₀) := by
  have hs := ord_aeval_eq_zero t w h1 hs₁
  have hr := ord_aeval_eq_zero t w h1 hr₁
  have hst := sub_algebraMap_ne_zero t ht c₀
  have := congrArg w.ord h
  rwa [w.ord_mul ha0 hs.1, hs.2, add_zero, w.ord_mul (zpow_ne_zero _ hst) hr.1, hr.2, add_zero,
    w.ord_zpow] at this

theorem exists_mul_aeval_eq (w : Place K F) {c₀ : K} (h1 : 1 ≤ w.ord (t - algebraMap K F c₀))
    {a : F} (ha : a ∈ IntermediateField.adjoin K ({t} : Set F)) (haw : a ∈ w.toValuationSubring) :
    ∃ p q : K[X], q.eval c₀ ≠ 0 ∧ a * aeval t q = aeval t p := by
  by_cases ha0 : a = 0
  · exact ⟨0, 1, by simp, by simp [ha0]⟩
  obtain ⟨n, r₁, s₁, hr₁, hs₁, h⟩ := exists_repr t ht c₀ ha ha0
  have hord := ord_eq_mul_of_repr t ht w h1 ha0 hr₁ hs₁ h
  have hn : 0 ≤ n := by
    have h0 := ord_nonneg_of_mem w haw
    rw [hord] at h0
    by_contra hn
    push Not at hn
    have : n * w.ord (t - algebraMap K F c₀) < 0 := Int.mul_neg_of_neg_of_pos hn (by omega)
    omega
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  refine ⟨(X - C c₀) ^ k * r₁, s₁, hs₁, ?_⟩
  rw [h, zpow_natCast]
  simp [map_mul, map_pow, map_sub, aeval_X, aeval_C]

end RationalBase

section Derivation

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (t : F) (ht : Transcendental K t)
  [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F]

def tD (y : F) : F :=
  (KaehlerDifferential.exists_unique_smul_D_of_transcendental K t ht (D K F y)).exists.choose

theorem D_eq_tD_smul (y : F) : D K F y = tD t ht y • D K F t :=
  (KaehlerDifferential.exists_unique_smul_D_of_transcendental K t ht (D K F y)).exists.choose_spec

include ht in
theorem D_t_ne_zero : D K F t ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K t ht

theorem tD_eq_of_eq {y c : F} (h : D K F y = c • D K F t) : tD t ht y = c :=
  smul_left_injective F (D_t_ne_zero t ht) ((D_eq_tD_smul t ht y).symm.trans h)

theorem tD_add (y z : F) : tD t ht (y + z) = tD t ht y + tD t ht z :=
  tD_eq_of_eq t ht (by rw [map_add, D_eq_tD_smul t ht y, D_eq_tD_smul t ht z, add_smul])

theorem tD_mul (y z : F) : tD t ht (y * z) = y * tD t ht z + z * tD t ht y :=
  tD_eq_of_eq t ht (by
    rw [Derivation.leibniz]
    conv_lhs => rw [D_eq_tD_smul t ht y, D_eq_tD_smul t ht z, smul_smul, smul_smul]
    rw [add_smul])

theorem tD_algebraMap (c : K) : tD t ht (algebraMap K F c) = 0 :=
  tD_eq_of_eq t ht (by rw [Derivation.map_algebraMap, zero_smul])

theorem tD_self : tD t ht t = 1 := tD_eq_of_eq t ht (one_smul F _).symm

theorem tD_aeval (p : K[X]) : tD t ht (aeval t p) = aeval t (derivative p) :=
  tD_eq_of_eq t ht (Derivation.map_aeval _ p t)

theorem tD_sub_algebraMap (y : F) (c : K) : tD t ht (y - algebraMap K F c) = tD t ht y :=
  tD_eq_of_eq t ht (by rw [map_sub, Derivation.map_algebraMap, sub_zero, ← D_eq_tD_smul t ht y])

theorem tD_pow (y : F) (n : ℕ) : tD t ht (y ^ n) = n * y ^ (n - 1) * tD t ht y :=
  tD_eq_of_eq t ht (by
    rw [Derivation.leibniz_pow]
    conv_lhs => rw [D_eq_tD_smul t ht y, smul_smul, ← Nat.cast_smul_eq_nsmul F, smul_smul,
      ← mul_assoc])

theorem tD_sum {ι : Type*} (s : Finset ι) (f : ι → F) :
    tD t ht (∑ i ∈ s, f i) = ∑ i ∈ s, tD t ht (f i) :=
  tD_eq_of_eq t ht (by
    rw [map_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => D_eq_tD_smul t ht (f i))

theorem tD_algebraMap_mul (c : K) (y : F) : tD t ht (algebraMap K F c * y) = algebraMap K F c * tD t ht y := by
  rw [tD_mul, tD_algebraMap, mul_zero, add_zero]

theorem tD_mem (w : Place K F) {c₀ : K} (h1 : 1 ≤ w.ord (t - algebraMap K F c₀))
    {a : F} (ha : a ∈ IntermediateField.adjoin K ({t} : Set F)) (haw : a ∈ w.toValuationSubring) :
    tD t ht a ∈ w.toValuationSubring := by
  obtain ⟨p, q, hq, h⟩ := exists_mul_aeval_eq t ht w h1 ha haw
  have hq' := ord_aeval_eq_zero t w h1 hq
  have htmem : t ∈ w.toValuationSubring := by
    have : t = (t - algebraMap K F c₀) + algebraMap K F c₀ := by ring
    rw [this]
    exact add_mem (mem_of_ord_nonneg w (by omega)) (w.algebraMap_mem' c₀)
  have hD := congrArg (tD t ht) h
  rw [tD_mul, tD_aeval, tD_aeval] at hD

  have : tD t ht a = (aeval t (derivative p) - a * aeval t (derivative q)) * (aeval t q)⁻¹ := by
    rw [← hD]; field_simp [hq'.1]; ring
  rw [this]
  exact mul_mem (sub_mem (aeval_mem w htmem _) (mul_mem haw (aeval_mem w htmem _)))
    (inv_mem_of_ord_eq_zero w hq'.2)

end Derivation

section LocalDual

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (t : F) (ht : Transcendental K t)
  [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]

include ht in

theorem trace_mul_mem (x : F)
    (hx : ∀ b : F, IsIntegral (Algebra.adjoin K ({t} : Set F)) b →
      ∃ P : Polynomial K, ((Algebra.trace (K⟮t⟯) F (x * b) : (K⟮t⟯)) : F) = Polynomial.aeval t P)
    (w : Place K F) {c₀ : K} (h1 : 1 ≤ w.ord (t - algebraMap K F c₀))
    {y : F} (hy : IsIntegral (w.restrict (K⟮t⟯)).toValuationSubring y) :
    ((Algebra.trace (K⟮t⟯) F (x * y) : (K⟮t⟯)) : F) ∈ w.toValuationSubring := by
  classical
  have htmem : t ∈ w.toValuationSubring := by
    have : t = (t - algebraMap K F c₀) + algebraMap K F c₀ := by ring
    rw [this]
    exact add_mem (mem_of_ord_nonneg w (by omega)) (w.algebraMap_mem' c₀)
  obtain ⟨pm, hmonic, heval⟩ := hy

  have hcoef : ∀ i, ∃ pq : K[X] × K[X], pq.2.eval c₀ ≠ 0 ∧
      ((pm.coeff i : (K⟮t⟯)) : F) * aeval t pq.2 = aeval t pq.1 := by
    intro i
    obtain ⟨p, q, hq, h⟩ := exists_mul_aeval_eq t ht w h1 (a := ((pm.coeff i : (K⟮t⟯)) : F))
      (pm.coeff i : (K⟮t⟯)).2 (pm.coeff i).2
    exact ⟨(p, q), hq, h⟩
  choose pq hpq using hcoef
  set d := pm.natDegree
  set q : K[X] := ∏ i ∈ Finset.range d, (pq i).2 with hqdef
  have hq : q.eval c₀ ≠ 0 := by
    rw [hqdef, eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hpq i).1
  obtain ⟨hQ0, hQord⟩ := ord_aeval_eq_zero t w h1 hq
  set Q : F := aeval t q with hQdef

  set P₀ : F[X] := pm.map (algebraMap (w.restrict (K⟮t⟯)).toValuationSubring F) with hP₀
  have hP₀monic : P₀.Monic := by rw [hP₀]; exact hmonic.map _
  have hP₀eval : aeval y P₀ = 0 := by
    rw [coe_aeval_eq_eval, hP₀, eval_map]; exact heval
  set P₁ : F[X] := P₀.scaleRoots Q with hP₁
  have hP₁monic : P₁.Monic := (monic_scaleRoots_iff Q).mpr hP₀monic
  have hP₁eval : aeval (Q * y) P₁ = 0 := by
    have := scaleRoots_aeval_eq_zero (r := Q) hP₀eval
    simpa using this
  have hdeg : P₀.natDegree = d := hmonic.natDegree_map _

  have hcoeffmem : ∀ n, P₁.coeff n ∈ Algebra.adjoin K ({t} : Set F) := by
    intro n
    rw [hP₁, coeff_scaleRoots, hdeg]
    rcases lt_trichotomy n d with hn | rfl | hn
    · have hcoeff : P₀.coeff n = ((pm.coeff n : (K⟮t⟯)) : F) := by rw [hP₀, coeff_map]; rfl
      rw [hcoeff]
      have hsplit : Q = aeval t (pq n).2 * aeval t (∏ i ∈ (Finset.range d).erase n, (pq i).2) := by
        rw [hQdef, hqdef, ← map_mul, Finset.mul_prod_erase _ (fun i => (pq i).2)
          (Finset.mem_range.mpr hn)]
      obtain ⟨k, hk⟩ : ∃ k, d - n = k + 1 := ⟨d - n - 1, by omega⟩
      have : ((pm.coeff n : (K⟮t⟯)) : F) * Q ^ (d - n) =
          aeval t (pq n).1 * aeval t (∏ i ∈ (Finset.range d).erase n, (pq i).2) * Q ^ k := by
        rw [hk, pow_succ, ← (hpq n).2]
        conv_lhs => rw [show Q ^ k * Q = (aeval t (pq n).2 *
          aeval t (∏ i ∈ (Finset.range d).erase n, (pq i).2)) * Q ^ k by rw [← hsplit]; ring]
        ring
      rw [this]
      refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (aeval_mem_adjoin_singleton K t)
        (aeval_mem_adjoin_singleton K t)) (Subalgebra.pow_mem _ ?_ _)
      rw [hQdef]; exact aeval_mem_adjoin_singleton K t
    · have h1' : P₀.coeff d = 1 := by rw [← hdeg]; exact hP₀monic
      rw [h1', Nat.sub_self, pow_zero, mul_one]
      exact Subalgebra.one_mem _
    · rw [coeff_eq_zero_of_natDegree_lt (hdeg ▸ hn), zero_mul]
      exact Subalgebra.zero_mem _
  have hlifts : P₁ ∈ Polynomial.lifts (algebraMap (Algebra.adjoin K ({t} : Set F)) F) :=
    (lifts_iff_coeff_lifts P₁).mpr fun n => ⟨⟨P₁.coeff n, hcoeffmem n⟩, rfl⟩
  obtain ⟨P₂, hP₂map, -, hP₂monic⟩ := lifts_and_degree_eq_and_monic hlifts hP₁monic
  have hint : IsIntegral (Algebra.adjoin K ({t} : Set F)) (Q * y) := by
    refine ⟨P₂, hP₂monic, ?_⟩
    rw [eval₂_eq_eval_map, hP₂map]
    rw [coe_aeval_eq_eval] at hP₁eval
    exact hP₁eval

  obtain ⟨Pt, hPt⟩ := hx (Q * y) hint
  have hQmem : Q ∈ (K⟮t⟯) := by
    rw [hQdef]
    exact (IntermediateField.algebra_adjoin_le_adjoin K _) (aeval_mem_adjoin_singleton K t)
  have htr : ((Algebra.trace (K⟮t⟯) F (x * y) : (K⟮t⟯)) : F) = aeval t Pt * Q⁻¹ := by
    have h2 : x * (Q * y) = (⟨Q, hQmem⟩ : (K⟮t⟯)) • (x * y) := by
      rw [IntermediateField.smul_def]; change x * (Q * y) = Q * (x * y); ring
    rw [h2, map_smul, smul_eq_mul] at hPt
    push_cast at hPt
    change Q * ((Algebra.trace (K⟮t⟯) F (x * y) : (K⟮t⟯)) : F) = aeval t Pt at hPt
    rw [← hPt]; field_simp
  rw [htr]
  exact mul_mem (aeval_mem w htmem Pt) (inv_mem_of_ord_eq_zero w hQord)

end LocalDual

section Euler

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (t : F)
  [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
  [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F]

theorem mul_aeval_derivative_mem (w : Place K F) {θ : F}
    (hθi : IsIntegral (w.restrict (K⟮t⟯)).toValuationSubring θ)
    (hθtop : IntermediateField.adjoin (K⟮t⟯) ({θ} : Set F) = ⊤) {x : F}
    (hxdual : ∀ y : F, IsIntegral (w.restrict (K⟮t⟯)).toValuationSubring y →
      ((Algebra.trace (K⟮t⟯) F (x * y) : (K⟮t⟯)) : F) ∈ w.toValuationSubring) :
    x * aeval θ (derivative (minpoly (K⟮t⟯) θ)) ∈ w.toValuationSubring := by
  set A := (w.restrict (K⟮t⟯)).toValuationSubring with hA
  have hx' : Algebra.adjoin (K⟮t⟯) ({θ} : Set F) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic θ), hθtop, IntermediateField.top_toSubalgebra]
  have hmem : x ∈ (Algebra.traceForm (K⟮t⟯) F).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin A ({θ} : Set F))) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    have hyint : IsIntegral A y := adjoin_le_integralClosure hθi hy
    have h := hxdual y hyint
    rw [Algebra.traceForm_apply, Submodule.mem_one]
    exact ⟨⟨Algebra.trace (K⟮t⟯) F (x * y), (Place.mem_restrict_iff w).mpr h⟩, rfl⟩
  rw [traceForm_dualSubmodule_adjoin A (K⟮t⟯) hx' hθi, Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨b, hb, hbx⟩ := hmem
  have hne : aeval θ (derivative (minpoly (K⟮t⟯) θ)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable (K⟮t⟯) θ).aeval_derivative_ne_zero (minpoly.aeval _ _)
  have : x * aeval θ (derivative (minpoly (K⟮t⟯) θ)) = b := by
    rw [← hbx, smul_eq_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rw [this]
  exact mem_of_isIntegral w (adjoin_le_integralClosure hθi hb)

end Euler

section BelowPlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
  (t : F) (ht : Transcendental K t)
  [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
  (w : Place K F)

omit [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] in
include ht in

theorem exists_one_le_ord_sub (hw : 0 ≤ w.ord t) :
    ∃ c₀ : K, 1 ≤ w.ord (t - algebraMap K F c₀) := by
  haveI : Module.Finite K w.ResidueField := IsCurveOver.finiteResidue w
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)
  set tO : w.toValuationSubring := ⟨t, mem_of_ord_nonneg w hw⟩
  obtain ⟨c₀, hc₀⟩ := hbij.2 (residue w.toValuationSubring tO)
  refine ⟨c₀, ?_⟩
  have hmem : tO - algebraMap K w.toValuationSubring c₀ ∈ maximalIdeal w.toValuationSubring := by
    rw [← residue_eq_zero_iff, map_sub, ← hc₀]
    exact sub_eq_zero.mpr rfl
  have hne := sub_algebraMap_ne_zero t ht c₀
  have := (w.mem_maximalIdeal_iff_ord_pos hne
    (sub_mem tO.2 (w.algebraMap_mem' c₀))).mp hmem
  omega

omit [IsCurveOver K F] [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] in

theorem isRational_of_finite (w : Place K F) [Module.Finite K w.ResidueField] : w.IsRational := by
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

omit [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] in
theorem isRational : w.IsRational := by
  haveI : Module.Finite K w.ResidueField := IsCurveOver.finiteResidue w
  exact isRational_of_finite w

omit [IsAlgClosed K] [IsCurveOver K F] in

theorem isRational_restrict {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F] (hw : w.IsRational) : (w.restrict E).IsRational := by
  set v := w.restrict E
  intro rbar
  obtain ⟨r, rfl⟩ := residue_surjective rbar
  have hrF : algebraMap E F (r : E) ∈ w.toValuationSubring := (Place.mem_restrict_iff w).mp r.2
  obtain ⟨c, hc⟩ := hw (residue w.toValuationSubring ⟨algebraMap E F (r : E), hrF⟩)
  refine ⟨c, ?_⟩
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField, eq_comm, ← sub_eq_zero]
  change residue v.toValuationSubring r - residue v.toValuationSubring _ = 0
  rw [← map_sub, residue_eq_zero_iff]
  set z : v.toValuationSubring := r - algebraMap K v.toValuationSubring c with hz
  by_cases hz0 : z = 0
  · rw [hz0]; exact zero_mem _
  have hzE : (z : E) ≠ 0 := fun h => hz0 (Subtype.ext h)
  have hzF : algebraMap E F (z : E) ≠ 0 := by simpa using hzE

  have hzw : (⟨algebraMap E F (z : E), (Place.mem_restrict_iff w).mp z.2⟩ : w.toValuationSubring) ∈
      maximalIdeal w.toValuationSubring := by
    rw [← residue_eq_zero_iff]
    have : (⟨algebraMap E F (z : E), (Place.mem_restrict_iff w).mp z.2⟩ : w.toValuationSubring) =
        ⟨algebraMap E F (r : E), hrF⟩ - algebraMap K w.toValuationSubring c := by
      apply Subtype.ext
      simp only [hz, AddSubgroupClass.coe_sub, map_sub]
      change _ = algebraMap E F (r : E) - algebraMap K F c
      rw [IsScalarTower.algebraMap_apply K E F]
      rfl
    rw [this, map_sub, ← hc]
    exact sub_eq_zero.mpr rfl
  have hpos := (w.mem_maximalIdeal_iff_ord_pos hzF _).mp hzw
  rw [w.ord_restrict] at hpos
  apply (v.mem_maximalIdeal_iff_ord_pos' hz0).mpr
  change 0 < v.ord (z : E)
  have he := w.ramificationIndex_pos (F := E)
  by_contra hle
  push Not at hle
  have : (w.ramificationIndex E : ℤ) * (w.restrict E).ord (z : E) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hle
  omega

omit [IsAlgClosed K] [IsCurveOver K F] in
include ht in

theorem ord_sub_eq_ramificationIndex {c₀ : K} (h1 : 1 ≤ w.ord (t - algebraMap K F c₀)) :
    (w.restrict (K⟮t⟯)).ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K (K⟮t⟯) c₀) = 1 ∧
    w.ord (t - algebraMap K F c₀) = w.ramificationIndex (K⟮t⟯) := by
  set v := w.restrict (K⟮t⟯)
  set sE : (K⟮t⟯) := IntermediateField.AdjoinSimple.gen K t - algebraMap K (K⟮t⟯) c₀ with hsE
  have hsEF : algebraMap (K⟮t⟯) F sE = t - algebraMap K F c₀ := by
    rw [hsE, map_sub, IntermediateField.AdjoinSimple.algebraMap_gen, ← IsScalarTower.algebraMap_apply]
  have he := w.ramificationIndex_pos (F := (K⟮t⟯))
  set e := w.ramificationIndex (K⟮t⟯)
  have hrel : w.ord (t - algebraMap K F c₀) = e * v.ord sE := by rw [← hsEF, w.ord_restrict]

  obtain ⟨πv, hπv, -⟩ := v.exists_ord_eq_one_and_dCoord_eq
  have hπv0 : (πv : F) ≠ 0 := by
    intro h
    have : πv = 0 := by exact_mod_cast h
    rw [this] at hπv; simp at hπv
  have hπw : w.ord (πv : F) = e := by
    change w.ord (algebraMap (K⟮t⟯) F πv) = e
    rw [w.ord_restrict, hπv, mul_one]
  obtain ⟨n, r₁, s₁, hr₁, hs₁, hrepr⟩ := exists_repr t ht c₀ πv.2 hπv0
  have hord := ord_eq_mul_of_repr t ht w h1 hπv0 hr₁ hs₁ hrepr
  rw [hπw, hrel] at hord

  have hm : 1 ≤ v.ord sE := by
    by_contra hlt
    push Not at hlt
    have : (e : ℤ) * v.ord sE ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    omega
  have hnm : n * v.ord sE = 1 := by
    have : (e : ℤ) * (n * v.ord sE) = (e : ℤ) * 1 := by rw [mul_one]; linarith [hord]
    exact mul_left_cancel₀ (by exact_mod_cast he.ne') this
  have hm1 : v.ord sE = 1 := Int.eq_one_of_mul_eq_one_left (by omega) hnm
  exact ⟨hm1, by rw [hrel, hm1, mul_one]⟩

end BelowPlace

section KeyInequality

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
  (t : F) (ht : Transcendental K t)
  [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
  [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F]
  (w : Place K F) (hw : 0 ≤ w.ord t)

theorem ord_eval_minpoly_eq_one {θ : F}
    (hθi : IsIntegral (w.restrict (K⟮t⟯)).toValuationSubring θ)
    (hθtop : IntermediateField.adjoin (K⟮t⟯) ({θ} : Set F) = ⊤) {c : K}
    (hc1 : w.ord (θ - algebraMap K F c) = 1)
    (hc0 : ∀ w' : Place K F, w'.restrict (K⟮t⟯) = w.restrict (K⟮t⟯) → w' ≠ w →
      w'.ord (θ - algebraMap K F c) = 0) :
    (w.restrict (K⟮t⟯)).ord
      (((minpoly (w.restrict (K⟮t⟯)).toValuationSubring θ).eval
        ⟨algebraMap K (K⟮t⟯) c, (w.restrict (K⟮t⟯)).algebraMap_mem' c⟩ :
        (w.restrict (K⟮t⟯)).toValuationSubring) : (K⟮t⟯)) = 1 := by
  classical
  set v := w.restrict (K⟮t⟯) with hv
  set A := v.toValuationSubring
  set Q := minpoly A θ
  set b : A := ⟨algebraMap K (K⟮t⟯) c, v.algebraMap_mem' c⟩
  have hQ : Q.map (algebraMap A (K⟮t⟯)) = minpoly (K⟮t⟯) θ :=
    (minpoly.isIntegrallyClosed_eq_field_fractions' (K⟮t⟯) hθi).symm
  have hdeg : (minpoly (K⟮t⟯) θ).natDegree = Module.finrank (K⟮t⟯) F := by
    rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral θ), hθtop,
      IntermediateField.finrank_top']
  have hbF : algebraMap (K⟮t⟯) F (b : (K⟮t⟯)) = algebraMap K F c :=
    (IsScalarTower.algebraMap_apply K (K⟮t⟯) F c).symm
  have hnorm := Place.ord_norm_sub_eq_ord_eval v Q hQ hdeg b
  rw [hbF] at hnorm
  rw [← hnorm]

  have hθc0 : θ - algebraMap K F c ≠ 0 := by rintro h; rw [h] at hc1; simp at hc1
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (θ - algebraMap K F c) hθc0
  have hnf := Divisor.pushforwardNormFormula_of_isSeparable (K := K) (F := (K⟮t⟯)) (F' := F)
    _ hθc0 D hD v
  rw [← hnf, Divisor.pushforward_apply]
  have hwsupp : w ∈ D.support := by
    rw [Finsupp.mem_support_iff, hD w, hc1]; exact one_ne_zero
  rw [Finset.sum_eq_single_of_mem w hwsupp]
  · rw [if_pos rfl, hD w, hc1, one_mul, Nat.cast_eq_one]
    exact Place.inertiaDeg_eq_one_of_isRational w (isRational w) (isRational_restrict w (isRational w))
  · intro w' _ hne
    by_cases hr : w'.restrict (K⟮t⟯) = v
    · rw [if_pos hr, hD w', hc0 w' hr hne, zero_mul]
    · rw [if_neg hr]

include ht hw in

theorem ord_aeval_derivative_le {θ : F}
    (hθi : IsIntegral (w.restrict (K⟮t⟯)).toValuationSubring θ)
    (hθtop : IntermediateField.adjoin (K⟮t⟯) ({θ} : Set F) = ⊤) {c : K}
    (hc1 : w.ord (θ - algebraMap K F c) = 1)
    (hc0 : ∀ w' : Place K F, w'.restrict (K⟮t⟯) = w.restrict (K⟮t⟯) → w' ≠ w →
      w'.ord (θ - algebraMap K F c) = 0)
    {π : F} (hπ : w.ord π = 1) :
    Place.diffCoeff π (D K F t) = 0 ∨
      w.ord (aeval θ (derivative (minpoly (K⟮t⟯) θ))) ≤ w.ord (Place.diffCoeff π (D K F t)) := by
  classical
  set v := w.restrict (K⟮t⟯) with hv
  set A := v.toValuationSubring
  set Q := minpoly A θ with hQdef
  set b : A := ⟨algebraMap K (K⟮t⟯) c, v.algebraMap_mem' c⟩
  set e := w.ramificationIndex (K⟮t⟯)
  have he := w.ramificationIndex_pos (F := (K⟮t⟯))
  obtain ⟨c₀, h1⟩ := exists_one_le_ord_sub t ht w hw
  obtain ⟨hv1, hwe⟩ := ord_sub_eq_ramificationIndex t ht w h1
  have hst := sub_algebraMap_ne_zero t ht c₀
  have hθw : θ ∈ w.toValuationSubring := mem_of_isIntegral w hθi
  have hcw : algebraMap K F c ∈ w.toValuationSubring := w.algebraMap_mem' c
  have hθc0 : θ - algebraMap K F c ≠ 0 := by rintro h; rw [h] at hc1; simp at hc1

  set g : (K⟮t⟯) := ((Q.eval b : A) : (K⟮t⟯)) with hgdef
  have hg1 : v.ord g = 1 := ord_eval_minpoly_eq_one t w hθi hθtop hc1 hc0
  set gF : F := algebraMap (K⟮t⟯) F g with hgF
  have hgFw : w.ord gF = e := by rw [hgF, w.ord_restrict, ← hv, hg1, mul_one]
  have hgF0 : gF ≠ 0 := by
    intro h; rw [h] at hgFw; simp at hgFw; omega

  set sE : (K⟮t⟯) := IntermediateField.AdjoinSimple.gen K t - algebraMap K (K⟮t⟯) c₀ with hsE
  have hsEF : algebraMap (K⟮t⟯) F sE = t - algebraMap K F c₀ := by
    rw [hsE, map_sub, IntermediateField.AdjoinSimple.algebraMap_gen, ← IsScalarTower.algebraMap_apply]
  set uE : (K⟮t⟯) := g * sE⁻¹ with huE
  set u : F := algebraMap (K⟮t⟯) F uE with hu
  have hgu : gF = (t - algebraMap K F c₀) * u := by
    rw [hu, huE, map_mul, map_inv₀, hsEF, ← hgF]; field_simp
  have hu0 : u ≠ 0 := by intro h; rw [h, mul_zero] at hgu; exact hgF0 hgu
  have hordu : w.ord u = 0 := by
    have := congrArg w.ord hgu
    rw [w.ord_mul hst hu0, hgFw, hwe] at this
    omega
  have humem : u ∈ IntermediateField.adjoin K ({t} : Set F) := uE.2
  have huw : u ∈ w.toValuationSubring := mem_of_ord_nonneg w (by rw [hordu])

  have hDg : tD t ht gF = u + (t - algebraMap K F c₀) * tD t ht u := by
    rw [hgu, tD_mul, tD_sub_algebraMap, tD_self, mul_one, add_comm]
  have hDg0 : tD t ht gF ≠ 0 ∧ w.ord (tD t ht gF) = 0 := by
    rw [hDg]
    have := ord_add_eq_of_lt' w hu0 (b := (t - algebraMap K F c₀) * tD t ht u) (by
      by_cases h0 : tD t ht u = 0
      · left; rw [h0, mul_zero]
      right
      rw [hordu, w.ord_mul hst h0]
      have := ord_nonneg_of_mem w (tD_mem t ht w h1 humem huw)
      omega)
    rw [hordu] at this
    exact this

  set d := Q.natDegree
  set aF : ℕ → F := fun i => algebraMap (K⟮t⟯) F ((Q.coeff i : A) : (K⟮t⟯)) with haF
  have haFmem : ∀ i, aF i ∈ IntermediateField.adjoin K ({t} : Set F) := fun i => (Q.coeff i : A).1.2
  have haFw : ∀ i, aF i ∈ w.toValuationSubring := fun i =>
    (Place.mem_restrict_iff w).mp (Q.coeff i).2
  have hcF : algebraMap (K⟮t⟯) F (b : (K⟮t⟯)) = algebraMap K F c :=
    (IsScalarTower.algebraMap_apply K (K⟮t⟯) F c).symm

  have hgsum : gF = ∑ i ∈ Finset.range (d + 1), aF i * algebraMap K F c ^ i := by
    rw [hgF, hgdef, eval_eq_sum_range]
    change algebraMap A F (∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * b ^ i) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow]
    change aF i * (algebraMap (K⟮t⟯) F (b : (K⟮t⟯))) ^ i = _
    rw [hcF]

  have hDgsum : tD t ht gF = ∑ i ∈ Finset.range (d + 1), tD t ht (aF i) * algebraMap K F c ^ i := by
    rw [hgsum, tD_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tD_mul, ← map_pow, tD_algebraMap, mul_zero, zero_add, map_pow, mul_comm]

  set S₁ : F := ∑ i ∈ Finset.range (d + 1), tD t ht (aF i) * θ ^ i with hS₁
  have hfactor : ∀ i : ℕ, ∃ k : F, k ∈ w.toValuationSubring ∧
      θ ^ i - algebraMap K F c ^ i = (θ - algebraMap K F c) * k := by
    intro i
    obtain ⟨k, hk⟩ := sub_dvd_pow_sub_pow (⟨θ, hθw⟩ : w.toValuationSubring) ⟨algebraMap K F c, hcw⟩ i
    refine ⟨k, k.2, ?_⟩
    have := congrArg Subtype.val hk
    push_cast at this
    exact this
  choose k hk using hfactor
  have hS₁eq : S₁ = tD t ht gF + (θ - algebraMap K F c) *
      ∑ i ∈ Finset.range (d + 1), tD t ht (aF i) * k i := by
    rw [hDgsum, hS₁, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hk i).2
    calc tD t ht (aF i) * θ ^ i
        = tD t ht (aF i) * algebraMap K F c ^ i + tD t ht (aF i) * (θ ^ i - algebraMap K F c ^ i) := by
          ring
      _ = _ := by rw [this]; ring
  have hTmem : ∑ i ∈ Finset.range (d + 1), tD t ht (aF i) * k i ∈ w.toValuationSubring :=
    sum_mem fun i _ => mul_mem (tD_mem t ht w h1 (haFmem i) (haFw i)) (hk i).1
  have hS₁0 : S₁ ≠ 0 ∧ w.ord S₁ = 0 := by
    rw [hS₁eq]
    have := ord_add_eq_of_lt' w hDg0.1
      (b := (θ - algebraMap K F c) * ∑ i ∈ Finset.range (d + 1), tD t ht (aF i) * k i) (by
      by_cases h0 : ∑ i ∈ Finset.range (d + 1), tD t ht (aF i) * k i = 0
      · left; rw [h0, mul_zero]
      right
      rw [hDg0.2, w.ord_mul hθc0 h0, hc1]
      have := ord_nonneg_of_mem w hTmem
      omega)
    rw [hDg0.2] at this
    exact this

  set QF : F[X] := Q.map (algebraMap A F) with hQF
  have hQFdeg : QF.natDegree = d := (minpoly.monic hθi).natDegree_map _
  have hQFcoeff : ∀ i, QF.coeff i = aF i := fun i => by rw [hQF, coeff_map]; rfl
  have hQFeval : QF.eval θ = 0 := by
    rw [hQF, eval_map]; exact minpoly.aeval A θ
  have hevalsum : QF.eval θ = ∑ i ∈ Finset.range (d + 1), aF i * θ ^ i := by
    rw [eval_eq_sum_range, hQFdeg]
    exact Finset.sum_congr rfl fun i _ => by rw [hQFcoeff]
  set Q'θ : F := (derivative QF).eval θ with hQ'θ
  have hderivsum : Q'θ = ∑ i ∈ Finset.range (d + 1), aF i * i * θ ^ (i - 1) := by
    rw [hQ'θ, derivative_eval, sum_over_range _ (fun n => by simp), hQFdeg]
    exact Finset.sum_congr rfl fun i _ => by rw [hQFcoeff]
  have hident : Q'θ * tD t ht θ = -S₁ := by
    have h0 : tD t ht (∑ i ∈ Finset.range (d + 1), aF i * θ ^ i) = 0 := by
      rw [← hevalsum, hQFeval]
      have := tD_algebraMap t ht 0
      rwa [map_zero] at this
    rw [tD_sum] at h0
    have : ∑ i ∈ Finset.range (d + 1), tD t ht (aF i * θ ^ i) =
        Q'θ * tD t ht θ + S₁ := by
      rw [hderivsum, hS₁, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tD_mul, tD_pow]; ring
    rw [this] at h0
    linear_combination h0

  haveI : Algebra.IsAlgebraic (K⟮t⟯) F := Algebra.IsAlgebraic.of_finite _ _
  set δt := Place.diffCoeff π (D K F t) with hδt
  set δθ := Place.diffCoeff π (D K F θ) with hδθ
  have hDt : δt • D K F π = D K F t := Place.diffCoeff_smul_D_of_ord_eq_one t w hπ _
  have hDθ : δθ = tD t ht θ * δt := by
    have h := D_eq_tD_smul t ht θ
    rw [← hDt, smul_smul] at h
    rw [hδθ, h]
    exact Place.diffCoeff_smul_D_eq_of_ord_eq_one t w hπ _
  have hδθ0 : 0 ≤ w.ord δθ :=
    Place.ord_diffCoeff_D_nonneg_of_perfectField t w hπ (ord_nonneg_of_mem w hθw)
  by_cases hδt0 : δt = 0
  · exact Or.inl hδt0
  right
  have hprod : Q'θ * δθ = -S₁ * δt := by rw [hDθ, ← mul_assoc, hident]
  have hrhs0 : -S₁ * δt ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hS₁0.1) hδt0
  have hQ'0 : Q'θ ≠ 0 := by intro h; rw [h, zero_mul] at hprod; exact hrhs0 hprod.symm
  have hδθne : δθ ≠ 0 := by intro h; rw [h, mul_zero] at hprod; exact hrhs0 hprod.symm
  have hord := congrArg w.ord hprod
  rw [w.ord_mul hQ'0 hδθne, w.ord_mul (neg_ne_zero.mpr hS₁0.1) hδt0, ord_neg, hS₁0.2,
    zero_add] at hord

  have hQ' : aeval θ (derivative (minpoly (K⟮t⟯) θ)) = Q'θ := by
    rw [← (minpoly.isIntegrallyClosed_eq_field_fractions' (K⟮t⟯) hθi).symm, derivative_map,
      aeval_map_algebraMap, aeval_def, eval₂_eq_eval_map, ← derivative_map]
  rw [hQ']
  omega

end KeyInequality

section Inseparable

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] (t : F)
  [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]

theorem D_eq_zero_of_not_isSeparable (h : ¬ Algebra.IsSeparable (K⟮t⟯) F) : D K F t = 0 := by
  by_contra hD
  apply h
  haveI : Module.Finite F (Ω[F⁄K]) := Module.finite_of_finrank_eq_succ IsCurveOver.finrank_kaehler
  have hspan : Submodule.span F ({D K F t} : Set (Ω[F⁄K])) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton hD, IsCurveOver.finrank_kaehler]
  set f := KaehlerDifferential.map K (K⟮t⟯) F F with hf
  have hft : f (D K F t) = 0 := by
    rw [hf, KaehlerDifferential.map_D]
    have : algebraMap F F t = algebraMap (K⟮t⟯) F (IntermediateField.AdjoinSimple.gen K t) := by
      rw [IntermediateField.AdjoinSimple.algebraMap_gen]; rfl
    rw [this, Derivation.map_algebraMap]
  have hrange : LinearMap.range f = ⊥ := by
    rw [LinearMap.range_eq_map, ← hspan, Submodule.map_span, Set.image_singleton, hft,
      Submodule.span_singleton_eq_bot]
  have hsurj := KaehlerDifferential.map_surjective K (K⟮t⟯) F
  have hsub : Subsingleton (Ω[F⁄(K⟮t⟯)]) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    have ha : f a' ∈ LinearMap.range f := LinearMap.mem_range_self f a'
    have hb : f b' ∈ LinearMap.range f := LinearMap.mem_range_self f b'
    rw [hrange, Submodule.mem_bot] at ha hb
    change f a' = f b'
    rw [ha, hb]
  haveI : Algebra.FormallyUnramified (K⟮t⟯) F := ⟨hsub⟩
  exact Algebra.FormallyUnramified.isSeparable (K⟮t⟯) F

end Inseparable

section Assembly

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]

theorem final (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    (x : F)
    (hx : ∀ b : F, IsIntegral (Algebra.adjoin K ({t} : Set F)) b →
      ∃ P : Polynomial K,
        ((Algebra.trace (IntermediateField.adjoin K ({t} : Set F)) F (x * b) :
            IntermediateField.adjoin K ({t} : Set F)) : F) = Polynomial.aeval t P)
    (w : Place K F) (hw : 0 ≤ w.ord t) :
    ∃ g ∈ w.toValuationSubring, x • KaehlerDifferential.D K F t = g • w.dCoord := by
  by_cases hsep : Algebra.IsSeparable (K⟮t⟯) F
  swap
  · refine ⟨0, zero_mem _, ?_⟩
    rw [D_eq_zero_of_not_isSeparable t hsep, smul_zero, zero_smul]
  haveI : Algebra.IsAlgebraic (K⟮t⟯) F := Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨π, hπ, hdc⟩ := w.exists_ord_eq_one_and_dCoord_eq
  set δt := Place.diffCoeff π (D K F t) with hδt
  have hDt : δt • D K F π = D K F t := Place.diffCoeff_smul_D_of_ord_eq_one t w hπ _
  refine ⟨x * δt, ?_, by rw [hdc, mul_smul, hDt]⟩
  by_cases hx0 : x = 0
  · rw [hx0, zero_mul]; exact zero_mem _
  by_cases hδ0 : δt = 0
  · rw [hδ0, mul_zero]; exact zero_mem _

  obtain ⟨θ, hθi, hθtop, c, hc1, hc0⟩ :=
    Place.exists_isIntegral_adjoin_eq_top_ord_sub_algebraMap_eq_one (E := (K⟮t⟯)) w
  obtain ⟨c₀, h1⟩ := exists_one_le_ord_sub t ht w hw
  have hxdual : ∀ y : F, IsIntegral (w.restrict (K⟮t⟯)).toValuationSubring y →
      ((Algebra.trace (K⟮t⟯) F (x * y) : (K⟮t⟯)) : F) ∈ w.toValuationSubring :=
    fun y hy => trace_mul_mem t ht x hx w h1 hy
  have hmem := mul_aeval_derivative_mem t w hθi hθtop hxdual
  have hf'0 : aeval θ (derivative (minpoly (K⟮t⟯) θ)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable (K⟮t⟯) θ).aeval_derivative_ne_zero (minpoly.aeval _ _)
  rcases ord_aeval_derivative_le t ht w hw hθi hθtop hc1 hc0 hπ with h0 | hle
  · exact absurd h0 hδ0
  apply mem_of_ord_nonneg
  have h2 := ord_nonneg_of_mem w hmem
  rw [w.ord_mul hx0 hf'0] at h2
  rw [w.ord_mul hx0 hδ0]
  have h3 : w.ord x + w.ord (aeval θ (derivative (minpoly (K⟮t⟯) θ))) ≤ w.ord x + w.ord δt :=
    add_le_add_right hle _
  omega

end Assembly

end AlgebraicCurve.DedekindDifferentProof

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [AlgebraicCurve.IsCurveOver K F]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    (x : F)
    (hx : ∀ b : F, IsIntegral (Algebra.adjoin K ({t} : Set F)) b →
      ∃ P : Polynomial K,
        ((Algebra.trace (IntermediateField.adjoin K ({t} : Set F)) F (x * b) :
            IntermediateField.adjoin K ({t} : Set F)) : F) = Polynomial.aeval t P)
    (w : AlgebraicCurve.Place K F) (hw : 0 ≤ w.ord t) :
    ∃ g ∈ w.toValuationSubring, x • KaehlerDifferential.D K F t = g • w.dCoord :=
  AlgebraicCurve.DedekindDifferentProof.final t ht x hx w hw

end
end S_AlgebraicCurve_exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval
end P2MW
export P2MW.S_AlgebraicCurve_exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval (solution)
