-- Prove2me | solution 1 for AlgebraicCurve.exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6451d9d3-a7c5-56af-bf86-25be5da09c03

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import Theorems.Thm_KaehlerDifferential_span_D_eq_top_of_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord.AlgebraicCurve KaehlerDifferential IsLocalRing Polynomial"

attribute [local instance] SMulCommClass.of_commMonoid

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue Place.mem_maximalIdeal_iff_ord_pos Place.integralClosureAt Place.forall_mem_of_restrict_eq Place.fiberCenter Place.mem_fiberCenter_iff_ord_pos Place.toValuationSubring_eq_of_restrict_eq Place.eq_of_fiberCenter_eq Place.mem_fiberOver Place.restrict_eq_of_mem_fiberOver Place.mem_fiber Place.min_ord_le_ord_add essFiniteType_of_transcendental_of_finiteDimensional Place.exists_integralClosureAt_of_ord_fiber_nonneg dCoordGenerates_of_isCurveOver Place.ord_diffCoeff_D_nonneg_of_perfectField Place.diffCoeff Place.diffCoeff_smul_D Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed"
namespace DedekindTraceProof
p2m_open "AlgebraicCurve"

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_coe_nonneg (v : Place K F) (f : v.toValuationSubring) : 0 ≤ v.ord (f : F) := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hπ
  have : (f : F) = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    rw [hu, zpow_natCast]; push_cast; rfl
  rw [this, v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ord_coe_nonneg v ⟨f, hf⟩

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem inv_mem_of_ord_eq_zero (v : Place K F) {f : F} (h : v.ord f = 0) :
    f⁻¹ ∈ v.toValuationSubring :=
  mem_of_ord_nonneg v (by rw [v.ord_inv, h, neg_zero])

theorem le_ord_add (v : Place K F) {a b : F} {m : ℤ} (ha : a = 0 ∨ m ≤ v.ord a)
    (hb : b = 0 ∨ m ≤ v.ord b) (hab : a + b ≠ 0) : m ≤ v.ord (a + b) := by
  rcases ha with rfl | ha
  · rw [zero_add] at hab ⊢
    exact hb.resolve_left hab
  rcases hb with rfl | hb
  · rw [add_zero]
    exact ha
  by_cases ha0 : a = 0
  · rw [ha0, zero_add] at hab ⊢; exact hb
  by_cases hb0 : b = 0
  · rw [hb0, add_zero]; exact ha
  exact (le_min ha hb).trans (Place.min_ord_le_ord_add v ha0 hb0 hab)

theorem ord_algebraMap' (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  by_cases hc : c = 0
  · rw [hc, map_zero, v.ord_zero]
  have h1 : 0 ≤ v.ord (algebraMap K F c) := ord_nonneg_of_mem v (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) := ord_nonneg_of_mem v (v.algebraMap_mem' c⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

theorem ord_neg (v : Place K F) (a : F) : v.ord (-a) = v.ord a := by
  by_cases ha : a = 0
  · rw [ha, neg_zero]
  rw [neg_eq_neg_one_mul, v.ord_mul (by norm_num) ha,
    show (-1 : F) = algebraMap K F (-1) by simp, ord_algebraMap', zero_add]

theorem ord_add_eq_of_lt (v : Place K F) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : v.ord a < v.ord b) : v.ord (a + b) = v.ord a := by
  have hab : a + b ≠ 0 := by
    intro h0
    have : a = -b := eq_neg_of_add_eq_zero_left h0
    rw [this, ord_neg] at h
    exact lt_irrefl _ h
  have h1 : v.ord a ≤ v.ord (a + b) := by
    have := Place.min_ord_le_ord_add v ha hb hab
    rwa [min_eq_left h.le] at this
  have h2 : v.ord (a + b) ≤ v.ord a := by
    by_contra hlt
    push Not at hlt
    have hmin := Place.min_ord_le_ord_add v hab (neg_ne_zero.mpr hb)
      (by rw [add_neg_cancel_right]; exact ha)
    rw [add_neg_cancel_right, ord_neg] at hmin
    have : min (v.ord (a + b)) (v.ord b) > v.ord a := lt_min hlt h
    omega
  exact le_antisymm h2 h1

theorem exists_eq_mul_of_ord_pos (v : Place K F) {π : F} (hπ : v.ord π = 1) {a : F}
    (ha : a = 0 ∨ 1 ≤ v.ord a) : ∃ b ∈ v.toValuationSubring, a = π * b := by
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  refine ⟨π⁻¹ * a, mem_of_ord_nonneg v ?_, by rw [← mul_assoc, mul_inv_cancel₀ hπ0, one_mul]⟩
  rcases ha with rfl | ha
  · rw [mul_zero, v.ord_zero]
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  rw [v.ord_mul (inv_ne_zero hπ0) ha0, v.ord_inv, hπ]
  omega

def subalg (v : Place K F) : Subalgebra K F where
  carrier := v.toValuationSubring
  mul_mem' ha hb := mul_mem ha hb
  add_mem' ha hb := add_mem ha hb
  algebraMap_mem' c := v.algebraMap_mem' c

theorem mem_subalg (v : Place K F) {f : F} : f ∈ subalg v ↔ f ∈ v.toValuationSubring := Iff.rfl

theorem aeval_mem (v : Place K F) {t : F} (ht : t ∈ v.toValuationSubring) (p : K[X]) :
    aeval t p ∈ v.toValuationSubring := by
  have h : Algebra.adjoin K {t} ≤ subalg v :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((mem_subalg v).mpr ht))
  exact h (aeval_mem_adjoin_singleton K t)

theorem le_ord_of_mem_maximalIdeal_pow (v : Place K F) {n : ℕ} {z : v.toValuationSubring}
    (hz : z ∈ (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n) (hz0 : (z : F) ≠ 0) :
    (n : ℤ) ≤ v.ord (z : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
  obtain ⟨r, hr⟩ := hz
  have hcoe : (z : F) = (π : F) ^ n * (r : F) := by rw [hr]; push_cast; rfl
  have hπ0 : (π : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hr0 : (r : F) ≠ 0 := by
    intro h0; rw [hcoe, h0, mul_zero] at hz0; exact hz0 rfl
  rw [hcoe, v.ord_mul (pow_ne_zero _ hπ0) hr0, ← zpow_natCast, v.ord_zpow,
    v.ord_coe_irreducible hπ, mul_one]
  have := ord_coe_nonneg v r
  omega

theorem exists_sub_algebraMap [IsAlgClosed K] [IsCurveOver K F] (w : Place K F) {f : F}
    (hf : f ∈ w.toValuationSubring) :
    ∃ c : K, f - algebraMap K F c = 0 ∨ 1 ≤ w.ord (f - algebraMap K F c) := by
  haveI : Module.Finite K w.ResidueField := IsCurveOver.finiteResidue w
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  set fO : w.toValuationSubring := ⟨f, hf⟩ with hfO
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := w.ResidueField)).2 (IsLocalRing.residue w.toValuationSubring fO)
  refine ⟨c, ?_⟩
  by_cases hne : f - algebraMap K F c = 0
  · exact Or.inl hne
  right
  have hmem : fO - algebraMap K w.toValuationSubring c ∈
      IsLocalRing.maximalIdeal w.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc]
    rw [IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField c]
    exact sub_self _
  have hcoe : ((fO - algebraMap K w.toValuationSubring c : w.toValuationSubring) : F) =
      f - algebraMap K F c := by
    rw [hfO]; push_cast; rw [Place.coe_algebraMap]
  have h1 := le_ord_of_mem_maximalIdeal_pow w (n := 1) (by rwa [pow_one]) (by rwa [hcoe])
  rwa [hcoe] at h1

end PlaceFacts

section LocalCalculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
variable (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
variable [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable {w : Place K F}
variable {π : F} (hπ : w.ord π = 1) (hdc : w.dCoord = D K F π)

include hdc in
theorem D_eq_diffCoeff_smul (f : F) :
    D K F f = Place.diffCoeff π (D K F f) • D K F π := by
  haveI : w.DCoordGenerates := dCoordGenerates_of_isCurveOver w
  obtain ⟨c, hc⟩ := w.exists_eq_smul_dCoord (D K F f)
  rw [hdc] at hc
  exact (Place.diffCoeff_smul_D ⟨c, hc⟩).symm

include hdc in
theorem D_pi_ne_zero : D K F π ≠ 0 := by
  haveI : w.DCoordGenerates := dCoordGenerates_of_isCurveOver w
  rw [← hdc]; exact w.dCoord_ne_zero

include hdc in
theorem coeff_unique {a b : F} (h : a • D K F π = b • D K F π) : a = b :=
  smul_left_injective F (D_pi_ne_zero hdc) h

include hdc in
theorem diffCoeff_eq_of_eq {f c : F} (h : D K F f = c • D K F π) :
    Place.diffCoeff π (D K F f) = c :=
  coeff_unique hdc ((D_eq_diffCoeff_smul hdc f).symm.trans h)

include hdc in
theorem diffCoeff_pi : Place.diffCoeff π (D K F π) = 1 :=
  diffCoeff_eq_of_eq hdc (one_smul F _).symm

include hdc in

theorem diffCoeff_mul (f g : F) :
    Place.diffCoeff π (D K F (f * g)) =
      f * Place.diffCoeff π (D K F g) + g * Place.diffCoeff π (D K F f) := by
  apply diffCoeff_eq_of_eq hdc
  rw [Derivation.leibniz]
  conv_lhs => rw [D_eq_diffCoeff_smul hdc f, D_eq_diffCoeff_smul hdc g, smul_smul, smul_smul]
  rw [add_smul]

include hdc in
theorem diffCoeff_sub_algebraMap (f : F) (c : K) :
    Place.diffCoeff π (D K F (f - algebraMap K F c)) = Place.diffCoeff π (D K F f) := by
  apply diffCoeff_eq_of_eq hdc
  rw [map_sub, Derivation.map_algebraMap, sub_zero, ← D_eq_diffCoeff_smul hdc f]

include x₀ hπ in
omit [Algebra.EssFiniteType K F] [IsCurveOver K F] in

theorem ord_diffCoeff_nonneg {f : F} (hf : 0 ≤ w.ord f) :
    0 ≤ w.ord (Place.diffCoeff π (D K F f)) :=
  Place.ord_diffCoeff_D_nonneg_of_perfectField x₀ w hπ hf

include x₀ hπ hdc in

theorem ord_diffCoeff_eq_zero_of_ord_eq_one {t : F} (ht : w.ord t = 1) :
    w.ord (Place.diffCoeff π (D K F t)) = 0 ∧ Place.diffCoeff π (D K F t) ≠ 0 := by
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  set u : F := t * π⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero ht0 (inv_ne_zero hπ0)
  have hordu : w.ord u = 0 := by rw [hu, w.ord_mul ht0 (inv_ne_zero hπ0), w.ord_inv, hπ, ht]; ring
  have htu : t = π * u := by rw [hu, mul_comm, mul_assoc, inv_mul_cancel₀ hπ0, mul_one]
  have hδu : 0 ≤ w.ord (Place.diffCoeff π (D K F u)) :=
    ord_diffCoeff_nonneg x₀ hπ (by rw [hordu])
  have hcalc : Place.diffCoeff π (D K F t) = π * Place.diffCoeff π (D K F u) + u := by
    rw [htu, diffCoeff_mul hdc, diffCoeff_pi hdc, mul_one]
  have key : ¬ (1 ≤ w.ord (Place.diffCoeff π (D K F t))) ∧ Place.diffCoeff π (D K F t) ≠ 0 := by
    have hπδ : π * Place.diffCoeff π (D K F u) = 0 ∨
        1 ≤ w.ord (π * Place.diffCoeff π (D K F u)) := by
      by_cases h0 : Place.diffCoeff π (D K F u) = 0
      · left; rw [h0, mul_zero]
      · right; rw [w.ord_mul hπ0 h0, hπ]; omega
    constructor
    · intro h1
      have hu' : u = Place.diffCoeff π (D K F t) + -(π * Place.diffCoeff π (D K F u)) := by
        rw [hcalc]; ring
      have : 1 ≤ w.ord u := by
        rw [hu']
        refine le_ord_add w (Or.inr h1) ?_ (by rw [← hu']; exact hu0)
        rcases hπδ with h | h
        · left; rw [h, neg_zero]
        · right
          rwa [ord_neg]
      omega
    · intro h0
      rw [hcalc] at h0
      have hu' : u = -(π * Place.diffCoeff π (D K F u)) := eq_neg_of_add_eq_zero_right h0
      rcases hπδ with h | h
      · exact hu0 (by rw [hu', h, neg_zero])
      · have : 1 ≤ w.ord u := by
          rw [hu', ord_neg]
          exact h
        omega
  refine ⟨le_antisymm (by omega) ?_, key.2⟩
  have hmem : Place.diffCoeff π (D K F t) ∈ w.toValuationSubring := by
    rw [hcalc]
    exact add_mem (mul_mem (mem_of_ord_nonneg w (by rw [hπ]; omega)) (mem_of_ord_nonneg w hδu))
      (mem_of_ord_nonneg w (by rw [hordu]))
  exact ord_nonneg_of_mem w hmem

end LocalCalculus

section Derivations

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_derivation_of_span_eq_top {ω₀ : Ω[F⁄K]} (hne : ω₀ ≠ 0)
    (htop : Submodule.span F ({ω₀} : Set Ω[F⁄K]) = ⊤) :
    ∃ δ : Derivation K F F, ∀ z : F, D K F z = δ z • ω₀ := by
  let ℓ : Ω[F⁄K] →ₗ[F] F :=
    (LinearEquiv.coord F Ω[F⁄K] ω₀ hne).toLinearMap ∘ₗ
      ((LinearEquiv.ofTop _ htop).symm : Ω[F⁄K] →ₗ[F] Submodule.span F ({ω₀} : Set Ω[F⁄K]))
  have hℓ : ∀ ω : Ω[F⁄K], ℓ ω • ω₀ = ω := by
    intro ω
    have h := LinearEquiv.coord_apply_smul F Ω[F⁄K] ω₀ hne ((LinearEquiv.ofTop _ htop).symm ω)
    simp [ℓ] at h ⊢
  refine ⟨ℓ.compDer (D K F), fun z => ?_⟩
  exact (hℓ (D K F z)).symm

theorem derivation_eval (δ : Derivation K F F) (p : F[X]) (θ : F) :
    δ (p.eval θ) = (derivative p).eval θ * δ θ + p.sum (fun i a => δ a * θ ^ i) := by
  rw [eval_eq_sum, derivative_eval, Polynomial.sum_def, Polynomial.sum_def, Polynomial.sum_def,
    map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul, nsmul_eq_mul,
    smul_eq_mul]
  ring

end Derivations

section RationalFunctions

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem eval_eq_zero_of_ord_pos (w : Place K F) {t : F} {c : K}
    (hc : 0 < w.ord (t - algebraMap K F c)) (r : K[X])
    (hr : aeval t r = 0 ∨ 0 < w.ord (aeval t r)) : r.eval c = 0 := by
  by_contra hne
  have htc0 : t - algebraMap K F c ≠ 0 := by rintro h; rw [h, w.ord_zero] at hc; exact lt_irrefl _ hc
  have ht : t ∈ w.toValuationSubring := by
    have : t = (t - algebraMap K F c) + algebraMap K F c := by ring
    rw [this]
    exact add_mem (mem_of_ord_nonneg w hc.le) (w.algebraMap_mem' c)
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := c) (p := r)
  have hq' : aeval t r - algebraMap K F (r.eval c) = (t - algebraMap K F c) * aeval t q := by
    have := congrArg (aeval t) hq
    simpa [map_sub, map_mul, aeval_X, aeval_C] using this

  have hconst : algebraMap K F (r.eval c) = aeval t r + -((t - algebraMap K F c) * aeval t q) := by
    rw [← hq']; ring
  have h0 : algebraMap K F (r.eval c) ≠ 0 := by simpa using hne
  have hpos : 1 ≤ w.ord (algebraMap K F (r.eval c)) := by
    rw [hconst]
    refine le_ord_add w ?_ ?_ (by rw [← hconst]; exact h0)
    · rcases hr with h | h
      · exact Or.inl h
      · exact Or.inr h
    · by_cases hq0 : aeval t q = 0
      · left; rw [hq0, mul_zero, neg_zero]
      · right
        rw [ord_neg, w.ord_mul htc0 hq0]
        have := ord_nonneg_of_mem w (aeval_mem w ht q)
        omega
  rw [ord_algebraMap'] at hpos
  omega

theorem ord_aeval_eq_zero (w : Place K F) {t : F} {c : K}
    (hc : 0 < w.ord (t - algebraMap K F c)) {s : K[X]} (hs : s.eval c ≠ 0) :
    w.ord (aeval t s) = 0 ∧ aeval t s ∈ w.toValuationSubring := by
  have ht : t ∈ w.toValuationSubring := by
    have : t = (t - algebraMap K F c) + algebraMap K F c := by ring
    rw [this]
    exact add_mem (mem_of_ord_nonneg w hc.le) (w.algebraMap_mem' c)
  have hmem := aeval_mem w ht s
  refine ⟨?_, hmem⟩
  have h0 := ord_nonneg_of_mem w hmem
  by_contra hne
  exact hs (eval_eq_zero_of_ord_pos w hc s (Or.inr (by omega)))

theorem exists_eq_div_eval_ne_zero (w : Place K F) {t : F} (htr : Transcendental K t) {c : K}
    (hc : 0 < w.ord (t - algebraMap K F c)) :
    ∀ (n : ℕ) (r s : K[X]), s.natDegree ≤ n → s ≠ 0 →
      aeval t r / aeval t s ∈ w.toValuationSubring →
      ∃ r' s' : K[X], s'.eval c ≠ 0 ∧ aeval t r / aeval t s = aeval t r' / aeval t s' := by
  have haev : ∀ p : K[X], p ≠ 0 → aeval t p ≠ 0 := fun p hp h => htr ⟨p, hp, h⟩
  have htc0 : t - algebraMap K F c ≠ 0 := by
    rintro h; rw [h, w.ord_zero] at hc; exact lt_irrefl _ hc
  intro n
  induction n with
  | zero =>
    intro r s hs hs0 hmem
    refine ⟨r, s, ?_, rfl⟩
    rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hs), eval_C]
    intro h0
    apply hs0
    rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hs), h0, map_zero]
  | succ n ih =>
    intro r s hs hs0 hmem
    by_cases hsc : s.eval c = 0
    ·
      have hs1 : (X - C c) * (s /ₘ (X - C c)) = s := mul_divByMonic_eq_iff_isRoot.mpr hsc
      set s₁ := s /ₘ (X - C c) with hs₁
      have hs₁0 : s₁ ≠ 0 := by rintro h; rw [h, mul_zero] at hs1; exact hs0 hs1.symm
      have hdeg : s₁.natDegree ≤ n := by
        rw [hs₁, natDegree_divByMonic _ (monic_X_sub_C c), natDegree_X_sub_C]; omega
      have hrc : r.eval c = 0 := by
        refine eval_eq_zero_of_ord_pos w hc r ?_
        by_cases hr0 : aeval t r = 0
        · exact Or.inl hr0
        right
        have hy : aeval t r = (aeval t r / aeval t s) * ((t - algebraMap K F c) * aeval t s₁) := by
          rw [← hs1]; simp [map_mul, aeval_X, aeval_C]
          rw [div_mul_cancel₀]
          exact mul_ne_zero htc0 (haev _ hs₁0)
        have hy0 : aeval t r / aeval t s ≠ 0 := div_ne_zero hr0 (haev s hs0)
        rw [hy, w.ord_mul hy0 (mul_ne_zero htc0 (haev _ hs₁0)), w.ord_mul htc0 (haev _ hs₁0)]
        have h1 := ord_nonneg_of_mem w hmem
        have h2 : t ∈ w.toValuationSubring := by
          have : t = (t - algebraMap K F c) + algebraMap K F c := by ring
          rw [this]; exact add_mem (mem_of_ord_nonneg w hc.le) (w.algebraMap_mem' c)
        have h3 := ord_nonneg_of_mem w (aeval_mem w h2 s₁)
        omega
      have hr1 : (X - C c) * (r /ₘ (X - C c)) = r := mul_divByMonic_eq_iff_isRoot.mpr hrc
      set r₁ := r /ₘ (X - C c)
      have heq : aeval t r / aeval t s = aeval t r₁ / aeval t s₁ := by
        rw [← hr1, ← hs1]
        simp only [map_mul, map_sub, aeval_X, aeval_C]
        rw [mul_div_mul_left _ _ htc0]
      obtain ⟨r', s', h1, h2⟩ := ih r₁ s₁ hdeg hs₁0 (by rwa [← heq])
      exact ⟨r', s', h1, heq.trans h2⟩
    · exact ⟨r, s, hsc, rfl⟩

theorem derivation_mem_of_mem_adjoin (δ : Derivation K F F) {t : F} (htr : Transcendental K t)
    (hδt : δ t = 1) (w : Place K F) {c : K} (hc : 0 < w.ord (t - algebraMap K F c))
    {a : F} (ha : a ∈ IntermediateField.adjoin K ({t} : Set F)) (haw : a ∈ w.toValuationSubring) :
    δ a ∈ w.toValuationSubring := by
  have haev : ∀ p : K[X], p ≠ 0 → aeval t p ≠ 0 := fun p hp h => htr ⟨p, hp, h⟩
  have hδp : ∀ p : K[X], δ (aeval t p) = aeval t (derivative p) := by
    intro p; rw [Derivation.map_aeval, hδt, smul_eq_mul, mul_one]
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K a).mp ha
  by_cases hs0 : s = 0
  · rw [hrs, hs0, map_zero, div_zero, map_zero]; exact zero_mem _
  obtain ⟨r', s', hs'c, heq⟩ :=
    exists_eq_div_eval_ne_zero w htr hc s.natDegree r s le_rfl hs0 (by rwa [← hrs])
  have hs'0 : s' ≠ 0 := by rintro rfl; exact hs'c (by simp)
  obtain ⟨hord, hs'mem⟩ := ord_aeval_eq_zero w hc hs'c
  have ht : t ∈ w.toValuationSubring := by
    have : t = (t - algebraMap K F c) + algebraMap K F c := by ring
    rw [this]; exact add_mem (mem_of_ord_nonneg w hc.le) (w.algebraMap_mem' c)

  have hmul : a * aeval t s' = aeval t r' := by
    rw [hrs, heq, div_mul_cancel₀ _ (haev s' hs'0)]
  have hleib := congrArg δ hmul
  rw [Derivation.leibniz, hδp, hδp, smul_eq_mul, smul_eq_mul] at hleib
  have hδa : δ a = (aeval t (derivative r') - a * aeval t (derivative s')) * (aeval t s')⁻¹ := by
    rw [← hleib]; field_simp [haev s' hs'0]; ring
  rw [hδa]
  exact mul_mem (sub_mem (aeval_mem w ht _) (mul_mem haw (aeval_mem w ht _)))
    (inv_mem_of_ord_eq_zero w hord)

theorem exists_ord_sub_pos [IsAlgClosed K] [IsCurveOver K F] {t : F} (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] (c : K) :
    ∃ w : Place K F, 0 < w.ord (t - algebraMap K F c) := by
  set f := t - algebraMap K F c with hf
  have hf0 : f ≠ 0 := by
    intro h
    apply htr
    have : t = algebraMap K F c := sub_eq_zero.mp h
    rw [this]; exact isAlgebraic_algebraMap c

  have hex : ∃ v : Place K F, v.ord f ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨a, ha⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed t htr hall
    apply htr
    have : t = algebraMap K F (a + c) := by rw [map_add, ha, hf]; ring
    rw [this]; exact isAlgebraic_algebraMap _
  obtain ⟨v, hv⟩ := hex
  rcases lt_or_gt_of_ne hv with hneg | hpos
  swap
  · exact ⟨v, hpos⟩

  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  by_contra hnone
  push Not at hnone
  have hdeg1 : ∀ u : Place K F, (u.deg : ℤ) = 1 := fun u => by
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed u]; rfl
  have hsum : Divisor.degree D = ∑ u ∈ D.support, D u := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [hdeg1 u]
  classical
  have hvmem : v ∈ D.support := by
    rw [Finsupp.mem_support_iff, hD v]; omega
  have := Finset.add_sum_erase D.support (fun u => D u) hvmem
  rw [← hsum, hdeg] at this
  have hle : ∑ u ∈ D.support.erase v, D u ≤ 0 :=
    Finset.sum_nonpos fun u _ => by rw [hD u]; exact hnone u
  rw [hD v] at this
  omega

theorem exists_eq_aeval_of_forall_mem [IsAlgClosed K] [IsCurveOver K F] {t : F}
    (htr : Transcendental K t) [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    {y : F} (hy : y ∈ IntermediateField.adjoin K ({t} : Set F))
    (hyw : ∀ w : Place K F, 0 ≤ w.ord t → y ∈ w.toValuationSubring) :
    ∃ P : K[X], y = aeval t P := by
  have haev : ∀ p : K[X], p ≠ 0 → aeval t p ≠ 0 := fun p hp h => htr ⟨p, hp, h⟩
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K y).mp hy

  suffices h : ∀ (n : ℕ) (r s : K[X]), s.natDegree ≤ n →
      (∀ w : Place K F, 0 ≤ w.ord t → aeval t r / aeval t s ∈ w.toValuationSubring) →
      ∃ P : K[X], aeval t r / aeval t s = aeval t P by
    obtain ⟨P, hP⟩ := h s.natDegree r s le_rfl (by rw [← hrs]; exact hyw)
    exact ⟨P, hrs.trans hP⟩
  intro n
  induction n with
  | zero =>
    intro r s hs _
    obtain ⟨a, ha⟩ : ∃ a, s = C a := ⟨_, Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hs)⟩
    refine ⟨C a⁻¹ * r, ?_⟩
    rw [ha, aeval_C, map_mul, aeval_C, map_inv₀, div_eq_inv_mul]
  | succ n ih =>
    intro r s hs hmem
    by_cases hs0 : s = 0
    · exact ⟨0, by simp [hs0]⟩
    by_cases hsn : s.natDegree = 0
    · exact ih r s (by omega) hmem

    obtain ⟨c, hc⟩ := IsAlgClosed.exists_root s (by rw [degree_eq_natDegree hs0]; exact_mod_cast hsn)
    obtain ⟨w, hw⟩ := exists_ord_sub_pos htr c
    have htc0 : t - algebraMap K F c ≠ 0 := by
      rintro h; rw [h, w.ord_zero] at hw; exact lt_irrefl _ hw
    have ht : t ∈ w.toValuationSubring := by
      have : t = (t - algebraMap K F c) + algebraMap K F c := by ring
      rw [this]; exact add_mem (mem_of_ord_nonneg w hw.le) (w.algebraMap_mem' c)
    have hs1 : (X - C c) * (s /ₘ (X - C c)) = s := mul_divByMonic_eq_iff_isRoot.mpr hc
    set s₁ := s /ₘ (X - C c) with hs₁
    have hs₁0 : s₁ ≠ 0 := by rintro h; rw [h, mul_zero] at hs1; exact hs0 hs1.symm
    have hdeg : s₁.natDegree ≤ n := by
      rw [hs₁, natDegree_divByMonic _ (monic_X_sub_C c), natDegree_X_sub_C]; omega
    have hrc : r.eval c = 0 := by
      refine eval_eq_zero_of_ord_pos w hw r ?_
      by_cases hr0 : aeval t r = 0
      · exact Or.inl hr0
      right
      have hy : aeval t r = (aeval t r / aeval t s) * ((t - algebraMap K F c) * aeval t s₁) := by
        rw [← hs1]; simp [map_mul, aeval_X, aeval_C]
        rw [div_mul_cancel₀]
        exact mul_ne_zero htc0 (haev _ hs₁0)
      have hy0 : aeval t r / aeval t s ≠ 0 := div_ne_zero hr0 (haev s hs0)
      rw [hy, w.ord_mul hy0 (mul_ne_zero htc0 (haev _ hs₁0)), w.ord_mul htc0 (haev _ hs₁0)]
      have h1 := ord_nonneg_of_mem w (hmem w (ord_nonneg_of_mem w ht))
      have h3 := ord_nonneg_of_mem w (aeval_mem w ht s₁)
      omega
    have hr1 : (X - C c) * (r /ₘ (X - C c)) = r := mul_divByMonic_eq_iff_isRoot.mpr hrc
    set r₁ := r /ₘ (X - C c)
    have heq : aeval t r / aeval t s = aeval t r₁ / aeval t s₁ := by
      rw [← hr1, ← hs1]
      simp only [map_mul, map_sub, aeval_X, aeval_C]
      rw [mul_div_mul_left _ _ htc0]
    obtain ⟨P, hP⟩ := ih r₁ s₁ hdeg (by intro w' hw'; rw [← heq]; exact hmem w' hw')
    exact ⟨P, heq.trans hP⟩

end RationalFunctions

section Fibre

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : IntermediateField K F} [FiniteDimensional E F] [Algebra.IsSeparable E F]
variable {v : Place K E}

scoped instance instIsScalarTowerConst (v : Place K E) : IsScalarTower K v.toValuationSubring F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K E F c]
    rfl

theorem algebraMap_valuationSubring_apply (a : v.toValuationSubring) :
    algebraMap v.toValuationSubring F a = ((a : E) : F) := rfl

theorem coe_algebraMap_integralClosureAt (a : v.toValuationSubring) :
    ((algebraMap v.toValuationSubring (Place.integralClosureAt F v) a :
      Place.integralClosureAt F v) : F) = ((a : E) : F) := rfl

def constC (v : Place K E) (c : K) : Place.integralClosureAt F v :=
  algebraMap v.toValuationSubring (Place.integralClosureAt F v) (algebraMap K v.toValuationSubring c)

@[scoped simp] theorem coe_constC (c : K) : ((constC (F := F) v c : Place.integralClosureAt F v) : F) =
    algebraMap K F c := by
  rw [constC, coe_algebraMap_integralClosureAt, Place.coe_algebraMap]
  exact (IsScalarTower.algebraMap_apply K E F c).symm

theorem mem_valuationSubring_iff {w : Place K F} (hw : w.restrict E = v) (a : E) :
    a ∈ v.toValuationSubring ↔ (a : F) ∈ w.toValuationSubring := by
  rw [← hw]; exact Iff.rfl

theorem exists_coe_eq_of_forall_mem [IsCurveOver K F] {z : F}
    (hz : ∀ w : Place K F, w.restrict E = v → z ∈ w.toValuationSubring) :
    ∃ c : Place.integralClosureAt F v, (c : F) = z := by
  by_cases hz0 : z = 0
  · exact ⟨0, by rw [hz0]; rfl⟩
  exact Place.exists_integralClosureAt_of_ord_fiber_nonneg (v := v) hz0
    fun w hw => ord_nonneg_of_mem w (hz w (Place.mem_fiber.mp hw))

theorem one_le_ord_of_irreducible {w : Place K F} (hw : w.restrict E = v)
    {π₀ : v.toValuationSubring} (hπ₀ : Irreducible π₀) : 1 ≤ w.ord ((π₀ : E) : F) := by
  have h := w.ord_restrict (F := E) (π₀ : E)
  rw [hw, v.ord_coe_irreducible hπ₀, mul_one] at h
  have hpos := w.ramificationIndex_pos (F := E)
  change w.ord ((π₀ : E) : F) = _ at h
  omega

theorem exists_ord_coe_eq_one {w : Place K F} (hw : w.restrict E = v) :
    ∃ ϖ : Place.integralClosureAt F v, w.ord (ϖ : F) = 1 := by
  obtain ⟨πw, hπw⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπw1 : w.ord (πw : F) = 1 := w.ord_coe_irreducible hπw
  have hπw0 : (πw : F) ≠ 0 := by rintro h; rw [h, w.ord_zero] at hπw1; exact zero_ne_one hπw1
  set P := Place.fiberCenter F v hw with hPdef
  have hmem : (πw : F) ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P := by
    rw [hPdef, ← Place.toValuationSubring_eq_of_restrict_eq hw]; exact πw.2
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj P.asIdeal.primeCompl
    (⟨(πw : F), hmem⟩ : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P)
  have has' : (πw : F) * (s : F) = (a : F) := by
    have h := congrArg (fun r : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P =>
      (r : F)) has
    first
      | exact h
      | simpa [IsScalarTower.algebraMap_apply (Place.integralClosureAt F v)
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P) F] using h
      | (simp only [IsScalarTower.algebraMap_apply (Place.integralClosureAt F v)
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F P) F] at h; exact h)
  have hs : (s : Place.integralClosureAt F v) ∉ P.asIdeal := s.2
  have hs0 : (s : Place.integralClosureAt F v) ≠ 0 := by
    intro h; exact hs (by rw [h]; exact zero_mem _)
  have hsF0 : ((s : Place.integralClosureAt F v) : F) ≠ 0 := by
    simpa using (IsFractionRing.injective (Place.integralClosureAt F v) F).ne_iff.mpr hs0
  have hords : w.ord ((s : Place.integralClosureAt F v) : F) = 0 := by
    have h1 : 0 ≤ w.ord ((s : Place.integralClosureAt F v) : F) :=
      ord_nonneg_of_mem w (Place.forall_mem_of_restrict_eq hw _)
    have h2 : ¬ 0 < w.ord ((s : Place.integralClosureAt F v) : F) := fun h =>
      hs ((Place.mem_fiberCenter_iff_ord_pos hw hs0).mpr h)
    omega
  refine ⟨a, ?_⟩
  rw [← has', w.ord_mul hπw0 hsF0, hπw1, hords, add_zero]

theorem le_ord_of_mem_pow_fiberCenter {w : Place K F} (hw : w.restrict E = v)
    {c : Place.integralClosureAt F v} {n : ℕ} (h : c ∈ (Place.fiberCenter F v hw).asIdeal ^ n)
    (hc0 : (c : F) ≠ 0) : (n : ℤ) ≤ w.ord (c : F) := by
  let φ : Place.integralClosureAt F v →+* w.toValuationSubring :=
    (algebraMap (Place.integralClosureAt F v) F).codRestrict w.toValuationSubring.toSubring
      (Place.forall_mem_of_restrict_eq hw)
  have hle : (Place.fiberCenter F v hw).asIdeal ≤
      (IsLocalRing.maximalIdeal w.toValuationSubring).comap φ := by
    intro d hd
    rw [Ideal.mem_comap]
    by_cases hd0 : d = 0
    · rw [hd0, map_zero]; exact zero_mem _
    have hdF0 : (d : F) ≠ 0 := by
      simpa using (IsFractionRing.injective (Place.integralClosureAt F v) F).ne_iff.mpr hd0
    have hpos := (Place.mem_fiberCenter_iff_ord_pos hw hd0).mp hd
    exact (Place.mem_maximalIdeal_iff_ord_pos w hdF0
      (Place.forall_mem_of_restrict_eq hw d)).mpr hpos
  have h2 : c ∈ ((IsLocalRing.maximalIdeal w.toValuationSubring).comap φ) ^ n :=
    Ideal.pow_right_mono hle n h
  have h3 := Ideal.le_comap_pow φ n h2
  rw [Ideal.mem_comap] at h3
  have h4 : ((φ c : w.toValuationSubring) : F) = (c : F) := rfl
  have h5 := le_ord_of_mem_maximalIdeal_pow w h3 (by rw [h4]; exact hc0)
  rw [h4] at h5
  exact h5

theorem exists_theta [IsAlgClosed K] :
    ∃ θ : Place.integralClosureAt F v, ∃ cst : Place K F → K,
      Set.InjOn cst {w | w.restrict E = v} ∧
      ∀ w : Place K F, w.restrict E = v →
        w.ord ((θ : F) - algebraMap K F (cst w)) = 1 := by
  classical
  set S := v.fiberOver F with hS
  let idx : Place K F → ℕ := fun w => if h : w ∈ S then S.equivFin ⟨w, h⟩ else 0
  let cst : Place K F → K := fun w => Infinite.natEmbedding K (idx w)
  have hinj : Set.InjOn cst {w | w.restrict E = v} := by
    intro w hw w' hw' heq
    have hwS : w ∈ S := (Place.mem_fiberOver v).mpr hw
    have hw'S : w' ∈ S := (Place.mem_fiberOver v).mpr hw'
    have h1 : idx w = idx w' := (Infinite.natEmbedding K).injective heq
    simp only [idx, dif_pos hwS, dif_pos hw'S] at h1
    have h2 := (S.equivFin).injective (Fin.ext h1)
    exact congrArg Subtype.val h2
  let P : Place K F → Ideal (Place.integralClosureAt F v) := fun w =>
    if h : w.restrict E = v then (Place.fiberCenter F v h).asIdeal else ⊤
  have hP : ∀ (w : Place K F) (h : w.restrict E = v), P w = (Place.fiberCenter F v h).asIdeal :=
    fun w h => dif_pos h
  let ϖ : ∀ w : Place K F, w.restrict E = v → Place.integralClosureAt F v :=
    fun w h => (exists_ord_coe_eq_one h).choose
  have hϖ : ∀ (w : Place K F) (h : w.restrict E = v), w.ord (ϖ w h : F) = 1 :=
    fun w h => (exists_ord_coe_eq_one h).choose_spec
  let tgt : S → Place.integralClosureAt F v := fun w =>
    constC v (cst w) + ϖ w (Place.restrict_eq_of_mem_fiberOver v w.2)
  obtain ⟨θ, hθ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) P (fun _ => 2)
    (fun w hw => by
      rw [hP w (Place.restrict_eq_of_mem_fiberOver v hw)]
      exact IsDedekindDomain.HeightOneSpectrum.prime _)
    (fun w hw w' hw' hne heq => by
      apply hne
      rw [hP w (Place.restrict_eq_of_mem_fiberOver v hw),
        hP w' (Place.restrict_eq_of_mem_fiberOver v hw')] at heq
      exact Place.eq_of_fiberCenter_eq _ _ (IsDedekindDomain.HeightOneSpectrum.ext heq))
    tgt
  refine ⟨θ, cst, hinj, fun w hw => ?_⟩
  have hwS : w ∈ S := (Place.mem_fiberOver v).mpr hw
  have h1 := hθ w hwS
  rw [hP w hw] at h1
  have hcoe : ((θ - tgt ⟨w, hwS⟩ : Place.integralClosureAt F v) : F) =
      ((θ : F) - algebraMap K F (cst w)) - (ϖ w hw : F) := by
    simp only [tgt]
    push_cast
    rw [coe_constC]
    ring
  have hϖ0 : (ϖ w hw : F) ≠ 0 := by
    intro h0; have := hϖ w hw; rw [h0, w.ord_zero] at this; exact zero_ne_one this
  by_cases hd0 : ((θ - tgt ⟨w, hwS⟩ : Place.integralClosureAt F v) : F) = 0
  · rw [hcoe, sub_eq_zero] at hd0
    rw [hd0]; exact hϖ w hw
  have h2 := le_ord_of_mem_pow_fiberCenter hw h1 hd0
  rw [hcoe] at h2 hd0
  have hsum : (θ : F) - algebraMap K F (cst w) =
      (ϖ w hw : F) + (((θ : F) - algebraMap K F (cst w)) - (ϖ w hw : F)) := by ring
  rw [hsum, ord_add_eq_of_lt w hϖ0 hd0 (by rw [hϖ w hw]; push_cast at h2; omega)]
  exact hϖ w hw

theorem exists_expansion [IsAlgClosed K] [IsCurveOver K F] (w : Place K F) {ϑ : F}
    (hϑ : w.ord ϑ = 1) :
    ∀ (N : ℕ) (c : F), c ∈ w.toValuationSubring →
      ∃ h : K[X], ∃ m ∈ w.toValuationSubring, c = aeval ϑ h + ϑ ^ N * m := by
  intro N
  induction N with
  | zero => intro c hc; exact ⟨0, c, hc, by simp⟩
  | succ N ih =>
    intro c hc
    obtain ⟨h, m, hm, hc'⟩ := ih c hc
    obtain ⟨a, ha⟩ := exists_sub_algebraMap w hm
    obtain ⟨m', hm', hmm'⟩ := exists_eq_mul_of_ord_pos w hϑ ha
    refine ⟨h + C a * X ^ N, m', hm', ?_⟩
    have : m = algebraMap K F a + ϑ * m' := by rw [← hmm']; ring
    rw [hc', this, map_add, map_mul, aeval_C, map_pow, aeval_X]
    ring

variable [IsAlgClosed K] [IsCurveOver K F]

theorem exists_eq_aeval_add (θ : Place.integralClosureAt F v) (cst : Place K F → K)
    (hinj : Set.InjOn cst {w | w.restrict E = v})
    (hθ : ∀ w : Place K F, w.restrict E = v → w.ord ((θ : F) - algebraMap K F (cst w)) = 1)
    {π₀ : v.toValuationSubring} (hπ₀ : Irreducible π₀) (c : Place.integralClosureAt F v) :
    ∃ g : K[X], ∃ c' : Place.integralClosureAt F v,
      c = aeval θ (g.map (algebraMap K v.toValuationSubring)) +
        algebraMap v.toValuationSubring (Place.integralClosureAt F v) π₀ * c' := by
  classical
  set S := v.fiberOver F with hS
  set πF : F := ((π₀ : E) : F) with hπF
  have hπpos : ∀ w : Place K F, w.restrict E = v → 1 ≤ w.ord πF :=
    fun w hw => one_le_ord_of_irreducible hw hπ₀
  have hπF0 : πF ≠ 0 := by
    have : ((π₀ : E)) ≠ 0 := by
      simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ₀.ne_zero
    simpa [hπF] using this
  let N : Place K F → ℕ := fun w => (w.ord πF).toNat
  have hN : ∀ w : Place K F, w.restrict E = v → ((N w : ℕ) : ℤ) = w.ord πF :=
    fun w hw => Int.toNat_of_nonneg (by have := hπpos w hw; omega)

  have hexp : ∀ w : Place K F, w.restrict E = v → ∃ h : K[X], ∃ m ∈ w.toValuationSubring,
      (c : F) = aeval ((θ : F) - algebraMap K F (cst w)) h +
        ((θ : F) - algebraMap K F (cst w)) ^ N w * m :=
    fun w hw => exists_expansion w (hθ w hw) (N w) c (Place.forall_mem_of_restrict_eq hw c)
  choose hh mm hmm hcm using hexp

  let Q : Place K F → Ideal K[X] := fun w => Ideal.span {X - C (cst w)}
  obtain ⟨g, hg⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) Q N
    (fun w _ => Ideal.prime_span_singleton_iff.mpr (prime_X_sub_C _))
    (fun w hw w' hw' hne heq => by
      apply hne
      apply hinj ((Place.mem_fiberOver v).mp hw) ((Place.mem_fiberOver v).mp hw')
      have hmem : X - C (cst w') ∈ Q w := by rw [heq]; exact Ideal.mem_span_singleton_self _
      have hdvd := Ideal.mem_span_singleton.mp hmem
      have hroot := (dvd_iff_isRoot.mp hdvd)
      simp only [IsRoot.def, eval_sub, eval_X, eval_C, sub_eq_zero] at hroot
      exact hroot)
    (fun w => (hh w.1 (Place.restrict_eq_of_mem_fiberOver v w.2)).comp (X - C (cst w.1)))

  set z : F := ((c : F) - aeval (θ : F) g) * πF⁻¹ with hz
  have hzmem : ∀ w : Place K F, w.restrict E = v → z ∈ w.toValuationSubring := by
    intro w hw
    have hwS : w ∈ S := (Place.mem_fiberOver v).mpr hw
    have h1 := hg w hwS
    simp only [Q, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    obtain ⟨k, hk⟩ := h1
    set ϑ : F := (θ : F) - algebraMap K F (cst w) with hϑ
    have hθmem : (θ : F) ∈ w.toValuationSubring := Place.forall_mem_of_restrict_eq hw θ
    have e1 : aeval (θ : F) g = aeval ϑ (hh w hw) + ϑ ^ N w * aeval (θ : F) k := by
      have := congrArg (aeval (θ : F)) hk
      simp only [map_sub, map_mul, map_pow, aeval_comp, aeval_X, aeval_C] at this
      rw [← hϑ] at this
      linear_combination this
    have e2 : (c : F) - aeval (θ : F) g = ϑ ^ N w * (mm w hw - aeval (θ : F) k) := by
      rw [hcm w hw, e1]; ring
    have hzeq : z = (ϑ ^ N w * πF⁻¹) * (mm w hw - aeval (θ : F) k) := by
      rw [hz, e2]; ring
    rw [hzeq]
    refine mul_mem (mem_of_ord_nonneg w ?_) (sub_mem (hmm w hw) (aeval_mem w hθmem k))
    have hϑ0 : ϑ ≠ 0 := by
      intro h0; have := hθ w hw; rw [← hϑ, h0, w.ord_zero] at this; exact zero_ne_one this
    have hϑ1 : w.ord ϑ = 1 := by rw [hϑ]; exact hθ w hw
    rw [w.ord_mul (pow_ne_zero _ hϑ0) (inv_ne_zero hπF0), w.ord_inv, ← zpow_natCast,
      w.ord_zpow, hϑ1, hN w hw]
    omega
  obtain ⟨c', hc'⟩ := exists_coe_eq_of_forall_mem hzmem
  refine ⟨g, c', ?_⟩
  apply Subtype.ext
  have hcoe1 : ((aeval θ (g.map (algebraMap K v.toValuationSubring)) :
      Place.integralClosureAt F v) : F) = aeval (θ : F) g := by
    rw [← Subalgebra.aeval_coe, aeval_map_algebraMap]
  change (c : F) = ((aeval θ (g.map (algebraMap K v.toValuationSubring)) :
      Place.integralClosureAt F v) : F) +
    ((algebraMap v.toValuationSubring (Place.integralClosureAt F v) π₀ :
      Place.integralClosureAt F v) : F) * (c' : F)
  rw [hcoe1, coe_algebraMap_integralClosureAt, ← hπF, hc', hz]
  field_simp
  ring

theorem adjoin_theta_eq_top (θ : Place.integralClosureAt F v) (cst : Place K F → K)
    (hinj : Set.InjOn cst {w | w.restrict E = v})
    (hθ : ∀ w : Place K F, w.restrict E = v → w.ord ((θ : F) - algebraMap K F (cst w)) = 1) :
    Algebra.adjoin v.toValuationSubring {θ} = ⊤ := by
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ₀mem : π₀ ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.mem_maximalIdeal _).mpr hπ₀.not_isUnit
  set N := Subalgebra.toSubmodule (Algebra.adjoin v.toValuationSubring {θ}) with hNdef
  have hle : (⊤ : Submodule v.toValuationSubring (Place.integralClosureAt F v)) ≤
      N ⊔ (IsLocalRing.maximalIdeal v.toValuationSubring) • ⊤ := by
    intro c _
    obtain ⟨g, c', hc⟩ := exists_eq_aeval_add θ cst hinj hθ hπ₀ c
    rw [hc]
    refine Submodule.add_mem_sup ?_ ?_
    · exact aeval_mem_adjoin_singleton _ θ
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hπ₀mem Submodule.mem_top
  have h := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle
  rw [← Algebra.toSubmodule_eq_top]
  exact top_le_iff.mp h

omit [IsAlgClosed K] [IsCurveOver K F] in

theorem coe_mem_adjoin {θ : Place.integralClosureAt F v}
    (hgen : Algebra.adjoin v.toValuationSubring {θ} = ⊤) (c : Place.integralClosureAt F v) :
    (c : F) ∈ Subalgebra.toSubmodule (Algebra.adjoin v.toValuationSubring {(θ : F)}) := by
  rw [Subalgebra.mem_toSubmodule]
  have h1 : (c : F) ∈ Subalgebra.map (integralClosure v.toValuationSubring F).val
      (Algebra.adjoin v.toValuationSubring {θ}) := by
    rw [hgen]; exact ⟨c, Algebra.mem_top, rfl⟩
  rwa [AlgHom.map_adjoin, Set.image_singleton] at h1

omit [IsAlgClosed K] [IsCurveOver K F] in

theorem adjoin_coe_theta_eq_top {θ : Place.integralClosureAt F v}
    (hgen : Algebra.adjoin v.toValuationSubring {θ} = ⊤) :
    Algebra.adjoin E {(θ : F)} = ⊤ := by
  have halg : IsAlgebraic E (θ : F) := Algebra.IsAlgebraic.isAlgebraic _
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg,
    ← IntermediateField.top_toSubalgebra]
  congr 1
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Place.integralClosureAt F v) z
  have hsub : Algebra.adjoin v.toValuationSubring {(θ : F)} ≤
      (IntermediateField.adjoin E {(θ : F)}).toSubalgebra.restrictScalars v.toValuationSubring :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self E _))
  have ha := hsub (coe_mem_adjoin hgen a)
  have hb' := hsub (coe_mem_adjoin hgen b)
  exact div_mem ha hb'

omit [IsAlgClosed K] [IsCurveOver K F] in

theorem trace_mul_mem_of_mul_derivative_mem {θ : Place.integralClosureAt F v}
    (hgen : Algebra.adjoin v.toValuationSubring {θ} = ⊤) {z : F}
    (hz : z * aeval (θ : F) (derivative (minpoly E (θ : F))) ∈
      Subalgebra.toSubmodule (Algebra.adjoin v.toValuationSubring {(θ : F)}))
    (b : Place.integralClosureAt F v) :
    Algebra.trace E F (z * b) ∈ v.toValuationSubring := by
  have hint : IsIntegral v.toValuationSubring (θ : F) := θ.2
  have htop := adjoin_coe_theta_eq_top hgen
  have hdual := traceForm_dualSubmodule_adjoin v.toValuationSubring E htop hint
  set f' : F := aeval (θ : F) (derivative (minpoly E (θ : F))) with hf'
  have hf'0 : f' ≠ 0 :=
    (Algebra.IsSeparable.isSeparable E (θ : F)).aeval_derivative_ne_zero (minpoly.aeval E _)
  have hzmem : z ∈ (Algebra.traceForm E F).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin v.toValuationSubring {(θ : F)})) := by
    rw [hdual, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨z * f', hz, by rw [smul_eq_mul, mul_comm, mul_assoc, mul_inv_cancel₀ hf'0, mul_one]⟩
  have h1 := (LinearMap.BilinForm.mem_dualSubmodule _).mp hzmem (b : F) (coe_mem_adjoin hgen b)
  rw [Algebra.traceForm_apply] at h1
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
  rw [← ha]
  exact a.2

end Fibre

section DerivativeIdentity

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
variable [Algebra.EssFiniteType K F]
variable {E : IntermediateField K F} [FiniteDimensional E F] [Algebra.IsSeparable E F]
variable {v : Place K E}

theorem mul_aeval_derivative_mem (x₀ : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (δ : Derivation K F F) (ω₀ : Ω[F⁄K]) (hδ : ∀ z : F, D K F z = δ z • ω₀)
    (hE : ∀ w : Place K F, w.restrict E = v → ∀ a : E,
      (a : F) ∈ w.toValuationSubring → δ a ∈ w.toValuationSubring)
    {θ : Place.integralClosureAt F v} {cst : Place K F → K}
    (hθ : ∀ w : Place K F, w.restrict E = v → w.ord ((θ : F) - algebraMap K F (cst w)) = 1)
    {x : F} (hx : ∀ w : Place K F, w.restrict E = v →
      ∃ g ∈ w.toValuationSubring, x • ω₀ = g • w.dCoord)
    {w : Place K F} (hw : w.restrict E = v) :
    x * aeval (θ : F) (derivative (minpoly E (θ : F))) ∈ w.toValuationSubring := by
  obtain ⟨π, hπ1, hdc⟩ := w.exists_ord_eq_one_and_dCoord_eq
  have hθmem : (θ : F) ∈ w.toValuationSubring := Place.forall_mem_of_restrict_eq hw θ
  have hint : IsIntegral v.toValuationSubring (θ : F) := θ.2

  set q := minpoly v.toValuationSubring (θ : F) with hqdef
  have hq : minpoly E (θ : F) = q.map (algebraMap v.toValuationSubring E) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' E hint
  set p : F[X] := (minpoly E (θ : F)).map (algebraMap E F) with hp
  have hp' : p = q.map (algebraMap v.toValuationSubring F) := by
    rw [hp, hq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hpeval : p.eval (θ : F) = 0 := by rw [hp, eval_map, ← aeval_def, minpoly.aeval]
  have hpderiv : (derivative p).eval (θ : F) = aeval (θ : F) (derivative (minpoly E (θ : F))) := by
    rw [hp, derivative_map, eval_map, ← aeval_def]
  have hcoeff : ∀ i, δ (p.coeff i) ∈ w.toValuationSubring := by
    intro i
    rw [hp', coeff_map, algebraMap_valuationSubring_apply]
    exact hE w hw (q.coeff i : E) ((mem_valuationSubring_iff hw _).mp (q.coeff i).2)

  have hid := derivation_eval δ p (θ : F)
  rw [hpeval, map_zero, hpderiv] at hid
  set f' := aeval (θ : F) (derivative (minpoly E (θ : F))) with hf'
  have hr : p.sum (fun i a => δ a * (θ : F) ^ i) ∈ w.toValuationSubring := by
    rw [Polynomial.sum_def]
    exact sum_mem fun i _ => mul_mem (hcoeff i) (pow_mem hθmem i)
  set r := p.sum (fun i a => δ a * (θ : F) ^ i) with hrdef
  have hfr : f' * δ (θ : F) = -r := by linear_combination -hid

  have hμ := ord_diffCoeff_eq_zero_of_ord_eq_one x₀ hπ1 hdc (hθ w hw)
  rw [diffCoeff_sub_algebraMap hdc] at hμ
  obtain ⟨hμ0, hμne⟩ := hμ
  set μ := Place.diffCoeff π (D K F (θ : F)) with hμdef
  have hDθ : D K F (θ : F) = μ • D K F π := D_eq_diffCoeff_smul hdc _
  obtain ⟨g, hg, hxg⟩ := hx w hw

  have hkey : x * μ = δ (θ : F) * g := by
    apply coeff_unique hdc
    calc (x * μ) • D K F π = x • D K F (θ : F) := by rw [hDθ, smul_smul]
      _ = δ (θ : F) • (x • ω₀) := by rw [hδ (θ : F), smul_smul, smul_smul, mul_comm]
      _ = (δ (θ : F) * g) • D K F π := by rw [hxg, hdc, smul_smul]

  have hxf : x * f' = -(g * r) * μ⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hμne]
    calc x * f' * μ = f' * (x * μ) := by ring
      _ = f' * (δ (θ : F) * g) := by rw [hkey]
      _ = (f' * δ (θ : F)) * g := by ring
      _ = -(g * r) := by rw [hfr]; ring
  rw [hxf]
  exact mul_mem (neg_mem (mul_mem hg hr)) (inv_mem_of_ord_eq_zero w hμ0)

end DerivativeIdentity

section Main

open scoped IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]

theorem main (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    (x : F)
    (hx : ∀ w : Place K F, 0 ≤ w.ord t →
      ∃ g ∈ w.toValuationSubring, x • D K F t = g • w.dCoord)
    (b : F) (hb : IsIntegral (Algebra.adjoin K ({t} : Set F)) b) :
    ∃ P : K[X],
      ((Algebra.trace (IntermediateField.adjoin K ({t} : Set F)) F (x * b) :
          IntermediateField.adjoin K ({t} : Set F)) : F) = aeval t P := by
  by_cases hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F
  swap
  · refine ⟨0, ?_⟩
    rw [Algebra.trace_eq_zero_of_not_isSeparable hsep, LinearMap.zero_apply, map_zero]
    rfl
  haveI : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional ht inferInstance
  have hDt0 : D K F t ≠ 0 := D_ne_zero_of_transcendental K t ht
  obtain ⟨δ, hδ⟩ := exists_derivation_of_span_eq_top hDt0
    (span_D_eq_top_of_transcendental K t ht)
  have hδt : δ t = 1 := by
    have h : (δ t) • D K F t = (1 : F) • D K F t := by rw [one_smul, ← hδ t]
    exact smul_left_injective F hDt0 h
  have htE : t ∈ IntermediateField.adjoin K ({t} : Set F) :=
    IntermediateField.mem_adjoin_simple_self K t
  refine exists_eq_aeval_of_forall_mem ht (SetLike.coe_mem _) fun w hwt => ?_
  set v : Place K (IntermediateField.adjoin K ({t} : Set F)) :=
    w.restrict (IntermediateField.adjoin K ({t} : Set F)) with hv
  have hwv : w.restrict (IntermediateField.adjoin K ({t} : Set F)) = v := rfl
  have htw : t ∈ w.toValuationSubring := mem_of_ord_nonneg w hwt

  have htw' : ∀ w' : Place K F, w'.restrict (IntermediateField.adjoin K ({t} : Set F)) = v →
      t ∈ w'.toValuationSubring := by
    intro w' hw'
    have h1 : (⟨t, htE⟩ : IntermediateField.adjoin K ({t} : Set F)) ∈ v.toValuationSubring :=
      (mem_valuationSubring_iff hwv ⟨t, htE⟩).mpr htw
    exact (mem_valuationSubring_iff hw' ⟨t, htE⟩).mp h1

  have hc : ∀ w' : Place K F, w'.restrict (IntermediateField.adjoin K ({t} : Set F)) = v →
      ∃ c : K, 0 < w'.ord (t - algebraMap K F c) := by
    intro w' hw'
    obtain ⟨c, hc⟩ := exists_sub_algebraMap w' (htw' w' hw')
    rcases hc with h0 | h1
    · exfalso; apply ht; rw [sub_eq_zero.mp h0]; exact isAlgebraic_algebraMap c
    · exact ⟨c, by omega⟩

  obtain ⟨θ, cst, hinj, hθ⟩ := exists_theta (F := F) (v := v)
  have hgen := adjoin_theta_eq_top θ cst hinj hθ

  have hbint : IsIntegral v.toValuationSubring b := by
    have hAE : ∀ a : F, a ∈ Algebra.adjoin K ({t} : Set F) →
        a ∈ IntermediateField.adjoin K ({t} : Set F) :=
      fun a ha => IntermediateField.algebra_adjoin_le_adjoin K _ ha
    have hAO : ∀ a : F, a ∈ Algebra.adjoin K ({t} : Set F) → a ∈ w.toValuationSubring :=
      fun a ha => (Algebra.adjoin_le (S := subalg w) (Set.singleton_subset_iff.mpr htw)) ha
    let φ : Algebra.adjoin K ({t} : Set F) →+* v.toValuationSubring :=
      { toFun := fun a => ⟨⟨a, hAE a a.2⟩, (mem_valuationSubring_iff hwv _).mpr (hAO a a.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    obtain ⟨p, hpm, hp0⟩ := hb
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [eval₂_map]
    exact hp0

  have hmem := trace_mul_mem_of_mul_derivative_mem hgen (z := x) ?_
    ⟨b, (mem_integralClosure_iff _ _).mpr hbint⟩
  · exact (mem_valuationSubring_iff hwv _).mp hmem
  have hxf : ∀ w' : Place K F, w'.restrict (IntermediateField.adjoin K ({t} : Set F)) = v →
      x * aeval (θ : F) (derivative (minpoly (IntermediateField.adjoin K ({t} : Set F)) (θ : F)))
        ∈ w'.toValuationSubring := by
    intro w' hw'
    refine mul_aeval_derivative_mem t δ (D K F t) hδ ?_ hθ ?_ hw'
    · intro w'' hw'' a ha
      obtain ⟨c, hc⟩ := hc w'' hw''
      exact derivation_mem_of_mem_adjoin δ ht hδt w'' hc a.2 ha
    · intro w'' hw''
      exact hx w'' (ord_nonneg_of_mem w'' (htw' w'' hw''))
  obtain ⟨c, hc⟩ := exists_coe_eq_of_forall_mem hxf
  rw [← hc]
  exact coe_mem_adjoin hgen c

end Main

end AlgebraicCurve.DedekindTraceProof
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord.AlgebraicCurve.DedekindTraceProof"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord.AlgebraicCurve in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [AlgebraicCurve.IsCurveOver K F]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    (x : F)
    (hx : ∀ w : AlgebraicCurve.Place K F, 0 ≤ w.ord t →
      ∃ g ∈ w.toValuationSubring, x • KaehlerDifferential.D K F t = g • w.dCoord)
    (b : F) (hb : IsIntegral (Algebra.adjoin K ({t} : Set F)) b) :
    ∃ P : Polynomial K,
      ((Algebra.trace (IntermediateField.adjoin K ({t} : Set F)) F (x * b) :
          IntermediateField.adjoin K ({t} : Set F)) : F) = Polynomial.aeval t P :=
  AlgebraicCurve.DedekindTraceProof.main t ht x hx b hb

end
end S_AlgebraicCurve_exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord
end P2MW
export P2MW.S_AlgebraicCurve_exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord (solution)
