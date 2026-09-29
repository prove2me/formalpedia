-- Prove2me | solution 1 for AlgebraicCurve.Annulus.exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/adb920bb-67a3-5237-81bc-902afc192512

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_eq_evalAt_residue_of_isAttached_both_ends
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord_zero Place.ord_inv HasPrincipalDivisors Place.ord_algebraMap Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends Annulus.residue_evalAt_eq_evalAt_residue_of_isAttached_both_ends"
p2m_open "AlgebraicCurve"

open IsLocalRing

section IsometryHelpers

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField ord ord_zero ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt ord_algebraMap" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.exists_isUnit_of_ord_eq_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ hm : f ∈ v.toValuationSubring, IsUnit (⟨f, hm⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  subst hu
  exact ⟨(u : v.toValuationSubring).2, u.isUnit⟩

end Place
p2m_export "AlgebraicCurve" "Place.exists_isUnit_of_ord_eq_zero_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

end Place
p2m_export "AlgebraicCurve" "Place.ord_nonneg_of_mem_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

end Place
p2m_export "AlgebraicCurve" "Place.mem_of_ord_nonneg_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_mul_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_mul_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_sub_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_sub_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap_G {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_algebraMap_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_evalAt_ne_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  have h0 : 0 ≤ v.ord f := v.ord_nonneg_of_mem_G hf
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne h0 (Ne.symm hne)
  apply h
  have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have : v.ord f = 0 := by
      have := v.ord_coe_unit u
      rwa [hu] at this
    omega
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

end Place
p2m_export "AlgebraicCurve" "Place.ord_eq_zero_of_evalAt_ne_zero_G"
p2m_open_scoped "AlgebraicCurve.Place" in

theorem Place.ord_pos_of_evalAt_eq_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.evalAt f = 0) :
    0 < v.ord f := by
  have h0 := v.ord_nonneg_of_mem_G hf
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero_G hf0 heq.symm
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hm⟩ ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu
    apply hres
    rw [← v.algebraMap_evalAt hv hm, h, map_zero]

namespace ComponentChart p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff residue residue_algebraMap ker_residue dom" end ComponentChart
namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.isUnit_of_residue_ne_zero_G
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]; exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.isUnit_of_residue_ne_zero_G"

theorem inv_mem_of_isUnit_G {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
    (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (u : O) = 0 := by rw [hu]; rfl
    exact u.ne_zero this
  have hval : ((u⁻¹ : Oˣ) : O).1 = x⁻¹ := by
    have h1 := congrArg (fun t : O => (t : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  exact hval ▸ ((u⁻¹ : Oˣ) : O).2

namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.residue_inv_G
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl; apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.residue_inv_G"
namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.residue_algebraMap_eq_zero_G
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (h : algebraMap L F a ∈ C.integers) : C.residue ⟨algebraMap L F a, h⟩ = 0 := by
  have e1 : (⟨algebraMap L F a, h⟩ : C.integers) = ⟨algebraMap L F a, (C.algebraMap_mem_iff a).mpr a.2⟩ := rfl
  rw [e1, C.residue_algebraMap a, (IsLocalRing.residue_eq_zero_iff _).2 ha, map_zero]

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.residue_algebraMap_eq_zero_G"

theorem abv_lt_one_of_mem_maximalIdeal_G {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    {m : ↥A} (hm : m ∈ IsLocalRing.maximalIdeal ↥A) : μ (m : L) < 1 := by
  have hle : μ (m : L) ≤ 1 := (hμA _).1 m.2
  refine lt_of_le_of_ne hle fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have hm0 : (m : L) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  have hinv : (m : L)⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hm0)⟩

theorem mem_maximalIdeal_of_abv_lt_one_G {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    {x : L} (hx : x ∈ A) (h : μ x < 1) : (⟨x, hx⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    intro h0
    have : (u : ↥A) = 0 := by rw [hu]; exact Subtype.ext h0
    exact u.ne_zero this
  have hinv : ((u⁻¹ : (↥A)ˣ) : ↥A).1 = x⁻¹ := by
    have h1 := congrArg (fun t : ↥A => (t : L)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hxinv : μ x⁻¹ ≤ 1 := (hμA _).1 (hinv ▸ ((u⁻¹ : (↥A)ˣ) : ↥A).2)
  rw [map_inv₀] at hxinv
  have : 1 < (μ x)⁻¹ := (one_lt_inv₀ (μ.pos hx0)).2 h
  linarith

theorem residue_ne_zero_of_abv_eq_one_G {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    {x : L} (hx : x ∈ A) (h : μ x = 1) : IsLocalRing.residue ↥A ⟨x, hx⟩ ≠ 0 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit]
  have hx0 : x ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hinv : x⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.evalAt_add_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

namespace Annulus p2m_export "AlgebraicCurve.Annulus" "IsAttached existsUnique_evalAt_eq modulus modulus_mem dom mem_dom param ord_param_sub sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends residue_evalAt_eq_evalAt_residue_of_isAttached_both_ends" end Annulus
p2m_open_scoped "AlgebraicCurve.Annulus" in

theorem Annulus.exists_mem_dom_abv_evalAt_param_ne_G {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param) := by
  set π : L := (An.modulus : L) with hπ
  have hμπ0 : 0 < μ π := μ.pos hmod0
  have hμπ1 : μ π < 1 := abv_lt_one_of_mem_maximalIdeal_G μ hμA An.modulus_mem
  obtain ⟨c₂, hc₂⟩ := IsAlgClosed.exists_pow_nat_eq π (by norm_num : 0 < 2)
  obtain ⟨c₃, hc₃⟩ := IsAlgClosed.exists_pow_nat_eq π (by norm_num : 0 < 3)
  have hμc₂ : μ c₂ ^ 2 = μ π := by rw [← map_pow, hc₂]
  have hμc₃ : μ c₃ ^ 3 = μ π := by rw [← map_pow, hc₃]
  have hc₂0 : c₂ ≠ 0 := by rintro rfl; apply hmod0; rw [← hc₂]; norm_num
  have hc₃0 : c₃ ≠ 0 := by rintro rfl; apply hmod0; rw [← hc₃]; norm_num
  have hμc₂1 : μ c₂ < 1 := by
    by_contra h; push Not at h
    have : 1 ≤ μ c₂ ^ 2 := one_le_pow₀ h
    linarith
  have hμc₃1 : μ c₃ < 1 := by
    by_contra h; push Not at h
    have : 1 ≤ μ c₃ ^ 3 := one_le_pow₀ h
    linarith
  have hc₂A : c₂ ∈ A := (hμA _).2 hμc₂1.le
  have hc₃A : c₃ ∈ A := (hμA _).2 hμc₃1.le
  have hc₂𝔪 := mem_maximalIdeal_of_abv_lt_one_G μ hμA hc₂A hμc₂1
  have hc₃𝔪 := mem_maximalIdeal_of_abv_lt_one_G μ hμA hc₃A hμc₃1
  have hc₃sqA : c₃ ^ 2 ∈ A := pow_mem hc₃A 2
  have hc₃sq𝔪 : (⟨c₃ ^ 2, hc₃sqA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have e1 : (⟨c₃ ^ 2, hc₃sqA⟩ : ↥A) = (⟨c₃, hc₃A⟩ : ↥A) ^ 2 := Subtype.ext (by simp)
    rw [e1]; exact Ideal.pow_mem_of_mem _ hc₃𝔪 2 (by norm_num)
  obtain ⟨Q₂, ⟨hQ₂, hzQ₂⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₂, hc₂A⟩ hc₂𝔪 hc₂0
    ⟨⟨c₂, hc₂A⟩, hc₂𝔪, by rw [← hπ, ← hc₂]; ring⟩
  obtain ⟨Q₃, ⟨hQ₃, hzQ₃⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₃, hc₃A⟩ hc₃𝔪 hc₃0
    ⟨⟨c₃ ^ 2, hc₃sqA⟩, hc₃sq𝔪, by rw [← hπ, ← hc₃]; ring⟩
  refine ⟨Q₂, hQ₂, Q₃, hQ₃, ?_⟩
  rw [hzQ₂, hzQ₃]
  show μ c₂ ≠ μ c₃
  intro heq
  have h0 : 0 < μ c₂ := μ.pos hc₂0
  have h23 : μ c₂ ^ 2 = μ c₂ ^ 3 := by rw [hμc₂, ← hμc₃, heq]
  have : μ c₂ ^ 2 * (1 - μ c₂) = 0 := by ring_nf; linarith [h23]
  rcases mul_eq_zero.1 this with h | h
  · exact (pow_pos h0 2).ne' h
  · exact hμc₂1.ne (by linarith)

end IsometryHelpers

end AlgebraicCurve

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x) (hx : x.IsRational)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x') (hx' : x'.IsRational)
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0) (hord : x.ord (C.residue ⟨h, hC⟩) = 1)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hord' : x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) = 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h)
    (hz : An.param ∈ C.integers) :
    ∃ Q ∈ An.dom, Q.ord h = 1 ∧ (∀ P ∈ An.dom, P ≠ Q → P.ord h = 0) ∧
      μ (Q.evalAt An.param) = μ c' ∧
      (∃ hq : Q.evalAt An.param * c'⁻¹ ∈ A, IsUnit (⟨_, hq⟩ : A) ∧
        IsLocalRing.residue A ⟨_, hq⟩
          = -(x'.evalAt (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩))
              * (x.evalAt (C.residue ⟨h, hC⟩ * (C.residue ⟨An.param, hz⟩)⁻¹))⁻¹) ∧
      ∀ R ∈ An.dom,
        ∃ hu : R.evalAt (h * (An.param - algebraMap L F (Q.evalAt An.param))⁻¹) ∈ A,
          IsUnit (⟨_, hu⟩ : A) ∧
          IsLocalRing.residue A ⟨_, hu⟩ = x.evalAt (C.residue ⟨h, hC⟩ * (C.residue ⟨An.param, hz⟩)⁻¹) := by
  classical
  obtain ⟨-, hzC, hzord, -⟩ := id hatt
  obtain ⟨-, hz'C', hz'ord, -⟩ := id hatt'
  set z := An.param with hz_def
  set z' := An'.param with hz'_def
  set π : L := (An.modulus : L) with hπ
  have hzord1 : x.ord (C.residue ⟨z, hz⟩) = 1 := hzord
  have hzres0 : C.residue ⟨z, hz⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hzord1; exact zero_ne_one hzord1
  have hz'res0 : C'.residue ⟨z', hz'C'⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hz'ord; exact zero_ne_one hz'ord
  have hz0 : z ≠ 0 := by
    intro h0; apply hzres0
    have : (⟨z, hz⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hz'0 : z' ≠ 0 := by
    intro h0; apply hz'res0
    have : (⟨z', hz'C'⟩ : C'.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hh0 : h ≠ 0 := by
    intro h0; apply hres
    have : (⟨h, hC⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hμπ0 : 0 < μ π := μ.pos hmod0
  have hPi : algebraMap L F π ≠ 0 := (map_ne_zero _).2 hmod0

  have hdomR : ∀ R ∈ An.dom,
      R.IsRational ∧ z ∈ R.toValuationSubring ∧ z' ∈ R.toValuationSubring ∧
      R.evalAt z ∈ A ∧ R.evalAt z ≠ 0 ∧ R.evalAt z' ≠ 0 ∧ R.evalAt z' * R.evalAt z = π ∧
      μ (R.evalAt z) < 1 ∧ ∃ m : ↥A, m ∈ IsLocalRing.maximalIdeal ↥A ∧ π = R.evalAt z * m := by
    intro R hR
    obtain ⟨hrat, hzR, ⟨hzA, hz𝔪⟩, hzR0, m, hm𝔪, hm⟩ := An.mem_dom R hR
    obtain ⟨-, hz'R, -, hz'R0, -⟩ := An'.mem_dom R (hdom ▸ hR)
    have hprod : R.evalAt z' * R.evalAt z = π := by
      rw [← R.evalAt_mul_G hrat hz'R hzR, htwo, R.evalAt_algebraMap_G]
    exact ⟨hrat, hzR, hz'R, hzA, hzR0, hz'R0, hprod, abv_lt_one_of_mem_maximalIdeal_G μ hμA hz𝔪, m, hm𝔪, hm⟩
  have hinj : ∀ R ∈ An.dom, ∀ R' ∈ An.dom, R.evalAt z = R'.evalAt z → R = R' := by
    intro R hR R' hR' hRR'
    obtain ⟨-, -, ⟨haA, ha𝔪⟩, ha0, hm⟩ := An.mem_dom R' hR'
    obtain ⟨P₀, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨R'.evalAt z, haA⟩ ha𝔪 ha0 hm
    exact (huniq R ⟨hR, hRR'⟩).trans (huniq R' ⟨hR', rfl⟩).symm

  have hwide' : ∃ Q₁ ∈ An'.dom, ∃ Q₂ ∈ An'.dom, μ (Q₁.evalAt An'.param) ≠ μ (Q₂.evalAt An'.param) := by
    obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := hwide
    refine ⟨Q₁, hdom ▸ hQ₁, Q₂, hdom ▸ hQ₂, ?_⟩
    have key : ∀ R ∈ An.dom, μ (R.evalAt An'.param) * μ (R.evalAt z) = μ π := by
      intro R hR
      obtain ⟨-, -, -, -, -, -, hp, -⟩ := hdomR R hR
      rw [← map_mul]; exact congrArg μ hp
    intro heq; apply hne
    have h1 := key Q₁ hQ₁
    have h2 := key Q₂ hQ₂
    rw [heq] at h1
    have h12 := h1.trans h2.symm
    have hne0 : μ (Q₂.evalAt An'.param) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h2; exact hμπ0.ne h2
    exact mul_left_cancel₀ hne0 h12

  obtain ⟨D, hD0, hDsupp, hDord, hdeg, hsum⟩ :=
    AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
      An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide h hC hres c' hc'0 hc'A hC' hres' hpole
  rw [hord, hord'] at hdeg
  rw [hord'] at hsum
  have hsupp : D.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hemp
    have : (D.sum fun _ m => m) = 0 := by rw [Finsupp.sum, hemp, Finset.sum_empty]
    omega
  obtain ⟨Q, hQsupp⟩ := hsupp
  have hDQ0 : D Q ≠ 0 := Finsupp.mem_support_iff.1 hQsupp
  have hQdom : Q ∈ An.dom := hDsupp Q hDQ0
  have hsplit : (D.sum fun _ m => m) = D Q + ∑ Q' ∈ D.support.erase Q, D Q' := by
    rw [Finsupp.sum, ← Finset.add_sum_erase _ _ hQsupp]
  have hrest0 : 0 ≤ ∑ Q' ∈ D.support.erase Q, D Q' := Finset.sum_nonneg fun Q' _ => hD0 Q'
  have hDQ1 : D Q = 1 := by have := hD0 Q; omega
  have hrest : ∑ Q' ∈ D.support.erase Q, D Q' = 0 := by omega
  have hothers : ∀ Q' ∈ D.support.erase Q, D Q' = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun Q' _ => hD0 Q').1 hrest
  have hD_other : ∀ P, P ≠ Q → D P = 0 := by
    intro P hP
    by_cases hPs : P ∈ D.support
    · exact hothers P (Finset.mem_erase.2 ⟨hP, hPs⟩)
    · exact Finsupp.notMem_support_iff.1 hPs
  have hordQ : Q.ord h = 1 := by rw [← hDord Q hQdom, hDQ1]
  have hordP : ∀ P ∈ An.dom, P ≠ Q → P.ord h = 0 := fun P hP hPQ => by rw [← hDord P hP, hD_other P hPQ]
  have hDsingle : D = Finsupp.single Q 1 := by
    ext P
    by_cases hPQ : P = Q
    · subst hPQ; rw [Finsupp.single_eq_same]; exact hDQ1
    · rw [Finsupp.single_eq_of_ne hPQ]; exact hD_other P hPQ
  obtain ⟨hQrat, hzQ, hz'Q, haA, ha0, hb0, hprodQ, hμa1, m, hm𝔪, hπam⟩ := hdomR Q hQdom
  set a : L := Q.evalAt z with ha_def
  have hμa : μ a = μ c' := by
    rw [hDsingle, Finsupp.sum_single_index (by simp)] at hsum
    simp only [Int.cast_one, one_mul, Int.cast_zero, zero_mul, add_zero] at hsum
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (μ.pos ha0)) (Set.mem_Ioi.2 (μ.pos hc'0)) hsum

  have ha𝔪 : (⟨a, haA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := mem_maximalIdeal_of_abv_lt_one_G μ hμA haA hμa1
  set Ca := algebraMap L F a with hCa
  set g : F := z - Ca with hg
  have hCaC : Ca ∈ C.integers := (C.algebraMap_mem_iff a).2 haA
  have hCares : C.residue ⟨Ca, hCaC⟩ = 0 := C.residue_algebraMap_eq_zero_G ⟨a, haA⟩ ha𝔪 hCaC
  have hgC : g ∈ C.integers := sub_mem hz hCaC
  have hgres : C.residue ⟨g, hgC⟩ = C.residue ⟨z, hz⟩ := by
    have e1 : (⟨g, hgC⟩ : C.integers) = ⟨z, hz⟩ - ⟨Ca, hCaC⟩ := Subtype.ext rfl
    rw [e1, map_sub, hCares, sub_zero]
  have hgres0 : C.residue ⟨g, hgC⟩ ≠ 0 := by rw [hgres]; exact hzres0
  have hg0 : g ≠ 0 := by
    intro h0; apply hgres0
    have : (⟨g, hgC⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hginv : g⁻¹ ∈ C.integers := inv_mem_of_isUnit_G hgC (C.isUnit_of_residue_ne_zero_G hgC hgres0)
  set f : F := h * (An.param - algebraMap L F (Q.evalAt An.param))⁻¹ with hf
  have hfg : f = h * g⁻¹ := rfl
  have hfC : f ∈ C.integers := mul_mem hC hginv
  have hfres : C.residue ⟨f, hfC⟩ = C.residue ⟨h, hC⟩ * (C.residue ⟨z, hz⟩)⁻¹ := by
    have e1 : (⟨f, hfC⟩ : C.integers) = ⟨h, hC⟩ * ⟨g⁻¹, hginv⟩ := Subtype.ext rfl
    rw [e1, map_mul, C.residue_inv_G hgC hgres0 hginv, hgres]
  have hfres0 : C.residue ⟨f, hfC⟩ ≠ 0 := by rw [hfres]; exact mul_ne_zero hres (inv_ne_zero hzres0)
  have hford : x.ord (C.residue ⟨f, hfC⟩) = 0 := by
    rw [hfres, x.ord_mul hres (inv_ne_zero hzres0), Place.ord_inv, hord, hzord1]; ring
  have hf0 : f ≠ 0 := by rw [hfg]; exact mul_ne_zero hh0 (inv_ne_zero hg0)

  have hz'inv : z'⁻¹ ∈ C'.integers := inv_mem_of_isUnit_G hz'C' (C'.isUnit_of_residue_ne_zero_G hz'C' hz'res0)
  have hCmC' : algebraMap L F (m : L) ∈ C'.integers := (C'.algebraMap_mem_iff _).2 m.2
  have hCmres : C'.residue ⟨_, hCmC'⟩ = 0 := by
    have := C'.residue_algebraMap_eq_zero_G m hm𝔪 hCmC'
    exact this
  have hna0 : (-a) ≠ 0 := neg_ne_zero.2 ha0
  have hz_eq : z = algebraMap L F π * z'⁻¹ := by
    rw [← htwo, mul_comm z' z, mul_inv_cancel_right₀ hz'0]
  have keyg : (algebraMap L F (-a))⁻¹ * g = 1 - algebraMap L F (m : L) * z'⁻¹ := by
    have haL : algebraMap L F a ≠ 0 := (map_ne_zero _).2 ha0
    rw [hg, hCa, hz_eq, hπam, map_mul, map_neg]
    first | (field_simp; done) | (field_simp; ring)
  have hgC' : (algebraMap L F (-a))⁻¹ * g ∈ C'.integers := by
    rw [keyg]; exact sub_mem (one_mem _) (mul_mem hCmC' hz'inv)
  have hgres' : C'.residue ⟨_, hgC'⟩ = 1 := by
    have e1 : (⟨_, hgC'⟩ : C'.integers) = 1 - ⟨_, hCmC'⟩ * ⟨z'⁻¹, hz'inv⟩ := Subtype.ext keyg
    rw [e1, map_sub, map_one, map_mul, hCmres, zero_mul, sub_zero]
  have hgC'unit : IsUnit (⟨_, hgC'⟩ : C'.integers) :=
    C'.isUnit_of_residue_ne_zero_G hgC' (by rw [hgres']; exact one_ne_zero)
  have hg'0 : (algebraMap L F (-a))⁻¹ * g ≠ 0 := mul_ne_zero (inv_ne_zero ((map_ne_zero _).2 hna0)) hg0
  have hg'inv : ((algebraMap L F (-a))⁻¹ * g)⁻¹ ∈ C'.integers := inv_mem_of_isUnit_G hgC' hgC'unit

  set κ : L := c' * (-a)⁻¹ with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero hc'0 (inv_ne_zero hna0)
  have hμκ : μ κ = 1 := by
    rw [hκ, map_mul, map_inv₀, AbsoluteValue.map_neg, hμa, mul_inv_cancel₀ (μ.pos hc'0).ne']
  have keyf : (algebraMap L F κ)⁻¹ * f = ((algebraMap L F c')⁻¹ * h) * ((algebraMap L F (-a))⁻¹ * g)⁻¹ := by
    rw [hfg, hκ, map_mul, map_inv₀]
    have h1 : algebraMap L F c' ≠ 0 := (map_ne_zero _).2 hc'0
    have h2 : algebraMap L F (-a) ≠ 0 := (map_ne_zero _).2 hna0
    field_simp
  have hfC' : (algebraMap L F κ)⁻¹ * f ∈ C'.integers := by rw [keyf]; exact mul_mem hC' hg'inv
  have hfres' : C'.residue ⟨_, hfC'⟩ = C'.residue ⟨_, hC'⟩ := by
    have e1 : (⟨_, hfC'⟩ : C'.integers) = ⟨_, hC'⟩ * ⟨_, hg'inv⟩ := Subtype.ext keyf
    rw [e1, map_mul, C'.residue_inv_G hgC' (by rw [hgres']; exact one_ne_zero) hg'inv, hgres', inv_one, mul_one]
  have hfres'0 : C'.residue ⟨_, hfC'⟩ ≠ 0 := by rw [hfres']; exact hres'
  have hford' : x'.ord (C'.residue ⟨_, hfC'⟩) = 0 := by rw [hfres']; exact hord'

  have hordg : ∀ R ∈ An.dom, R.ord g = (if R = Q then 1 else 0) := by
    intro R hR
    obtain ⟨hRrat, hzR, -⟩ := hdomR R hR
    by_cases hRQ : R = Q
    · subst hRQ; rw [if_pos rfl, hg, hCa, ha_def]; exact An.ord_param_sub R hR
    · rw [if_neg hRQ]
      apply R.ord_eq_zero_of_evalAt_ne_zero_G (sub_mem hzR (R.algebraMap_mem' a))
      rw [R.evalAt_sub_G hRrat hzR (R.algebraMap_mem' a), R.evalAt_algebraMap_G, ha_def, sub_ne_zero]
      exact fun h1 => hRQ (hinj R hR Q hQdom h1)
  have hfpole : ∀ R ∈ An.dom, 0 ≤ R.ord f := by
    intro R hR
    rw [hfg, R.ord_mul hh0 (inv_ne_zero hg0), Place.ord_inv, hordg R hR]
    by_cases hRQ : R = Q
    · subst hRQ; rw [if_pos rfl, hordQ]; omega
    · rw [if_neg hRQ, hordP R hR hRQ]; omega

  obtain ⟨-, -, hc⟩ := AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends μ hμA
    An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide f hfC hfres0 κ hκ0 ((hμA κ).2 hμκ.le) hfC' hfres'0 hfpole
  have hunit : ∀ R ∈ An.dom, R.ord f = 0 ∧ μ (R.evalAt f) = 1 := hc ⟨hμκ, hford, hford'⟩
  have hnear := AlgebraicCurve.Annulus.residue_evalAt_eq_evalAt_residue_of_isAttached_both_ends μ hμA
    An An' hdom hmod hmod0 htwo C x hatt hx C' x' hatt' hwide f hfpole hfC hfres0 κ hμκ hfC' hfres'0

  have hff : (algebraMap L F κ⁻¹)⁻¹ * ((algebraMap L F κ)⁻¹ * f) = f := by
    rw [map_inv₀, inv_inv, ← mul_assoc, mul_inv_cancel₀ ((map_ne_zero _).2 hκ0), one_mul f]
  have hfC'' : (algebraMap L F κ⁻¹)⁻¹ * ((algebraMap L F κ)⁻¹ * f) ∈ C.integers := by rw [hff]; exact hfC
  have e1f : (⟨_, hfC''⟩ : C.integers) = ⟨f, hfC⟩ := Subtype.ext hff
  have hfpole' : ∀ R ∈ An'.dom, 0 ≤ R.ord ((algebraMap L F κ)⁻¹ * f) := by
    intro R hR
    rw [R.ord_mul (inv_ne_zero ((map_ne_zero _).2 hκ0)) hf0, Place.ord_inv, Place.ord_algebraMap, neg_zero, zero_add]
    exact hfpole R (hdom ▸ hR)
  have hfar := AlgebraicCurve.Annulus.residue_evalAt_eq_evalAt_residue_of_isAttached_both_ends μ hμA
    An' An hdom.symm hmod.symm (by rw [hmod]; exact hmod0) (by rw [mul_comm, htwo, hmod]) C' x' hatt' hx' C x hatt hwide'
    ((algebraMap L F κ)⁻¹ * f) hfpole' hfC' hfres'0 κ⁻¹ (by rw [map_inv₀, hμκ, inv_one]) hfC''
    (by rw [e1f]; exact hfres0)

  refine ⟨Q, hQdom, hordQ, hordP, hμa, ?_, ?_⟩
  ·
    obtain ⟨hmemN, hresN, hunitN⟩ := hnear Q hQdom
    obtain ⟨hmemF, hresF, -⟩ := hfar Q (hdom ▸ hQdom)
    have hfQ : f ∈ Q.toValuationSubring := Q.mem_of_ord_nonneg_G hf0 (hunit Q hQdom).1.symm.le
    have hκiF : algebraMap L F κ⁻¹ ∈ Q.toValuationSubring := Q.algebraMap_mem' _
    have hevF : Q.evalAt ((algebraMap L F κ)⁻¹ * f) = κ⁻¹ * Q.evalAt f := by
      rw [← map_inv₀, Q.evalAt_mul_G hQrat hκiF hfQ, Q.evalAt_algebraMap_G]
    have hκiA : κ⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, hμκ, inv_one])
    have hwunit : IsUnit (⟨Q.evalAt f, hmemN⟩ : ↥A) := hunitN hford
    have hw0 : IsLocalRing.residue ↥A ⟨Q.evalAt f, hmemN⟩ ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hwunit
    have hprodA : (⟨κ⁻¹, hκiA⟩ : ↥A) * ⟨Q.evalAt f, hmemN⟩ = ⟨Q.evalAt ((algebraMap L F κ)⁻¹ * f), hmemF⟩ :=
      Subtype.ext (by show κ⁻¹ * Q.evalAt f = Q.evalAt ((algebraMap L F κ)⁻¹ * f); rw [hevF])
    have hresκ : IsLocalRing.residue ↥A ⟨κ⁻¹, hκiA⟩
        = x'.evalAt (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) * (x.evalAt (C.residue ⟨f, hfC⟩))⁻¹ := by
      have h1 := congrArg (IsLocalRing.residue ↥A) hprodA
      rw [map_mul, hresN, hresF, hfres'] at h1
      rw [← h1, mul_inv_cancel_right₀]
      rw [← hresN]; exact hw0
    have hq : Q.evalAt An.param * c'⁻¹ ∈ A := by
      have : Q.evalAt An.param * c'⁻¹ = -κ⁻¹ := by rw [hκ, mul_inv, inv_inv, ha_def]; ring
      rw [this]; exact neg_mem hκiA
    refine ⟨hq, ?_, ?_⟩
    · have hμq : μ (Q.evalAt An.param * c'⁻¹) = 1 := by
        rw [map_mul, map_inv₀, show Q.evalAt An.param = a from rfl, hμa, mul_inv_cancel₀ (μ.pos hc'0).ne']
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 (residue_ne_zero_of_abv_eq_one_G μ hμA hq hμq)
    · have e2 : (⟨Q.evalAt An.param * c'⁻¹, hq⟩ : ↥A) = -⟨κ⁻¹, hκiA⟩ :=
        Subtype.ext (by show Q.evalAt An.param * c'⁻¹ = -κ⁻¹; rw [hκ, mul_inv, inv_inv, ha_def]; ring)
      rw [e2, map_neg, hresκ, hfres, neg_mul]
  · intro R hR
    obtain ⟨hmemN, hresN, hunitN⟩ := hnear R hR
    refine ⟨hmemN, hunitN hford, ?_⟩
    rw [hresN, hfres]

end S_AlgebraicCurve_Annulus_exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one (solution)
