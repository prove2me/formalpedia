-- Prove2me | solution 1 for AlgebraicCurve.Annulus.abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/36e85e10-9fb6-517b-b721-05d14e0cd501

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord_zero Place.ord_inv HasPrincipalDivisors Place.ord_algebraMap Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends"
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
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_pos_of_evalAt_eq_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
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

end Place
p2m_export "AlgebraicCurve" "Place.ord_pos_of_evalAt_eq_zero_G"
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
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (f : F) (hC : f ∈ C.integers) (hres : C.residue ⟨f, hC⟩ ≠ 0) (hord : x.ord (C.residue ⟨f, hC⟩) = 1)
    (hC' : (algebraMap L F (An.modulus : L))⁻¹ * f ∈ C'.integers)
    (hres' : C'.residue ⟨(algebraMap L F (An.modulus : L))⁻¹ * f, hC'⟩ ≠ 0)
    (hreg : ∀ R ∈ An.dom, f ∈ R.toValuationSubring) :
    (∀ R ∈ An.dom, R.ord f = 0) ∧
    ∀ P ∈ An.dom, ∀ Q ∈ An.dom,
      μ (P.evalAt f) = μ (P.evalAt An.param) ∧
      μ (P.evalAt f - Q.evalAt f) = μ (P.evalAt An.param - Q.evalAt An.param) := by
  obtain ⟨-, hzC, hzord, -⟩ := id hatt
  obtain ⟨-, hz'C, hz'ord, -⟩ := id hatt'
  set z := An.param with hz
  set z' := An'.param with hz'
  set π : L := (An.modulus : L) with hπ
  have hf0 : f ≠ 0 := by
    intro h0; apply hres
    have : (⟨f, hC⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  have hzres0 : C.residue ⟨z, hzC⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hzord; exact zero_ne_one hzord
  have hz'res0 : C'.residue ⟨z', hz'C⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hz'ord; exact zero_ne_one hz'ord
  have hz'0 : z' ≠ 0 := by
    intro h0; apply hz'res0
    have : (⟨z', hz'C⟩ : C'.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hz0 : z ≠ 0 := by
    intro h0; apply hzres0
    have : (⟨z, hzC⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hπA : π ∈ A := An.modulus.2
  have hμπ0 : 0 < μ π := μ.pos hmod0
  have hμπ1 : μ π < 1 := abv_lt_one_of_mem_maximalIdeal_G μ hμA An.modulus_mem
  have hPi : algebraMap L F π ≠ 0 := (map_ne_zero _).2 hmod0

  have hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord f := fun Q hQ => Q.ord_nonneg_of_mem_G (hreg Q hQ)

  have hdomQ : ∀ Q ∈ An.dom,
      Q.IsRational ∧ z ∈ Q.toValuationSubring ∧ z' ∈ Q.toValuationSubring ∧
      Q.evalAt z ∈ A ∧ Q.evalAt z' ∈ A ∧ Q.evalAt z ≠ 0 ∧ Q.evalAt z' ≠ 0 ∧
      Q.evalAt z' * Q.evalAt z = π ∧ μ π < μ (Q.evalAt z) ∧ μ (Q.evalAt z) < 1 := by
    intro Q hQ
    obtain ⟨hrat, hzQ, ⟨hzA, hz𝔪⟩, hzQ0, m, hm𝔪, hm⟩ := An.mem_dom Q hQ
    obtain ⟨-, hz'Q, ⟨hz'A, -⟩, hz'Q0, -⟩ := An'.mem_dom Q (hdom ▸ hQ)
    have hprod : Q.evalAt z' * Q.evalAt z = π := by
      rw [← Q.evalAt_mul_G hrat hz'Q hzQ, htwo, Q.evalAt_algebraMap_G]
    refine ⟨hrat, hzQ, hz'Q, hzA, hz'A, hzQ0, hz'Q0, hprod, ?_, abv_lt_one_of_mem_maximalIdeal_G μ hμA hz𝔪⟩
    rw [hπ, hm, map_mul]
    have hzpos : 0 < μ (Q.evalAt z) := μ.pos hzQ0
    have hm1 : μ (m : L) < 1 := abv_lt_one_of_mem_maximalIdeal_G μ hμA hm𝔪
    calc μ (Q.evalAt z) * μ (m : L) < μ (Q.evalAt z) * 1 := mul_lt_mul_of_pos_left hm1 hzpos
      _ = μ (Q.evalAt z) := mul_one _

  have hinj : ∀ R ∈ An.dom, ∀ Q ∈ An.dom, R.evalAt z = Q.evalAt z → R = Q := by
    intro R hR Q hQ hRQ
    obtain ⟨-, -, ⟨haA, ha𝔪⟩, ha0, hm⟩ := An.mem_dom Q hQ
    obtain ⟨P₀, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨Q.evalAt z, haA⟩ ha𝔪 ha0 hm
    exact (huniq R ⟨hR, hRQ⟩).trans (huniq Q ⟨hQ, rfl⟩).symm

  obtain ⟨D, hD0, hDsupp, hDord, hdeg, hsum⟩ :=
    AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
      An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide f hC hres π hmod0 hπA hC' hres' hpole
  rw [hord] at hdeg
  have hDzero : D = 0 := by
    by_contra hne
    obtain ⟨R, hDR⟩ : ∃ R, D R ≠ 0 := by
      by_contra hall; push Not at hall; exact hne (Finsupp.ext hall)
    have hRdom : R ∈ An.dom := hDsupp R hDR
    set d : ℤ := D.sum fun _ m => m with hd
    have hDR1 : 1 ≤ D R := lt_of_le_of_ne (hD0 R) (Ne.symm hDR)
    have hlow : (d : ℝ) * Real.log (μ π) < D.sum fun Q m => (m : ℝ) * Real.log (μ (Q.evalAt z)) := by
      rw [hd, Finsupp.sum, Finsupp.sum, Int.cast_sum, Finset.sum_mul]
      apply Finset.sum_lt_sum
      · intro Q hQ
        have hQdom : Q ∈ An.dom := hDsupp Q (Finsupp.mem_support_iff.1 hQ)
        have hDQ : (0 : ℝ) ≤ (D Q : ℝ) := by exact_mod_cast hD0 Q
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log hμπ0 (hdomQ Q hQdom).2.2.2.2.2.2.2.2.1.le) hDQ
      · refine ⟨R, Finsupp.mem_support_iff.2 hDR, ?_⟩
        have hDRpos : (0 : ℝ) < (D R : ℝ) := by exact_mod_cast hDR1
        exact mul_lt_mul_of_pos_left (Real.log_lt_log hμπ0 (hdomQ R hRdom).2.2.2.2.2.2.2.2.1) hDRpos
    have ha' : x'.ord (C'.residue ⟨_, hC'⟩) = d - 1 := by rw [hd]; omega
    rw [ha'] at hsum
    have hrhs : (D.sum fun Q m => (m : ℝ) * Real.log (μ (Q.evalAt z))) ≤ (d : ℝ) * Real.log (μ π) := by
      rw [hsum]; push_cast; nlinarith
    exact absurd (hlow.trans_le hrhs) (lt_irrefl _)
  rw [hDzero, Finsupp.sum_zero_index] at hdeg
  have hzf : ∀ R ∈ An.dom, R.ord f = 0 := by
    intro R hR
    rw [← hDord R hR, hDzero]; rfl
  have ha' : x'.ord (C'.residue ⟨_, hC'⟩) = -1 := by omega

  have hzinv : z⁻¹ ∈ C.integers := inv_mem_of_isUnit_G hzC (C.isUnit_of_residue_ne_zero_G hzC hzres0)
  set f₂ : F := f * z⁻¹ with hf₂
  have hf₂0 : f₂ ≠ 0 := mul_ne_zero hf0 (inv_ne_zero hz0)
  have hf₂C : f₂ ∈ C.integers := mul_mem hC hzinv
  have hf₂res : C.residue ⟨f₂, hf₂C⟩ = C.residue ⟨f, hC⟩ * (C.residue ⟨z, hzC⟩)⁻¹ := by
    have e1 : (⟨f₂, hf₂C⟩ : C.integers) = ⟨f, hC⟩ * ⟨z⁻¹, hzinv⟩ := Subtype.ext rfl
    rw [e1, map_mul, C.residue_inv_G hzC hzres0 hzinv]
  have hf₂res0 : C.residue ⟨f₂, hf₂C⟩ ≠ 0 := by
    rw [hf₂res]; exact mul_ne_zero hres (inv_ne_zero hzres0)
  have hf₂ord : x.ord (C.residue ⟨f₂, hf₂C⟩) = 0 := by
    rw [hf₂res, x.ord_mul hres (inv_ne_zero hzres0), Place.ord_inv, hord, hzord]
    ring
  have hz_eq : z = algebraMap L F π * z'⁻¹ := by
    rw [← htwo, mul_comm z' z, mul_inv_cancel_right₀ hz'0]
  have key : (algebraMap L F (1 : L))⁻¹ * f₂ = (algebraMap L F π)⁻¹ * f * z' := by
    rw [map_one, inv_one, one_mul f₂, hf₂, hz_eq]
    field_simp
  have hC'₂ : (algebraMap L F (1 : L))⁻¹ * f₂ ∈ C'.integers := by
    rw [key]; exact mul_mem hC' hz'C
  have hres'₂eq : C'.residue ⟨_, hC'₂⟩ = C'.residue ⟨_, hC'⟩ * C'.residue ⟨z', hz'C⟩ := by
    have e1 : (⟨_, hC'₂⟩ : C'.integers) = ⟨_, hC'⟩ * ⟨z', hz'C⟩ := Subtype.ext key
    rw [e1, map_mul]
  have hres'₂ : C'.residue ⟨_, hC'₂⟩ ≠ 0 := by rw [hres'₂eq]; exact mul_ne_zero hres' hz'res0
  have hord'₂ : x'.ord (C'.residue ⟨_, hC'₂⟩) = 0 := by
    rw [hres'₂eq, x'.ord_mul hres' hz'res0, ha', hz'ord]; ring
  have hpole₂ : ∀ Q ∈ An.dom, 0 ≤ Q.ord f₂ := by
    intro Q hQ
    obtain ⟨-, hzQ, -, hzQ0, -⟩ := An.mem_dom Q hQ
    have hzQord : Q.ord z = 0 := Q.ord_eq_zero_of_evalAt_ne_zero_G hzQ hzQ0
    rw [hf₂, Q.ord_mul hf0 (inv_ne_zero hz0), Place.ord_inv, hzQord]
    simpa using hpole Q hQ
  obtain ⟨-, -, hc⟩ := AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends μ hμA
    An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide f₂ hf₂C hf₂res0 1 one_ne_zero (one_mem A) hC'₂ hres'₂ hpole₂
  have hsize : ∀ R ∈ An.dom, μ (R.evalAt f) = μ (R.evalAt z) := by
    intro R hR
    obtain ⟨hordf₂, hμf₂⟩ := hc ⟨by rw [map_one], hf₂ord, hord'₂⟩ R hR
    obtain ⟨hRrat, hzR, -⟩ := An.mem_dom R hR
    have hf₂R : f₂ ∈ R.toValuationSubring := R.mem_of_ord_nonneg_G hf₂0 hordf₂.symm.le
    have hf_eq : f = f₂ * z := by rw [hf₂, inv_mul_cancel_right₀ hz0]
    rw [hf_eq, R.evalAt_mul_G hRrat hf₂R hzR, map_mul, hμf₂, one_mul (μ _)]

  have hdiff : ∀ Q ∈ An.dom, ∀ P ∈ An.dom, P ≠ Q →
      μ (P.evalAt f - Q.evalAt f) = μ (P.evalAt z - Q.evalAt z) := by
    intro Q hQ P hP hPQ
    obtain ⟨hQrat, hzQ, hz'Q, haA, hbA, ha0, hb0, hba, hπa, ha1⟩ := hdomQ Q hQ
    have hfQ : f ∈ Q.toValuationSubring := hreg Q hQ
    have hμc : μ (Q.evalAt f) = μ (Q.evalAt z) := hsize Q hQ
    set a : L := Q.evalAt z with ha_def
    set b : L := Q.evalAt z' with hb_def
    set c : L := Q.evalAt f with hc_def
    have hcA : c ∈ A := (hμA c).2 (by rw [hμc]; exact ha1.le)
    have hc𝔪 : (⟨c, hcA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
      mem_maximalIdeal_of_abv_lt_one_G μ hμA hcA (by rw [hμc]; exact ha1)
    have ha𝔪 : (⟨a, haA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := mem_maximalIdeal_of_abv_lt_one_G μ hμA haA ha1
    have hμb1 : μ b < 1 := by
      obtain ⟨-, -, ⟨hbA', hb𝔪⟩, -⟩ := An'.mem_dom Q (hdom ▸ hQ)
      exact abv_lt_one_of_mem_maximalIdeal_G μ hμA hb𝔪
    have hb𝔪 : (⟨b, hbA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := mem_maximalIdeal_of_abv_lt_one_G μ hμA hbA hμb1

    set Cc := algebraMap L F c with hCc
    set Ca := algebraMap L F a with hCa
    set Cb := algebraMap L F b with hCb
    set u : F := f - Cc with hu
    set w : F := z - Ca with hw
    set g : F := u * w⁻¹ with hg

    have hCcC : Cc ∈ C.integers := (C.algebraMap_mem_iff c).2 hcA
    have hCaC : Ca ∈ C.integers := (C.algebraMap_mem_iff a).2 haA
    have hCcres : C.residue ⟨Cc, hCcC⟩ = 0 := C.residue_algebraMap_eq_zero_G ⟨c, hcA⟩ hc𝔪 hCcC
    have hCares : C.residue ⟨Ca, hCaC⟩ = 0 := C.residue_algebraMap_eq_zero_G ⟨a, haA⟩ ha𝔪 hCaC
    have huC : u ∈ C.integers := sub_mem hC hCcC
    have hwC : w ∈ C.integers := sub_mem hzC hCaC
    have hures : C.residue ⟨u, huC⟩ = C.residue ⟨f, hC⟩ := by
      have e1 : (⟨u, huC⟩ : C.integers) = ⟨f, hC⟩ - ⟨Cc, hCcC⟩ := Subtype.ext rfl
      rw [e1, map_sub, hCcres, sub_zero]
    have hwres : C.residue ⟨w, hwC⟩ = C.residue ⟨z, hzC⟩ := by
      have e1 : (⟨w, hwC⟩ : C.integers) = ⟨z, hzC⟩ - ⟨Ca, hCaC⟩ := Subtype.ext rfl
      rw [e1, map_sub, hCares, sub_zero]
    have hwres0 : C.residue ⟨w, hwC⟩ ≠ 0 := by rw [hwres]; exact hzres0
    have hures0 : C.residue ⟨u, huC⟩ ≠ 0 := by rw [hures]; exact hres
    have hu0 : u ≠ 0 := by
      intro h0; apply hures0
      have : (⟨u, huC⟩ : C.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    have hw0 : w ≠ 0 := by
      intro h0; apply hwres0
      have : (⟨w, hwC⟩ : C.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    have hwinv : w⁻¹ ∈ C.integers := inv_mem_of_isUnit_G hwC (C.isUnit_of_residue_ne_zero_G hwC hwres0)
    have hgC : g ∈ C.integers := mul_mem huC hwinv
    have hgres : C.residue ⟨g, hgC⟩ = C.residue ⟨f, hC⟩ * (C.residue ⟨z, hzC⟩)⁻¹ := by
      have e1 : (⟨g, hgC⟩ : C.integers) = ⟨u, huC⟩ * ⟨w⁻¹, hwinv⟩ := Subtype.ext rfl
      rw [e1, map_mul, C.residue_inv_G hwC hwres0 hwinv, hures, hwres]
    have hgres0 : C.residue ⟨g, hgC⟩ ≠ 0 := by
      rw [hgres]; exact mul_ne_zero hres (inv_ne_zero hzres0)
    have hgord : x.ord (C.residue ⟨g, hgC⟩) = 0 := by
      rw [hgres, x.ord_mul hres (inv_ne_zero hzres0), Place.ord_inv, hord, hzord]; ring
    have hg0 : g ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hw0)

    set X : L := c * a⁻¹ with hX
    have hμX : μ X = 1 := by rw [hX, map_mul, map_inv₀, hμc, mul_inv_cancel₀ (μ.pos ha0).ne']
    have hXA : X ∈ A := (hμA X).2 hμX.le
    have hXres : IsLocalRing.residue ↥A ⟨X, hXA⟩ ≠ 0 := residue_ne_zero_of_abv_eq_one_G μ hμA hXA hμX
    set CX := algebraMap L F X with hCX
    set F₀ : F := (algebraMap L F π)⁻¹ * f with hF₀
    have hF₀C' : F₀ ∈ C'.integers := hC'
    have hCXC' : CX ∈ C'.integers := (C'.algebraMap_mem_iff X).2 hXA
    have hCbC' : Cb ∈ C'.integers := (C'.algebraMap_mem_iff b).2 hbA
    have hCbres : C'.residue ⟨Cb, hCbC'⟩ = 0 := C'.residue_algebraMap_eq_zero_G ⟨b, hbA⟩ hb𝔪 hCbC'
    have hCXres : C'.residue ⟨CX, hCXC'⟩
        = algebraMap (IsLocalRing.ResidueField ↥A) _ (IsLocalRing.residue ↥A ⟨X, hXA⟩) := by
      have e1 : (⟨CX, hCXC'⟩ : C'.integers)
          = ⟨algebraMap L F ((⟨X, hXA⟩ : ↥A) : L), (C'.algebraMap_mem_iff _).mpr (⟨X, hXA⟩ : ↥A).2⟩ := rfl
      rw [e1, C'.residue_algebraMap]
    have hCXres0 : C'.residue ⟨CX, hCXC'⟩ ≠ 0 := by
      rw [hCXres]; exact (map_ne_zero_iff _ (algebraMap (IsLocalRing.ResidueField ↥A) _).injective).2 hXres
    set v : F := CX - Cb * F₀ with hv
    set w' : F := z' - Cb with hw'
    have hvC' : v ∈ C'.integers := sub_mem hCXC' (mul_mem hCbC' hF₀C')
    have hw'C' : w' ∈ C'.integers := sub_mem hz'C hCbC'
    have hvres : C'.residue ⟨v, hvC'⟩ = C'.residue ⟨CX, hCXC'⟩ := by
      have e1 : (⟨v, hvC'⟩ : C'.integers) = ⟨CX, hCXC'⟩ - ⟨Cb, hCbC'⟩ * ⟨F₀, hF₀C'⟩ := Subtype.ext rfl
      rw [e1, map_sub, map_mul, hCbres, zero_mul, sub_zero]
    have hw'res : C'.residue ⟨w', hw'C'⟩ = C'.residue ⟨z', hz'C⟩ := by
      have e1 : (⟨w', hw'C'⟩ : C'.integers) = ⟨z', hz'C⟩ - ⟨Cb, hCbC'⟩ := Subtype.ext rfl
      rw [e1, map_sub, hCbres, sub_zero]
    have hw'res0 : C'.residue ⟨w', hw'C'⟩ ≠ 0 := by rw [hw'res]; exact hz'res0
    have hw'0 : w' ≠ 0 := by
      intro h0; apply hw'res0
      have : (⟨w', hw'C'⟩ : C'.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    have hw'inv : w'⁻¹ ∈ C'.integers := inv_mem_of_isUnit_G hw'C' (C'.isUnit_of_residue_ne_zero_G hw'C' hw'res0)

    have ha_eq : a = π * b⁻¹ := by
      rw [← hba, mul_comm b a, mul_inv_cancel_right₀ hb0]
    have hCb0 : Cb ≠ 0 := by rw [hCb]; exact (map_ne_zero _).2 hb0
    have hgv : g = v * (z' * w'⁻¹) := by
      have hw_eq : w = algebraMap L F π * (Cb - z') * (z' * Cb)⁻¹ := by
        rw [hw, hz_eq, hCa, ha_eq, map_mul, map_inv₀, ← hCb]
        field_simp
      have hu_eq : u = algebraMap L F π * (F₀ - CX * Cb⁻¹) := by
        rw [hu, hF₀, hCX, hX, hCc, ha_eq, mul_inv, inv_inv, map_mul, map_mul, map_inv₀, ← hCb]
        field_simp
      have hCbz' : Cb - z' ≠ 0 := by rw [sub_ne_zero]; exact fun h => hw'0 (by rw [hw', h, sub_self])
      have hz'b : z' - Cb ≠ 0 := by rw [hw'] at hw'0; exact hw'0
      have hz'b' : -Cb + z' ≠ 0 := by rw [neg_add_eq_sub]; exact hz'b
      rw [hg, hw_eq, hu_eq, hv, hw']
      first | (field_simp; done) | (field_simp; ring)
    have hgC' : g ∈ C'.integers := by rw [hgv]; exact mul_mem hvC' (mul_mem hz'C hw'inv)
    have hgres' : C'.residue ⟨g, hgC'⟩ = C'.residue ⟨CX, hCXC'⟩ := by
      have e1 : (⟨g, hgC'⟩ : C'.integers) = ⟨v, hvC'⟩ * (⟨z', hz'C⟩ * ⟨w'⁻¹, hw'inv⟩) := Subtype.ext hgv
      rw [e1, map_mul, map_mul, C'.residue_inv_G hw'C' hw'res0 hw'inv, hvres, hw'res,
        mul_inv_cancel₀ hz'res0, mul_one]
    have hgC'1 : (algebraMap L F (1 : L))⁻¹ * g ∈ C'.integers := by
      rw [map_one, inv_one, one_mul g]; exact hgC'
    have e1g : (⟨_, hgC'1⟩ : C'.integers) = ⟨g, hgC'⟩ :=
      Subtype.ext (by show (algebraMap L F (1 : L))⁻¹ * g = g; rw [map_one, inv_one, one_mul g])
    have hgres'0 : C'.residue ⟨_, hgC'1⟩ ≠ 0 := by rw [e1g, hgres']; exact hCXres0
    have hgord' : x'.ord (C'.residue ⟨_, hgC'1⟩) = 0 := by
      rw [e1g, hgres', hCXres]; exact Place.ord_algebraMap _ _

    have hgpole : ∀ R ∈ An.dom, 0 ≤ R.ord g := by
      intro R hR
      obtain ⟨hRrat, hzR, -⟩ := An.mem_dom R hR
      have hfR : f ∈ R.toValuationSubring := hreg R hR
      have huR : u ∈ R.toValuationSubring := sub_mem hfR (R.algebraMap_mem' c)
      have hwR : w ∈ R.toValuationSubring := sub_mem hzR (R.algebraMap_mem' a)
      rw [hg, R.ord_mul hu0 (inv_ne_zero hw0), Place.ord_inv]
      by_cases hRQ : R = Q
      · subst hRQ
        have hw1 : R.ord w = 1 := by rw [hw, hCa, ha_def]; exact An.ord_param_sub R hR
        have hu1 : 0 < R.ord u := by
          apply R.ord_pos_of_evalAt_eq_zero_G hRrat huR hu0
          rw [hu, R.evalAt_sub_G hRrat hfR (R.algebraMap_mem' c), R.evalAt_algebraMap_G, hc_def, sub_self]
        omega
      · have hw0' : R.ord w = 0 := by
          apply R.ord_eq_zero_of_evalAt_ne_zero_G hwR
          rw [hw, R.evalAt_sub_G hRrat hzR (R.algebraMap_mem' a), R.evalAt_algebraMap_G, ha_def, sub_ne_zero]
          exact fun h => hRQ (hinj R hR Q hQ h)
        have := R.ord_nonneg_of_mem_G huR
        omega
    obtain ⟨-, -, hcg⟩ := AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends μ hμA
      An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide g hgC hgres0 1 one_ne_zero (one_mem A) hgC'1 hgres'0 hgpole
    obtain ⟨hordg, hμg⟩ := hcg ⟨by rw [map_one], hgord, hgord'⟩ P hP

    obtain ⟨hPrat, hzP, -⟩ := An.mem_dom P hP
    have hfP : f ∈ P.toValuationSubring := hreg P hP
    have huP : u ∈ P.toValuationSubring := sub_mem hfP (P.algebraMap_mem' c)
    have hwP : w ∈ P.toValuationSubring := sub_mem hzP (P.algebraMap_mem' a)
    have hgP : g ∈ P.toValuationSubring := P.mem_of_ord_nonneg_G hg0 hordg.symm.le
    have hu_eq : u = g * w := by rw [hg, inv_mul_cancel_right₀ hw0]
    have h1 : P.evalAt u = P.evalAt g * P.evalAt w := by rw [hu_eq, P.evalAt_mul_G hPrat hgP hwP]
    have h2 : P.evalAt u = P.evalAt f - c := by
      rw [hu, P.evalAt_sub_G hPrat hfP (P.algebraMap_mem' c), P.evalAt_algebraMap_G]
    have h3 : P.evalAt w = P.evalAt z - a := by
      rw [hw, P.evalAt_sub_G hPrat hzP (P.algebraMap_mem' a), P.evalAt_algebraMap_G]
    rw [hc_def] at h2; rw [ha_def] at h3
    rw [← h2, h1, map_mul, hμg, one_mul (μ _), h3]

  refine ⟨hzf, fun P hP Q hQ => ⟨hsize P hP, ?_⟩⟩
  by_cases hPQ : P = Q
  · subst hPQ; rw [sub_self, sub_self]
  · exact hdiff Q hQ P hP hPQ

end S_AlgebraicCurve_Annulus_abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one (solution)
