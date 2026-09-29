-- Prove2me | solution 1 for AlgebraicCurve.Annulus.abv_evalAt_le_max_of_isAttached_both_ends
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/74fe0735-46dd-5261-abaf-9761452451f0

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_abv_evalAt_le_max_of_isAttached_both_ends
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_abv_evalAt_le_max_of_isAttached_both_ends.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord_inv HasPrincipalDivisors Place.ord_algebraMap Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends"
p2m_open "AlgebraicCurve"

open IsLocalRing

section IsometryHelpers

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt ord_algebraMap" end Place
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
p2m_open_scoped "AlgebraicCurve.Place" in

theorem Place.evalAt_sub_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

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
p2m_open_scoped "AlgebraicCurve.Place" in

theorem Place.ord_eq_zero_of_evalAt_ne_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F]
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

namespace ComponentChart p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff residue exists_smul_mem residue_algebraMap ker_residue dom" end ComponentChart
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

p2m_open_scoped "AlgebraicCurve.ComponentChart" in

theorem ComponentChart.residue_inv_G
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

p2m_open_scoped "AlgebraicCurve.ComponentChart" in

theorem ComponentChart.residue_algebraMap_eq_zero_G
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (h : algebraMap L F a ∈ C.integers) : C.residue ⟨algebraMap L F a, h⟩ = 0 := by
  have e1 : (⟨algebraMap L F a, h⟩ : C.integers) = ⟨algebraMap L F a, (C.algebraMap_mem_iff a).mpr a.2⟩ := rfl
  rw [e1, C.residue_algebraMap a, (IsLocalRing.residue_eq_zero_iff _).2 ha, map_zero]

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

namespace Annulus p2m_export "AlgebraicCurve.Annulus" "IsAttached existsUnique_evalAt_eq modulus modulus_mem dom mem_dom param ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends" end Annulus
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
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (g : F) (hg0 : g ≠ 0) (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord g)
    (hgC : g ∈ C.integers) (b : L) (hb0 : b ≠ 0) (hgC' : (algebraMap L F b)⁻¹ * g ∈ C'.integers) :
    ∀ R ∈ An.dom, μ (R.evalAt g) ≤ max 1 (μ b) ∧ (μ b ≠ 1 → μ (R.evalAt g) < max 1 (μ b)) := by
  classical
  obtain ⟨-, hzC, hzord, -⟩ := id hatt
  obtain ⟨-, hz'C', hz'ord, -⟩ := id hatt'
  set z := An.param with hz_def
  set z' := An'.param with hz'_def
  set π : L := (An.modulus : L) with hπ
  have hμπ0 : 0 < μ π := μ.pos hmod0
  have hbL : algebraMap L F b ≠ 0 := (map_ne_zero _).2 hb0
  set g' : F := (algebraMap L F b)⁻¹ * g with hg'
  have hg'0 : g' ≠ 0 := mul_ne_zero (inv_ne_zero hbL) hg0

  have hdomR : ∀ R ∈ An.dom,
      R.IsRational ∧ z ∈ R.toValuationSubring ∧ z' ∈ R.toValuationSubring ∧
      R.evalAt z ≠ 0 ∧ R.evalAt z' ≠ 0 ∧ R.evalAt z' * R.evalAt z = π := by
    intro R hR
    obtain ⟨hrat, hzR, -, hzR0, -⟩ := An.mem_dom R hR
    obtain ⟨-, hz'R, -, hz'R0, -⟩ := An'.mem_dom R (hdom ▸ hR)
    have hprod : R.evalAt z' * R.evalAt z = π := by
      rw [← R.evalAt_mul_G hrat hz'R hzR, htwo, R.evalAt_algebraMap_G]
    exact ⟨hrat, hzR, hz'R, hzR0, hz'R0, hprod⟩
  have hwide' : ∃ Q₁ ∈ An'.dom, ∃ Q₂ ∈ An'.dom, μ (Q₁.evalAt An'.param) ≠ μ (Q₂.evalAt An'.param) := by
    obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := hwide
    refine ⟨Q₁, hdom ▸ hQ₁, Q₂, hdom ▸ hQ₂, ?_⟩
    have key : ∀ R ∈ An.dom, μ (R.evalAt An'.param) * μ (R.evalAt z) = μ π := by
      intro R hR
      obtain ⟨-, -, -, -, -, hp⟩ := hdomR R hR
      rw [← map_mul]; exact congrArg μ hp
    intro heq; apply hne
    have h1 := key Q₁ hQ₁
    have h2 := key Q₂ hQ₂
    rw [heq] at h1
    have h12 := h1.trans h2.symm
    have hne0 : μ (Q₂.evalAt An'.param) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h2; exact hμπ0.ne h2
    exact mul_left_cancel₀ hne0 h12

  obtain ⟨c₁, hc₁g, hc₁res⟩ := C.exists_smul_mem g hg0
  obtain ⟨c₂, hc₂g, hc₂res⟩ := C'.exists_smul_mem g' hg'0
  set h₀ : F := c₁ • g with hh₀
  set h₁ : F := c₂ • g' with hh₁
  have hsm₁ : h₀ = algebraMap L F c₁ * g := Algebra.smul_def _ _
  have hsm₂ : h₁ = algebraMap L F c₂ * g' := Algebra.smul_def _ _
  have hc₁0 : c₁ ≠ 0 := by
    intro h0; apply hc₁res
    have : (⟨h₀, hc₁g⟩ : C.integers) = 0 := Subtype.ext (by show c₁ • g = 0; rw [h0, zero_smul])
    rw [this, map_zero]
  have hc₂0 : c₂ ≠ 0 := by
    intro h0; apply hc₂res
    have : (⟨h₁, hc₂g⟩ : C'.integers) = 0 := Subtype.ext (by show c₂ • g' = 0; rw [h0, zero_smul])
    rw [this, map_zero]

  have hu₁ : IsUnit (⟨h₀, hc₁g⟩ : C.integers) := C.isUnit_of_residue_ne_zero_G hc₁g hc₁res
  have hu₂ : IsUnit (⟨h₁, hc₂g⟩ : C'.integers) := C'.isUnit_of_residue_ne_zero_G hc₂g hc₂res
  have hc₁invA : c₁⁻¹ ∈ A := by
    have hinv : h₀⁻¹ ∈ C.integers := inv_mem_of_isUnit_G hc₁g hu₁
    have hprod : g * h₀⁻¹ = algebraMap L F c₁⁻¹ := by
      rw [hsm₁, map_inv₀]; field_simp
    have : algebraMap L F c₁⁻¹ ∈ C.integers := by rw [← hprod]; exact mul_mem hgC hinv
    exact (C.algebraMap_mem_iff _).1 this
  have hc₂invA : c₂⁻¹ ∈ A := by
    have hinv : h₁⁻¹ ∈ C'.integers := inv_mem_of_isUnit_G hc₂g hu₂
    have hprod : g' * h₁⁻¹ = algebraMap L F c₂⁻¹ := by
      rw [hsm₂, map_inv₀]; field_simp
    have : algebraMap L F c₂⁻¹ ∈ C'.integers := by rw [← hprod]; exact mul_mem hgC' hinv
    exact (C'.algebraMap_mem_iff _).1 this
  have hμc₁ : 1 ≤ μ c₁ := by
    have h1 : μ c₁⁻¹ ≤ 1 := (hμA _).1 hc₁invA
    rw [map_inv₀] at h1; exact (inv_le_one₀ (μ.pos hc₁0)).1 h1
  have hμc₂ : 1 ≤ μ c₂ := by
    have h1 : μ c₂⁻¹ ≤ 1 := (hμA _).1 hc₂invA
    rw [map_inv₀] at h1; exact (inv_le_one₀ (μ.pos hc₂0)).1 h1

  set c'' : L := c₁ * b * c₂⁻¹ with hc''
  have hc''0 : c'' ≠ 0 := mul_ne_zero (mul_ne_zero hc₁0 hb0) (inv_ne_zero hc₂0)
  have key₁ : (algebraMap L F c'')⁻¹ * h₀ = h₁ := by
    rw [hsm₁, hsm₂, hg', hc'', map_mul, map_mul, map_inv₀]
    have h1 : algebraMap L F c₁ ≠ 0 := (map_ne_zero _).2 hc₁0
    have h2 : algebraMap L F c₂ ≠ 0 := (map_ne_zero _).2 hc₂0
    field_simp
  have key₂ : (algebraMap L F c''⁻¹)⁻¹ * h₁ = h₀ := by
    rw [map_inv₀, inv_inv, ← key₁, ← mul_assoc, mul_inv_cancel₀ ((map_ne_zero _).2 hc''0), one_mul h₀]
  have hh₀0 : h₀ ≠ 0 := by rw [hsm₁]; exact mul_ne_zero ((map_ne_zero _).2 hc₁0) hg0
  have hh₁0 : h₁ ≠ 0 := by rw [hsm₂]; exact mul_ne_zero ((map_ne_zero _).2 hc₂0) hg'0
  have hordh₀ : ∀ R ∈ An.dom, R.ord h₀ = R.ord g := by
    intro R hR; rw [hsm₁, R.ord_mul ((map_ne_zero _).2 hc₁0) hg0, Place.ord_algebraMap, zero_add]
  have hordh₁ : ∀ R ∈ An.dom, R.ord h₁ = R.ord g := by
    intro R hR
    rw [hsm₂, hg', R.ord_mul ((map_ne_zero _).2 hc₂0) hg'0, Place.ord_algebraMap, zero_add,
      R.ord_mul (inv_ne_zero hbL) hg0, Place.ord_inv, Place.ord_algebraMap, neg_zero, zero_add]
  have hpole₀ : ∀ R ∈ An.dom, 0 ≤ R.ord h₀ := fun R hR => by rw [hordh₀ R hR]; exact hpole R hR
  have hpole₁ : ∀ R ∈ An'.dom, 0 ≤ R.ord h₁ := fun R hR => by rw [hordh₁ R (hdom ▸ hR)]; exact hpole R (hdom ▸ hR)

  have hval : ∀ R ∈ An.dom, g ∈ R.toValuationSubring ∧
      μ (R.evalAt h₀) = μ c₁ * μ (R.evalAt g) ∧ μ (R.evalAt h₁) = μ c₂ * (μ b)⁻¹ * μ (R.evalAt g) := by
    intro R hR
    obtain ⟨hrat, -⟩ := hdomR R hR
    have hgR : g ∈ R.toValuationSubring := R.mem_of_ord_nonneg_G hg0 (hpole R hR)
    refine ⟨hgR, ?_, ?_⟩
    · rw [hsm₁, R.evalAt_mul_G hrat (R.algebraMap_mem' _) hgR, R.evalAt_algebraMap_G, map_mul]
    · rw [hsm₂, hg', ← mul_assoc, ← map_inv₀, ← map_mul,
        R.evalAt_mul_G hrat (R.algebraMap_mem' _) hgR, R.evalAt_algebraMap_G, map_mul, map_mul, map_inv₀]
  intro R hR
  obtain ⟨hgR, hv₀, hv₁⟩ := hval R hR
  have hμb0 : 0 < μ b := μ.pos hb0
  have hμc₁0 : 0 < μ c₁ := μ.pos hc₁0
  have hμc₂0 : 0 < μ c₂ := μ.pos hc₂0
  by_cases hle : μ c'' ≤ 1
  ·
    have hc''A : c'' ∈ A := (hμA _).2 hle
    have hC'₀ : (algebraMap L F c'')⁻¹ * h₀ ∈ C'.integers := by rw [key₁]; exact hc₂g
    have e1 : (⟨_, hC'₀⟩ : C'.integers) = ⟨h₁, hc₂g⟩ := Subtype.ext key₁
    have hres'₀ : C'.residue ⟨_, hC'₀⟩ ≠ 0 := by rw [e1]; exact hc₂res
    obtain ⟨-, hb', -⟩ := AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends μ hμA
      An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide h₀ hc₁g hc₁res c'' hc''0 hc''A hC'₀ hres'₀ hpole₀
    obtain ⟨hle1, hstrict⟩ := hb' R hR
    have hg1 : μ (R.evalAt g) ≤ 1 := by
      calc μ (R.evalAt g) = 1 * μ (R.evalAt g) := (one_mul _).symm
        _ ≤ μ c₁ * μ (R.evalAt g) := mul_le_mul_of_nonneg_right hμc₁ (μ.nonneg _)
        _ = μ (R.evalAt h₀) := hv₀.symm
        _ ≤ 1 := hle1
    refine ⟨hg1.trans (le_max_left _ _), fun hb1 => ?_⟩
    rcases hμc₁.lt_or_eq with hgt1 | heq1
    ·
      by_cases hg00 : R.evalAt g = 0
      · rw [hg00, map_zero]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
      · have hpos : 0 < μ (R.evalAt g) := μ.pos hg00
        calc μ (R.evalAt g) = 1 * μ (R.evalAt g) := (one_mul _).symm
          _ < μ c₁ * μ (R.evalAt g) := mul_lt_mul_of_pos_right hgt1 hpos
          _ = μ (R.evalAt h₀) := hv₀.symm
          _ ≤ 1 := hle1
          _ ≤ max 1 (μ b) := le_max_left _ _
    ·
      rcases lt_or_gt_of_ne hb1 with hblt | hbgt
      · have hc''lt : μ c'' < 1 := by
          rw [hc'', map_mul, map_mul, map_inv₀, ← heq1, one_mul]
          calc μ b * (μ c₂)⁻¹ ≤ μ b * 1 := by
                apply mul_le_mul_of_nonneg_left _ hμb0.le
                exact inv_le_one_of_one_le₀ hμc₂
            _ = μ b := mul_one _
            _ < 1 := hblt
        have h1 : μ (R.evalAt h₀) < 1 := hstrict (Or.inl hc''lt)
        rw [hv₀, ← heq1, one_mul] at h1
        exact h1.trans_le (le_max_left _ _)
      · exact hg1.trans_lt (lt_max_of_lt_right hbgt)
  ·
    push Not at hle
    set d : L := c''⁻¹ with hd
    have hd0 : d ≠ 0 := inv_ne_zero hc''0
    have hμd : μ d < 1 := by rw [hd, map_inv₀]; exact inv_lt_one_of_one_lt₀ hle
    have hdA : d ∈ A := (hμA _).2 hμd.le
    have hC₁ : (algebraMap L F d)⁻¹ * h₁ ∈ C.integers := by rw [key₂]; exact hc₁g
    have e2 : (⟨_, hC₁⟩ : C.integers) = ⟨h₀, hc₁g⟩ := Subtype.ext key₂
    have hres₁ : C.residue ⟨_, hC₁⟩ ≠ 0 := by rw [e2]; exact hc₁res
    have hmod0' : ((An'.modulus : L)) ≠ 0 := by rw [hmod]; exact hmod0
    have htwo' : An.param * An'.param = algebraMap L F (An'.modulus : L) := by rw [mul_comm, htwo, hmod]
    obtain ⟨-, hb', -⟩ := AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends μ hμA
      An' An hdom.symm hmod.symm hmod0' htwo' C' x' hatt' C x hatt hwide' h₁ hc₂g hc₂res d hd0 hdA hC₁ hres₁ hpole₁
    obtain ⟨-, hstrict⟩ := hb' R (hdom ▸ hR)
    have h1 : μ (R.evalAt h₁) < 1 := hstrict (Or.inl hμd)
    rw [hv₁] at h1

    have hglt : μ (R.evalAt g) < μ b := by
      have h2 : μ c₂ * (μ b)⁻¹ * μ (R.evalAt g) * (μ b * (μ c₂)⁻¹) < 1 * (μ b * (μ c₂)⁻¹) :=
        mul_lt_mul_of_pos_right h1 (mul_pos hμb0 (inv_pos.2 hμc₂0))
      have h3 : μ c₂ * (μ b)⁻¹ * μ (R.evalAt g) * (μ b * (μ c₂)⁻¹) = μ (R.evalAt g) := by
        field_simp
      rw [h3, one_mul] at h2
      calc μ (R.evalAt g) < μ b * (μ c₂)⁻¹ := h2
        _ ≤ μ b * 1 := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hμc₂) hμb0.le
        _ = μ b := mul_one _
    exact ⟨hglt.le.trans (le_max_right _ _), fun _ => hglt.trans_le (le_max_right _ _)⟩

end S_AlgebraicCurve_Annulus_abv_evalAt_le_max_of_isAttached_both_ends
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_abv_evalAt_le_max_of_isAttached_both_ends (solution)
