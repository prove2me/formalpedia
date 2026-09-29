-- Prove2me | solution 1 for AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/05204e56-af38-5d9b-ae2f-3bf9cdfb9bbd

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_eq_evalAt_residue_of_isAttached_both_ends
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord Place.ord_zero Place.ord_inv HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends Place.mem_of_ord_nonneg Annulus.residue_evalAt_eq_evalAt_residue_of_isAttached_both_ends"
p2m_open "AlgebraicCurve"

private theorem abv_sub_le_max {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (a b : L) :
    μ (a - b) ≤ max (μ a) (μ b) := by
  rcases le_total (μ b) (μ a) with hab | hab
  ·
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [map_zero] at hab
      have hb : b = 0 := μ.eq_zero.1 (le_antisymm hab (μ.nonneg b))
      simp [hb]
    have hq : b * a⁻¹ ∈ A := (hμA _).2 (by
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ (μ.pos ha0)).2 (by simpa using hab))
    have h1 : 1 - b * a⁻¹ ∈ A := sub_mem (one_mem _) hq
    have h2 : μ (1 - b * a⁻¹) ≤ 1 := (hμA _).1 h1
    have : a - b = a * (1 - b * a⁻¹) := by field_simp
    rw [this, map_mul]
    calc μ a * μ (1 - b * a⁻¹) ≤ μ a * 1 := mul_le_mul_of_nonneg_left h2 (μ.nonneg a)
      _ = μ a := mul_one _
      _ ≤ max (μ a) (μ b) := le_max_left _ _
  · rcases eq_or_ne b 0 with rfl | hb0
    · rw [map_zero] at hab
      have ha : a = 0 := μ.eq_zero.1 (le_antisymm hab (μ.nonneg a))
      simp [ha]
    have hq : a * b⁻¹ ∈ A := (hμA _).2 (by
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ (μ.pos hb0)).2 (by simpa using hab))
    have h1 : a * b⁻¹ - 1 ∈ A := sub_mem hq (one_mem _)
    have h2 : μ (a * b⁻¹ - 1) ≤ 1 := (hμA _).1 h1
    have : a - b = b * (a * b⁻¹ - 1) := by field_simp
    rw [this, map_mul]
    calc μ b * μ (a * b⁻¹ - 1) ≤ μ b * 1 := mul_le_mul_of_nonneg_left h2 (μ.nonneg b)
      _ = μ b := mul_one _
      _ ≤ max (μ a) (μ b) := le_max_right _ _

private theorem abv_eq_one_of_isUnit_vs {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L} (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : A)) : μ a = 1 := by
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : a * (b : L) = 1 := by
    have := congrArg (fun t : A => (t : L)) hb
    simpa using this
  have h1 : μ a * μ (b : L) = 1 := by rw [← map_mul, hb', map_one]
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  have hb1 : μ (b : L) ≤ 1 := (hμA (b : L)).1 b.2
  have ha0 : 0 ≤ μ a := μ.nonneg a
  exact le_antisymm ha1 (by nlinarith)

private theorem abv_lt_one_of_mem_maximalIdeal_vs {L : Type*} [Field L]
    {A : ValuationSubring L} (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L}
    (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A) : μ a < 1 := by
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  refine lt_of_le_of_ne ha1 fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at h1
  have hinv : a⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

private theorem residue_eq_zero_of_mem_maximalIdeal' {L : Type*} [Field L] {A : ValuationSubring L}
    {a : L} (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A) :
    IsLocalRing.residue A ⟨a, ha⟩ = 0 :=
  (IsLocalRing.residue_eq_zero_iff _).2 hm

private theorem abv_evalAt_eq_zpow_of_isAttached
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (IsLocalRing.ResidueField A) Fbar)
    (hatt : An.IsAttached C x) (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hzf : ∀ Q ∈ An.dom, Q.ord f = 0) :
    ∀ Q ∈ An.dom, 0 < μ (Q.evalAt An.param) ∧ μ (Q.evalAt An.param) < 1 ∧
      μ (Q.evalAt f) = μ (Q.evalAt An.param) ^ (x.ord (C.residue ⟨f, hf⟩)) := by
  intro Q hQ
  obtain ⟨-, hzC, -, hlaw⟩ := hatt
  obtain ⟨hw, hunit⟩ := hlaw f hf hres hzf Q hQ
  obtain ⟨-, -, ⟨hzA, hzmax⟩, hz0, -⟩ := An.mem_dom Q hQ
  have hμz1 : μ (Q.evalAt An.param) < 1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA hzA hzmax
  have hμz0 : 0 < μ (Q.evalAt An.param) := μ.pos hz0
  have hunit1 := abv_eq_one_of_isUnit_vs μ hμA hw hunit
  rw [map_mul, map_zpow₀, zpow_neg] at hunit1
  exact ⟨hμz0, hμz1, (mul_inv_eq_one₀ (zpow_ne_zero _ hμz0.ne')).1 hunit1⟩

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField ord ord_zero ord_mul ord_inv ord_coe_unit ord_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring adicValuation_le_one_of_mem adicValuation_le_one_iff IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt mem_of_ord_nonneg" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_mul' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_mul'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_sub' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_sub'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_algebraMap'"
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_prod' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {ι : Type*} (S : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ S, f i ∈ v.toValuationSubring) :
    (∏ i ∈ S, f i) ∈ v.toValuationSubring ∧ v.evalAt (∏ i ∈ S, f i) = ∏ i ∈ S, v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨by simp, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨hmem, heq⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfi : f i ∈ v.toValuationSubring := hf i (Finset.mem_insert_self _ _)
    refine ⟨?_, ?_⟩
    · rw [Finset.prod_insert hi]; exact mul_mem hfi hmem
    · rw [Finset.prod_insert hi, Finset.prod_insert hi, v.evalAt_mul' hv hfi hmem, heq]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul' hv (pow_mem hf n) hf, ih]

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_neg' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (f : F) : v.ord (-f) = v.ord f := by
  unfold Place.ord
  rw [Valuation.map_neg]

end Place
p2m_export "AlgebraicCurve" "Place.ord_neg'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

end Place
p2m_export "AlgebraicCurve" "Place.ord_pow'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_prod' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {ι : Type*} (S : Finset ι) (f : ι → F) (hf : ∀ i ∈ S, f i ≠ 0) :
    v.ord (∏ i ∈ S, f i) = ∑ i ∈ S, v.ord (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      v.ord_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.2 fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

end Place
p2m_export "AlgebraicCurve" "Place.ord_prod'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hmem := v.algebraMap_mem' c
  have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
    rw [← map_inv₀]; exact v.algebraMap_mem' _
  have h1 : 0 ≤ v.ord (algebraMap K F c) := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hmem) with h | h
    · simp [h]
    · exact h
  have h2 : 0 ≤ v.ord (algebraMap K F c)⁻¹ := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hmem') with h | h
    · simp [h]
    · exact h
  rw [v.ord_inv] at h2
  omega

end Place
p2m_export "AlgebraicCurve" "Place.ord_algebraMap'"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hf) with h | h
  · simp [h]
  · exact h

end Place
p2m_export "AlgebraicCurve" "Place.ord_nonneg_of_mem'"
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.isUnit_of_ord_eq_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hϖ
  rw [h, zpow_zero, mul_one] at hu
  have : (⟨f, hf⟩ : v.toValuationSubring) = u := Subtype.ext hu
  rw [this]
  exact Units.isUnit u

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_evalAt_ne_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne (v.ord_nonneg_of_mem' hf) (Ne.symm hne)
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
p2m_export "AlgebraicCurve" "Place.ord_eq_zero_of_evalAt_ne_zero'"

private theorem inv_mem_of_isUnit' {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
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

namespace ComponentChart p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff residue residue_algebraMap ker_residue dom" end ComponentChart
namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.isUnit_of_residue_ne_zero'
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]
    exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.isUnit_of_residue_ne_zero'"
namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.residue_inv'
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.residue_inv'"
end AlgebraicCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt.AlgebraicCurve IsLocalRing"

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
    (hx : x.IsRational)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h)
    (hz : An.param ∈ C.integers)
    (R : Place L F) (hR : R ∈ An.dom)
    (hout : ∀ Q ∈ An.dom, Q.ord h ≠ 0 → μ (Q.evalAt An.param) < μ (R.evalAt An.param)) :
    ∃ hmem : R.evalAt h * (R.evalAt An.param) ^ (-(x.ord (C.residue ⟨h, hC⟩))) ∈ A,
      IsUnit (⟨_, hmem⟩ : A) ∧
      IsLocalRing.residue A ⟨_, hmem⟩
        = x.evalAt (C.residue ⟨h, hC⟩ * (C.residue ⟨An.param, hz⟩) ^ (-(x.ord (C.residue ⟨h, hC⟩)))) := by
  classical
  have hwide0 := hwide

  set h' : F := (algebraMap L F c')⁻¹ * h with hh'_def
  set a : ℤ := x.ord (C.residue ⟨h, hC⟩) with ha_def
  set a' : ℤ := x'.ord (C'.residue ⟨h', hC'⟩) with ha'_def
  set z : F := An.param with hz_def
  set z' : F := An'.param with hz'_def
  set π : L := (An.modulus : L) with hπ_def
  have hattC := hatt
  have hattC' := hatt'
  obtain ⟨hxnode, hzC, hzord, hlawC⟩ := hatt
  obtain ⟨hx'node, hz'C', hz'ord, hlawC'⟩ := hatt'
  have hh0 : h ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : F), hC⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have hh'0 : h' ≠ 0 := mul_ne_zero (inv_ne_zero ((map_ne_zero _).2 hc'0)) hh0
  have hπA : π ∈ A := An.modulus.2
  have hμπ0 : 0 < μ π := μ.pos hmod0
  have hμπ1 : μ π < 1 :=
    abv_lt_one_of_mem_maximalIdeal_vs μ hμA hπA (by simpa [hπ_def] using An.modulus_mem)
  have hμc'1 : μ c' ≤ 1 := (hμA _).1 hc'A
  have hμc'0 : 0 < μ c' := μ.pos hc'0
  have hz'0 : z' ≠ 0 := by
    intro h0
    apply hmod0
    have : algebraMap L F π = 0 := by rw [← htwo, h0, zero_mul]
    exact (map_eq_zero _).1 this
  have hzbar0 : C.residue ⟨z, hzC⟩ ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hzord
    exact zero_ne_one hzord
  have hz'bar0 : C'.residue ⟨z', hz'C'⟩ ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hz'ord
    exact zero_ne_one hz'ord

  have hdomfacts : ∀ Q ∈ An.dom, Q.IsRational ∧ z ∈ Q.toValuationSubring ∧ z' ∈ Q.toValuationSubring ∧
      (∃ hzA : Q.evalAt z ∈ A, (⟨Q.evalAt z, hzA⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
      Q.evalAt z ≠ 0 ∧ 0 < μ (Q.evalAt z) ∧ μ (Q.evalAt z) < 1 ∧ μ π < μ (Q.evalAt z) ∧
      (∃ m : A, m ∈ IsLocalRing.maximalIdeal A ∧ μ (m : L) < 1 ∧ π = Q.evalAt z * m) := by
    intro Q hQ
    obtain ⟨hrat, hzreg, ⟨hzA, hzmax⟩, hzne, m, hm, hπm⟩ := An.mem_dom Q hQ
    obtain ⟨-, hz'reg, -⟩ := An'.mem_dom Q (hdom ▸ hQ)
    have hμm : μ (m : L) < 1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA m.2 (by simpa using hm)
    have hμz : μ (Q.evalAt z) < 1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA hzA hzmax
    have hπlt : μ π < μ (Q.evalAt z) := by
      rw [hπ_def, hπm, map_mul]
      calc μ (Q.evalAt An.param) * μ (m : L) < μ (Q.evalAt An.param) * 1 :=
            mul_lt_mul_of_pos_left hμm (μ.pos hzne)
        _ = μ (Q.evalAt z) := mul_one _
    exact ⟨hrat, hzreg, hz'reg, ⟨hzA, hzmax⟩, hzne, μ.pos hzne, hμz, hπlt, m, hm, hμm, hπm⟩
  have hcA : ∀ Q ∈ An.dom, Q.evalAt z ∈ A := fun Q hQ => by
    obtain ⟨-, -, -, ⟨h1, -⟩, -⟩ := hdomfacts Q hQ
    exact h1
  have hcmax : ∀ Q (hQ : Q ∈ An.dom), (⟨Q.evalAt z, hcA Q hQ⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    fun Q hQ => by
      obtain ⟨-, -, -, ⟨h1, h2⟩, -⟩ := hdomfacts Q hQ
      exact h2

  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) h hh0
  set Z : Finset (Place L F) := D.support.filter (fun Q => Q ∈ An.dom) with hZ_def
  have hZ : ∀ Q, Q ∈ Z ↔ Q ∈ An.dom ∧ 0 < Q.ord h := by
    intro Q
    rw [hZ_def, Finset.mem_filter, Finsupp.mem_support_iff, hD]
    constructor
    · rintro ⟨hne, hQ⟩
      exact ⟨hQ, lt_of_le_of_ne (hpole Q hQ) (Ne.symm hne)⟩
    · rintro ⟨hQ, hpos⟩
      exact ⟨hpos.ne', hQ⟩
  have hZdom : ∀ Q ∈ Z, Q ∈ An.dom := fun Q hQ => ((hZ Q).1 hQ).1
  set m : Place L F → ℕ := fun Q => (Q.ord h).toNat with hm_def
  have hmQ : ∀ Q ∈ Z, ((m Q : ℕ) : ℤ) = Q.ord h := by
    intro Q hQ
    exact Int.toNat_of_nonneg ((hZ Q).1 hQ).2.le
  have hmpos : ∀ Q ∈ Z, 0 < m Q := by
    intro Q hQ
    have := ((hZ Q).1 hQ).2
    rw [← hmQ Q hQ] at this
    exact_mod_cast this
  set n : ℕ := ∑ Q ∈ Z, m Q with hn_def
  have hordh : ∀ R ∈ An.dom, R ∉ Z → R.ord h = 0 := by
    intro R hR hRZ
    have := hpole R hR
    by_contra hne
    exact hRZ ((hZ R).2 ⟨hR, lt_of_le_of_ne this (Ne.symm hne)⟩)

  have hc0 : ∀ Q ∈ Z, Q.evalAt z ≠ 0 := fun Q hQ => (hdomfacts Q (hZdom Q hQ)).2.2.2.2.1
  set v : Place L F → F := fun Q => algebraMap L F (Q.evalAt z) - z with hv_def
  have hv0 : ∀ Q ∈ Z, v Q ≠ 0 := by
    intro Q hQ h0
    have h1 := An.ord_param_sub Q (hZdom Q hQ)
    have : z - algebraMap L F (Q.evalAt z) = -(v Q) := by rw [hv_def]; ring
    rw [← hz_def, this, h0, neg_zero, Place.ord_zero] at h1
    exact zero_ne_one h1
  have hvord : ∀ Q ∈ Z, ∀ R ∈ An.dom, R.ord (v Q) = if R = Q then 1 else 0 := by
    intro Q hQ R hR
    have hQd := hZdom Q hQ
    obtain ⟨hRrat, hzR, -, -, hzRne, -⟩ := hdomfacts R hR
    obtain ⟨-, -, -, ⟨hzQA, hzQmax⟩, hzQne, -, -, -, mQ, hmQmax, hμmQ, hπmQ⟩ := hdomfacts Q hQd
    split_ifs with hRQ
    · subst hRQ
      have h1 := An.ord_param_sub R hQd
      have : v R = -(z - algebraMap L F (R.evalAt z)) := by rw [hv_def]; ring
      rw [this, Place.ord_neg', ← hz_def] at *
      exact h1
    · have hvR : v Q ∈ R.toValuationSubring := sub_mem (R.algebraMap_mem' _) hzR
      apply R.ord_eq_zero_of_evalAt_ne_zero' hvR
      rw [hv_def, R.evalAt_sub' hRrat (R.algebraMap_mem' _) hzR, R.evalAt_algebraMap']
      intro h0
      apply hRQ
      have hval : R.evalAt z = Q.evalAt z := (sub_eq_zero.1 h0).symm
      obtain ⟨P0, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨Q.evalAt z, hzQA⟩ hzQmax
        (by simpa using hzQne) ⟨mQ, hmQmax, by simpa [hπ_def, hz_def] using hπmQ⟩
      have e1 := huniq R ⟨hR, by simpa [hz_def] using hval⟩
      have e2 := huniq Q ⟨hQd, by simp [hz_def]⟩
      exact e1.trans e2.symm
  have hvR : ∀ Q ∈ Z, ∀ R ∈ An.dom, v Q ∈ R.toValuationSubring := fun Q hQ R hR =>
    sub_mem (R.algebraMap_mem' _) (hdomfacts R hR).2.1

  have hvC : ∀ Q ∈ Z, v Q ∈ C.integers := fun Q hQ =>
    sub_mem ((C.algebraMap_mem_iff _).2 (hcA Q (hZdom Q hQ))) hzC
  have hvres : ∀ Q (hQ : Q ∈ Z), C.residue ⟨v Q, hvC Q hQ⟩ = -C.residue ⟨z, hzC⟩ := by
    intro Q hQ
    have e : (⟨v Q, hvC Q hQ⟩ : C.integers)
        = ⟨algebraMap L F ((⟨Q.evalAt z, hcA Q (hZdom Q hQ)⟩ : A) : L),
            (C.algebraMap_mem_iff _).mpr (⟨Q.evalAt z, hcA Q (hZdom Q hQ)⟩ : A).2⟩ - ⟨z, hzC⟩ :=
      Subtype.ext rfl
    rw [e, map_sub, C.residue_algebraMap, residue_eq_zero_of_mem_maximalIdeal' _ (hcmax Q (hZdom Q hQ)),
      map_zero, zero_sub]
  have hvres0 : ∀ Q (hQ : Q ∈ Z), C.residue ⟨v Q, hvC Q hQ⟩ ≠ 0 := fun Q hQ => by
    rw [hvres Q hQ]; exact neg_ne_zero.2 hzbar0
  set w : Place L F → F := fun Q => if Q ∈ Z then (v Q)⁻¹ else 1 with hw_def
  have hwZ : ∀ Q ∈ Z, w Q = (v Q)⁻¹ := fun Q hQ => by simp [hw_def, hQ]
  have hw0 : ∀ Q, w Q ≠ 0 := fun Q => by
    by_cases hQ : Q ∈ Z
    · rw [hwZ Q hQ]; exact inv_ne_zero (hv0 Q hQ)
    · simp [hw_def, hQ]
  have hwC : ∀ Q, w Q ∈ C.integers := fun Q => by
    by_cases hQ : Q ∈ Z
    · rw [hwZ Q hQ]
      exact inv_mem_of_isUnit' (hvC Q hQ) (C.isUnit_of_residue_ne_zero' (hvC Q hQ) (hvres0 Q hQ))
    · simp only [hw_def, hQ, if_false]; exact one_mem _
  have hwres : ∀ Q, C.residue ⟨w Q, hwC Q⟩ = if Q ∈ Z then (-C.residue ⟨z, hzC⟩)⁻¹ else 1 := by
    intro Q
    by_cases hQ : Q ∈ Z
    · rw [if_pos hQ]
      have hwi : (v Q)⁻¹ ∈ C.integers := (hwZ Q hQ) ▸ hwC Q
      have e : (⟨w Q, hwC Q⟩ : C.integers) = ⟨(v Q)⁻¹, hwi⟩ := Subtype.ext (hwZ Q hQ)
      rw [e, C.residue_inv' (hvC Q hQ) (hvres0 Q hQ) hwi, hvres Q hQ]
    · rw [if_neg hQ]
      have e : (⟨w Q, hwC Q⟩ : C.integers) = 1 := Subtype.ext (by simp [hw_def, hQ])
      rw [e, map_one]

  have hword : ∀ Q ∈ Z, ∀ R ∈ An.dom, R.ord (w Q) = -(if R = Q then 1 else 0) := by
    intro Q hQ R hR
    rw [hwZ Q hQ, Place.ord_inv, hvord Q hQ R hR]
  set gC : F := h * ∏ Q ∈ Z, w Q ^ m Q with hgC_def
  have hgC0 : gC ≠ 0 := mul_ne_zero hh0 (Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ (hw0 Q))
  have hgCmem : gC ∈ C.integers := mul_mem hC (prod_mem fun Q _ => pow_mem (hwC Q) _)

  have hprodmem : (∏ Q ∈ Z, w Q ^ m Q) ∈ C.integers := prod_mem fun Q _ => pow_mem (hwC Q) _
  have hprodres : C.residue ⟨∏ Q ∈ Z, w Q ^ m Q, hprodmem⟩ = ((-C.residue ⟨z, hzC⟩)⁻¹) ^ n := by
    have e : (⟨∏ Q ∈ Z, w Q ^ m Q, hprodmem⟩ : C.integers) = ∏ Q ∈ Z, (⟨w Q, hwC Q⟩ : C.integers) ^ m Q := by
      apply Subtype.ext
      push_cast
      rfl
    rw [e, map_prod]
    simp_rw [map_pow, hwres]
    rw [hn_def, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun Q hQ => by rw [if_pos hQ]
  have hgCres : C.residue ⟨gC, hgCmem⟩ = C.residue ⟨h, hC⟩ * ((-C.residue ⟨z, hzC⟩)⁻¹) ^ n := by
    have e : (⟨gC, hgCmem⟩ : C.integers) = ⟨h, hC⟩ * ⟨∏ Q ∈ Z, w Q ^ m Q, hprodmem⟩ := Subtype.ext rfl
    rw [e, map_mul, hprodres]
  have hgCres0 : C.residue ⟨gC, hgCmem⟩ ≠ 0 := by
    rw [hgCres]
    exact mul_ne_zero hres (pow_ne_zero _ (inv_ne_zero (neg_ne_zero.2 hzbar0)))
  have hgCord : x.ord (C.residue ⟨gC, hgCmem⟩) = a - n := by
    rw [hgCres, x.ord_mul hres (pow_ne_zero _ (inv_ne_zero (neg_ne_zero.2 hzbar0))), ← ha_def,
      x.ord_pow', x.ord_inv, x.ord_neg', hzord]
    ring

  have hgCzf : ∀ R ∈ An.dom, R.ord gC = 0 := by
    intro R hR
    rw [hgC_def, R.ord_mul hh0 (Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ (hw0 Q)),
      R.ord_prod' _ _ (fun Q _ => pow_ne_zero _ (hw0 Q))]
    simp_rw [R.ord_pow']
    have hsum : ∑ Q ∈ Z, (m Q : ℤ) * R.ord (w Q) = -(if R ∈ Z then (m R : ℤ) else 0) := by
      rw [Finset.sum_congr rfl fun Q hQ => by rw [hword Q hQ R hR]]
      simp_rw [mul_neg, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_neg_distrib, Finset.sum_ite_eq Z R (fun Q => (m Q : ℤ))]
    rw [hsum]
    by_cases hRZ : R ∈ Z
    · rw [if_pos hRZ, hmQ R hRZ]; ring
    · rw [if_neg hRZ, hordh R hR hRZ]; ring

  have hslopeC : ∀ R ∈ An.dom, μ (R.evalAt gC) = μ (R.evalAt z) ^ (a - (n : ℤ)) := by
    intro R hR
    obtain ⟨-, -, h3⟩ := abv_evalAt_eq_zpow_of_isAttached μ hμA An C x hattC gC hgCmem hgCres0 hgCzf R hR
    rw [h3, hgCord]

  have hz'unit : IsUnit (⟨z', hz'C'⟩ : C'.integers) := C'.isUnit_of_residue_ne_zero' hz'C' hz'bar0
  have hz'inv : z'⁻¹ ∈ C'.integers := inv_mem_of_isUnit' hz'C' hz'unit
  have hzeq : z = algebraMap L F π * z'⁻¹ := by
    rw [← htwo]; field_simp
  have htQ : ∀ Q ∈ Z, ∃ ht : z * algebraMap L F (Q.evalAt z)⁻¹ ∈ C'.integers, C'.residue ⟨_, ht⟩ = 0 := by
    intro Q hQ
    obtain ⟨-, -, -, -, -, -, -, -, mQ, hmQmax, -, hπmQ⟩ := hdomfacts Q (hZdom Q hQ)
    have hπc : π * (Q.evalAt z)⁻¹ = (mQ : L) := by
      rw [hπmQ, mul_comm (Q.evalAt z) (mQ : L), mul_inv_cancel_right₀ (hc0 Q hQ)]
    have e1 : z * algebraMap L F (Q.evalAt z)⁻¹ = algebraMap L F (mQ : L) * z'⁻¹ := by
      nth_rewrite 1 [hzeq]
      rw [← hπc, map_mul]
      ring
    have hmem : algebraMap L F (mQ : L) * z'⁻¹ ∈ C'.integers :=
      mul_mem ((C'.algebraMap_mem_iff _).2 mQ.2) hz'inv
    refine ⟨e1 ▸ hmem, ?_⟩
    have e2 : (⟨z * algebraMap L F (Q.evalAt z)⁻¹, e1 ▸ hmem⟩ : C'.integers)
        = ⟨algebraMap L F (mQ : L), (C'.algebraMap_mem_iff _).mpr mQ.2⟩ * ⟨z'⁻¹, hz'inv⟩ :=
      Subtype.ext e1
    rw [e2, map_mul, C'.residue_algebraMap, residue_eq_zero_of_mem_maximalIdeal' _ (by simpa using hmQmax),
      map_zero, zero_mul]
  set v' : Place L F → F := fun Q => 1 - z * algebraMap L F (Q.evalAt z)⁻¹ with hv'_def
  have hv'C : ∀ Q ∈ Z, v' Q ∈ C'.integers := fun Q hQ => sub_mem (one_mem _) (htQ Q hQ).1
  have hv'res : ∀ Q (hQ : Q ∈ Z), C'.residue ⟨v' Q, hv'C Q hQ⟩ = 1 := by
    intro Q hQ
    obtain ⟨ht, htres⟩ := htQ Q hQ
    have e : (⟨v' Q, hv'C Q hQ⟩ : C'.integers) = 1 - ⟨_, ht⟩ := Subtype.ext rfl
    rw [e, map_sub, map_one, htres, sub_zero]
  have hv'w : ∀ Q ∈ Z, v' Q = algebraMap L F (Q.evalAt z)⁻¹ * v Q := by
    intro Q hQ
    rw [hv'_def, hv_def]
    simp only []
    rw [map_inv₀]
    field_simp [(map_ne_zero (algebraMap L F)).2 (hc0 Q hQ)]
  have hv'0 : ∀ Q ∈ Z, v' Q ≠ 0 := fun Q hQ => by
    rw [hv'w Q hQ]; exact mul_ne_zero ((map_ne_zero (algebraMap L F)).2 (inv_ne_zero (hc0 Q hQ))) (hv0 Q hQ)
  set w' : Place L F → F := fun Q => if Q ∈ Z then (v' Q)⁻¹ else 1 with hw'_def
  have hw'Z : ∀ Q ∈ Z, w' Q = (v' Q)⁻¹ := fun Q hQ => by simp [hw'_def, hQ]
  have hw'w : ∀ Q, w' Q = (if Q ∈ Z then algebraMap L F (Q.evalAt z) else 1) * w Q := by
    intro Q
    by_cases hQ : Q ∈ Z
    · rw [hw'Z Q hQ, hwZ Q hQ, if_pos hQ, hv'w Q hQ, mul_inv, map_inv₀, inv_inv]
    · simp [hw'_def, hw_def, hQ]
  have hw'0 : ∀ Q, w' Q ≠ 0 := fun Q => by
    by_cases hQ : Q ∈ Z
    · rw [hw'Z Q hQ]; exact inv_ne_zero (hv'0 Q hQ)
    · simp [hw'_def, hQ]
  have hw'C : ∀ Q, w' Q ∈ C'.integers := fun Q => by
    by_cases hQ : Q ∈ Z
    · rw [hw'Z Q hQ]
      exact inv_mem_of_isUnit' (hv'C Q hQ)
        (C'.isUnit_of_residue_ne_zero' (hv'C Q hQ) (by rw [hv'res Q hQ]; exact one_ne_zero))
    · simp only [hw'_def, hQ, if_false]; exact one_mem _
  have hw'res : ∀ Q, C'.residue ⟨w' Q, hw'C Q⟩ = 1 := by
    intro Q
    by_cases hQ : Q ∈ Z
    · have hwi : (v' Q)⁻¹ ∈ C'.integers := (hw'Z Q hQ) ▸ hw'C Q
      have e : (⟨w' Q, hw'C Q⟩ : C'.integers) = ⟨(v' Q)⁻¹, hwi⟩ := Subtype.ext (hw'Z Q hQ)
      rw [e, C'.residue_inv' (hv'C Q hQ) (by rw [hv'res Q hQ]; exact one_ne_zero) hwi, hv'res Q hQ, inv_one]
    · have e : (⟨w' Q, hw'C Q⟩ : C'.integers) = 1 := Subtype.ext (by simp [hw'_def, hQ])
      rw [e, map_one]
  set gC' : F := h' * ∏ Q ∈ Z, w' Q ^ m Q with hgC'_def
  have hgC'mem : gC' ∈ C'.integers := mul_mem hC' (prod_mem fun Q _ => pow_mem (hw'C Q) _)
  have hprodmem' : (∏ Q ∈ Z, w' Q ^ m Q) ∈ C'.integers := prod_mem fun Q _ => pow_mem (hw'C Q) _
  have hprodres' : C'.residue ⟨∏ Q ∈ Z, w' Q ^ m Q, hprodmem'⟩ = 1 := by
    have e : (⟨∏ Q ∈ Z, w' Q ^ m Q, hprodmem'⟩ : C'.integers) = ∏ Q ∈ Z, (⟨w' Q, hw'C Q⟩ : C'.integers) ^ m Q := by
      apply Subtype.ext
      push_cast
      rfl
    rw [e, map_prod]
    simp_rw [map_pow, hw'res, one_pow]
    exact Finset.prod_const_one
  have hgC'res : C'.residue ⟨gC', hgC'mem⟩ = C'.residue ⟨h', hC'⟩ := by
    have e : (⟨gC', hgC'mem⟩ : C'.integers) = ⟨h', hC'⟩ * ⟨∏ Q ∈ Z, w' Q ^ m Q, hprodmem'⟩ := Subtype.ext rfl
    rw [e, map_mul, hprodres', mul_one]
  have hgC'res0 : C'.residue ⟨gC', hgC'mem⟩ ≠ 0 := by rw [hgC'res]; exact hres'

  set κ : L := c'⁻¹ * ∏ Q ∈ Z, Q.evalAt z ^ m Q with hκ_def
  have hκ0 : κ ≠ 0 := mul_ne_zero (inv_ne_zero hc'0) (Finset.prod_ne_zero_iff.2 fun Q hQ => pow_ne_zero _ (hc0 Q hQ))
  have hgC'eq : gC' = algebraMap L F κ * gC := by
    have hprod : (∏ Q ∈ Z, w' Q ^ m Q) = algebraMap L F (∏ Q ∈ Z, Q.evalAt z ^ m Q) * ∏ Q ∈ Z, w Q ^ m Q := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun Q hQ => ?_
      rw [hw'w Q, if_pos hQ, mul_pow, map_pow]
    rw [hgC'_def, hgC_def, hh'_def, hprod, hκ_def, map_mul, map_inv₀]
    ring
  have hgC'zf : ∀ R ∈ An'.dom, R.ord gC' = 0 := by
    intro R hR
    rw [hdom] at hR
    rw [hgC'eq, R.ord_mul ((map_ne_zero _).2 hκ0) hgC0, R.ord_algebraMap' hκ0, hgCzf R hR, add_zero]
  have hgC'ord : x'.ord (C'.residue ⟨gC', hgC'mem⟩) = a' := by rw [hgC'res]

  have hslopeC' : ∀ R ∈ An.dom, μ (R.evalAt gC') = μ (R.evalAt z') ^ a' := by
    intro R hR
    obtain ⟨-, -, h3⟩ := abv_evalAt_eq_zpow_of_isAttached μ hμA An' C' x' hattC' gC' hgC'mem hgC'res0 hgC'zf R
      (hdom ▸ hR)
    rw [h3, hgC'ord]

  have hgCreg : ∀ R ∈ An.dom, gC ∈ R.toValuationSubring := fun R hR =>
    R.mem_of_ord_nonneg hgC0 (hgCzf R hR).symm.le
  have hprofile : ∀ R ∈ An.dom,
      μ (R.evalAt z) ^ (a - (n : ℤ) + a') = μ π ^ a' * (μ κ)⁻¹ := by
    intro R hR
    obtain ⟨hRrat, hzR, hz'R, -, hzRne, hu0, hu1, hπu, -⟩ := hdomfacts R hR
    have hprod : R.evalAt z' * R.evalAt z = π := by
      rw [← R.evalAt_mul' hRrat hz'R hzR, htwo, R.evalAt_algebraMap']
    have hz'val : μ (R.evalAt z') = μ π * (μ (R.evalAt z))⁻¹ := by
      rw [← hprod, map_mul, mul_inv_cancel_right₀ hu0.ne']
    have h1 := hslopeC R hR
    have h2 := hslopeC' R hR
    rw [hz'val] at h2
    have h3 : R.evalAt gC' = κ * R.evalAt gC := by
      rw [hgC'eq, R.evalAt_mul' hRrat (R.algebraMap_mem' _) (hgCreg R hR), R.evalAt_algebraMap']
    rw [h3, map_mul, h1, mul_zpow, inv_zpow, ← div_eq_mul_inv] at h2

    have hua' : μ (R.evalAt z) ^ a' ≠ 0 := zpow_ne_zero _ hu0.ne'
    have hμκ0 : μ κ ≠ 0 := (μ.pos hκ0).ne'
    rw [eq_div_iff hua'] at h2
    rw [zpow_add₀ hu0.ne', eq_mul_inv_iff_mul_eq₀ hμκ0]
    calc μ (R.evalAt z) ^ (a - (n : ℤ)) * μ (R.evalAt z) ^ a' * μ κ
        = μ κ * μ (R.evalAt z) ^ (a - (n : ℤ)) * μ (R.evalAt z) ^ a' := by ring
      _ = μ π ^ a' := h2

  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := hwide
  have hexp : a - (n : ℤ) + a' = 0 := by
    by_contra hne0
    apply hne
    have hu1 := (hdomfacts Q₁ hQ₁).2.2.2.2.2.1
    have hu2 := (hdomfacts Q₂ hQ₂).2.2.2.2.2.1
    have h12 : μ (Q₁.evalAt z) ^ (a - (n : ℤ) + a') = μ (Q₂.evalAt z) ^ (a - (n : ℤ) + a') := by
      rw [hprofile Q₁ hQ₁, hprofile Q₂ hQ₂]
    exact (zpow_left_inj₀ hu1.le hu2.le hne0).1 h12
  have hn : (n : ℤ) = a + a' := by omega

  have hμκ : μ κ = μ π ^ a' := by
    have h := hprofile Q₁ hQ₁
    rw [hexp, zpow_zero] at h
    have hμκ0 : μ κ ≠ 0 := (μ.pos hκ0).ne'
    field_simp at h
    linarith [h]

  have hzunit : IsUnit (⟨z, hzC⟩ : C.integers) := C.isUnit_of_residue_ne_zero' hzC hzbar0
  have hzinvC : z⁻¹ ∈ C.integers := inv_mem_of_isUnit' hzC hzunit
  have hz0 : z ≠ 0 := by
    intro h0; apply hmod0
    have : algebraMap L F π = 0 := by rw [← htwo, h0, mul_zero]
    exact (map_eq_zero _).1 this
  have hzpowC : ∀ k : ℤ, z ^ k ∈ C.integers := by
    intro k
    rcases Int.eq_nat_or_neg k with ⟨n0, rfl | rfl⟩
    · rw [zpow_natCast]; exact pow_mem hzC _
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hzinvC _
  have hzpowres : ∀ k : ℤ, C.residue ⟨z ^ k, hzpowC k⟩ = (C.residue ⟨z, hzC⟩) ^ k := by
    intro k
    rcases Int.eq_nat_or_neg k with ⟨n0, rfl | rfl⟩
    · have e : (⟨z ^ (n0 : ℤ), hzpowC n0⟩ : C.integers) = ⟨z, hzC⟩ ^ n0 := Subtype.ext (by push_cast; rw [zpow_natCast])
      rw [e, map_pow, zpow_natCast]
    · have e : (⟨z ^ (-(n0 : ℤ)), hzpowC (-(n0 : ℤ))⟩ : C.integers) = ⟨z⁻¹, hzinvC⟩ ^ n0 :=
        Subtype.ext (by push_cast; rw [zpow_neg, zpow_natCast, inv_pow])
      rw [e, map_pow, C.residue_inv' hzC hzbar0 hzinvC, zpow_neg, zpow_natCast, inv_pow]
  have hz'inv' : z'⁻¹ ∈ C'.integers := hz'inv
  have hz'powC' : ∀ k : ℤ, z' ^ k ∈ C'.integers := by
    intro k
    rcases Int.eq_nat_or_neg k with ⟨n0, rfl | rfl⟩
    · rw [zpow_natCast]; exact pow_mem hz'C' _
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hz'inv' _
  have hz'powres : ∀ k : ℤ, C'.residue ⟨z' ^ k, hz'powC' k⟩ = (C'.residue ⟨z', hz'C'⟩) ^ k := by
    intro k
    rcases Int.eq_nat_or_neg k with ⟨n0, rfl | rfl⟩
    · have e : (⟨z' ^ (n0 : ℤ), hz'powC' n0⟩ : C'.integers) = ⟨z', hz'C'⟩ ^ n0 := Subtype.ext (by push_cast; rw [zpow_natCast])
      rw [e, map_pow, zpow_natCast]
    · have e : (⟨z' ^ (-(n0 : ℤ)), hz'powC' (-(n0 : ℤ))⟩ : C'.integers) = ⟨z'⁻¹, hz'inv'⟩ ^ n0 :=
        Subtype.ext (by push_cast; rw [zpow_neg, zpow_natCast, inv_pow])
      rw [e, map_pow, C'.residue_inv' hz'C' hz'bar0 hz'inv', zpow_neg, zpow_natCast, inv_pow]

  set g : F := gC * (-z) ^ n * z ^ (-a) with hg_def
  have hnegzC : (-z) ^ n ∈ C.integers := pow_mem (neg_mem hzC) _
  have hgmem : g ∈ C.integers := mul_mem (mul_mem hgCmem hnegzC) (hzpowC (-a))
  have hgres : C.residue ⟨g, hgmem⟩ = C.residue ⟨h, hC⟩ * (C.residue ⟨z, hzC⟩) ^ (-a) := by
    have e : (⟨g, hgmem⟩ : C.integers) = ⟨gC, hgCmem⟩ * (-⟨z, hzC⟩) ^ n * ⟨z ^ (-a), hzpowC (-a)⟩ :=
      Subtype.ext (by push_cast; rfl)
    rw [e, map_mul, map_mul, map_pow, map_neg, hgCres, hzpowres, inv_pow, mul_assoc (C.residue ⟨h, hC⟩),
      inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 hzbar0)), mul_one]
  have hgres0 : C.residue ⟨g, hgmem⟩ ≠ 0 := by
    rw [hgres]; exact mul_ne_zero hres (zpow_ne_zero _ hzbar0)
  have hgord : x.ord (C.residue ⟨g, hgmem⟩) = 0 := by
    rw [hgres, x.ord_mul hres (zpow_ne_zero _ hzbar0), x.ord_zpow, hzord, ← ha_def]; ring
  have hordz : ∀ Q ∈ An.dom, Q.ord z = 0 := by
    intro Q hQ
    obtain ⟨-, hzQ, -, -, hzQne, -⟩ := hdomfacts Q hQ
    exact Place.ord_eq_zero_of_evalAt_ne_zero' Q hzQ hzQne
  have hg0' : g ≠ 0 := mul_ne_zero (mul_ne_zero hgC0 (pow_ne_zero _ (neg_ne_zero.2 hz0))) (zpow_ne_zero _ hz0)
  have hgzf : ∀ Q ∈ An.dom, Q.ord g = 0 := by
    intro Q hQ
    rw [hg_def, Q.ord_mul (mul_ne_zero hgC0 (pow_ne_zero _ (neg_ne_zero.2 hz0))) (zpow_ne_zero _ hz0),
      Q.ord_mul hgC0 (pow_ne_zero _ (neg_ne_zero.2 hz0)), hgCzf Q hQ, Q.ord_pow', Q.ord_neg', Q.ord_zpow, hordz Q hQ]
    ring

  set κB : L := κ⁻¹ * (-1) ^ n * π ^ a' with hκB_def
  have hπ0 : π ≠ 0 := hmod0
  have hκB0 : κB ≠ 0 := mul_ne_zero (mul_ne_zero (inv_ne_zero hκ0) (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))) (zpow_ne_zero _ hπ0)
  have hμκB : μ κB = 1 := by
    rw [hκB_def, map_mul, map_mul, map_inv₀, map_pow, map_zpow₀, μ.map_neg, μ.map_one, one_pow, mul_one, hμκ,
      inv_mul_cancel₀ (zpow_ne_zero _ hμπ0.ne')]

  have hgeq : (algebraMap L F κB)⁻¹ * g = gC' * z' ^ (-a') := by
    have ha_eq : -a = a' - (n : ℤ) := by omega
    have hzz' : z = algebraMap L F π * z'⁻¹ := hzeq
    have hαπ : algebraMap L F π ≠ 0 := (map_ne_zero _).2 hπ0
    have hακ : algebraMap L F κ ≠ 0 := (map_ne_zero _).2 hκ0
    rw [hg_def, hgC'eq, ha_eq, zpow_sub₀ hz0, zpow_natCast, hκB_def]
    rw [map_mul, map_mul, map_inv₀, map_pow, map_neg, map_one, map_zpow₀]

    have hza' : z ^ a' = (algebraMap L F π) ^ a' * z' ^ (-a') := by
      rw [hzz', mul_zpow, inv_zpow']
    rw [hza']
    have hnegz : (-z) ^ n = (-1) ^ n * z ^ n := by rw [neg_eq_neg_one_mul, mul_pow]
    rw [hnegz]
    have hzn : z ^ n ≠ 0 := pow_ne_zero _ hz0
    have h1n : ((-1 : F)) ^ n ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    field_simp
  have hgC'B : (algebraMap L F κB)⁻¹ * g ∈ C'.integers := by
    rw [hgeq]; exact mul_mem hgC'mem (hz'powC' (-a'))
  have hgres'B : C'.residue ⟨(algebraMap L F κB)⁻¹ * g, hgC'B⟩
      = C'.residue ⟨h', hC'⟩ * (C'.residue ⟨z', hz'C'⟩) ^ (-a') := by
    have e : (⟨(algebraMap L F κB)⁻¹ * g, hgC'B⟩ : C'.integers) = ⟨gC', hgC'mem⟩ * ⟨z' ^ (-a'), hz'powC' (-a')⟩ :=
      Subtype.ext hgeq
    rw [e, map_mul, hgC'res, hz'powres]
  have hgres'B0 : C'.residue ⟨(algebraMap L F κB)⁻¹ * g, hgC'B⟩ ≠ 0 := by
    rw [hgres'B]; exact mul_ne_zero hres' (zpow_ne_zero _ hz'bar0)
  have hgord'B : x'.ord (C'.residue ⟨(algebraMap L F κB)⁻¹ * g, hgC'B⟩) = 0 := by
    rw [hgres'B, x'.ord_mul hres' (zpow_ne_zero _ hz'bar0), x'.ord_zpow, hz'ord, ← ha'_def]; ring

  obtain ⟨hgRA, hgRres, hgRunit'⟩ :=
    Annulus.residue_evalAt_eq_evalAt_residue_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0 htwo
      C x hattC hx C' x' hattC' hwide0 g (fun Q hQ => (hgzf Q hQ).ge) hgmem hgres0 κB hμκB hgC'B hgres'B0 R hR
  have hgRunit := hgRunit' hgord

  have hRZ : R ∉ Z := by
    intro hRZ
    have := hout R hR (ne_of_gt ((hZ R).1 hRZ).2)
    exact lt_irrefl _ this
  obtain ⟨hRrat, hzR, -, -, hzRne, hu0, -, -, -⟩ := hdomfacts R hR

  set uf : Place L F → F := fun Q => 1 - algebraMap L F (Q.evalAt z) * z⁻¹ with huf_def
  have hufw : ∀ Q ∈ Z, uf Q = (-z * w Q)⁻¹ := by
    intro Q hQ
    rw [hwZ Q hQ, huf_def, hv_def]
    simp only []
    field_simp
    ring
  have hident : g * ∏ Q ∈ Z, uf Q ^ m Q = h * z ^ (-a) := by
    have hprod : (∏ Q ∈ Z, uf Q ^ m Q) * ((-z) ^ n * ∏ Q ∈ Z, w Q ^ m Q) = 1 := by
      rw [hn_def, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun Q hQ => ?_
      rw [hufw Q hQ, ← mul_pow, ← mul_pow, inv_mul_cancel₀ (mul_ne_zero (neg_ne_zero.2 hz0) (hw0 Q)), one_pow]
    calc g * ∏ Q ∈ Z, uf Q ^ m Q
        = h * z ^ (-a) * ((∏ Q ∈ Z, uf Q ^ m Q) * ((-z) ^ n * ∏ Q ∈ Z, w Q ^ m Q)) := by rw [hg_def, hgC_def]; ring
      _ = h * z ^ (-a) := by rw [hprod, mul_one]

  have hzinvR : z⁻¹ ∈ R.toValuationSubring :=
    inv_mem_of_isUnit' hzR (Place.isUnit_of_ord_eq_zero' R hzR hz0 (hordz R hR))
  have hufR : ∀ Q ∈ Z, uf Q ∈ R.toValuationSubring := fun Q _ =>
    sub_mem (one_mem _) (mul_mem (R.algebraMap_mem' _) hzinvR)
  have hzinvval : R.evalAt z⁻¹ = (R.evalAt z)⁻¹ := by
    have h1 : R.evalAt (z * z⁻¹) = R.evalAt z * R.evalAt z⁻¹ := Place.evalAt_mul' R hRrat hzR hzinvR
    rw [mul_inv_cancel₀ hz0, show (1 : F) = algebraMap L F 1 from (map_one _).symm, Place.evalAt_algebraMap'] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm).symm ▸ rfl
  have hufval : ∀ Q ∈ Z, R.evalAt (uf Q) = 1 - Q.evalAt z * (R.evalAt z)⁻¹ := by
    intro Q hQ
    rw [huf_def]
    simp only []
    rw [Place.evalAt_sub' R hRrat (one_mem _) (mul_mem (R.algebraMap_mem' _) hzinvR),
      show (1 : F) = algebraMap L F 1 from (map_one _).symm, Place.evalAt_algebraMap',
      Place.evalAt_mul' R hRrat (R.algebraMap_mem' _) hzinvR, Place.evalAt_algebraMap', hzinvval]

  have hufunit : ∀ Q ∈ Z, ∃ hA : R.evalAt (uf Q) ∈ A, IsUnit (⟨_, hA⟩ : A) ∧ IsLocalRing.residue A ⟨_, hA⟩ = 1 := by
    intro Q hQ
    have hlt : μ (Q.evalAt z * (R.evalAt z)⁻¹) < 1 := by
      rw [map_mul, map_inv₀]
      exact (mul_inv_lt_iff₀ hu0).2 (by rw [one_mul]; exact hout Q (hZdom Q hQ) (ne_of_gt ((hZ Q).1 hQ).2))
    have hεA : Q.evalAt z * (R.evalAt z)⁻¹ ∈ A := (hμA _).2 hlt.le
    have hεmax : (⟨_, hεA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; intro hu
      have := abv_eq_one_of_isUnit_vs μ hμA hεA hu; linarith
    have hA : R.evalAt (uf Q) ∈ A := by rw [hufval Q hQ]; exact sub_mem (one_mem _) hεA
    refine ⟨hA, ?_, ?_⟩
    · have hres1 : IsLocalRing.residue A ⟨_, hA⟩ = 1 := by
        have e : (⟨R.evalAt (uf Q), hA⟩ : A) = 1 - ⟨_, hεA⟩ := Subtype.ext (by push_cast; exact hufval Q hQ)
        rw [e, map_sub, map_one, (IsLocalRing.residue_eq_zero_iff _).2 hεmax, sub_zero]
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by rw [hres1]; exact one_ne_zero)
    · have e : (⟨R.evalAt (uf Q), hA⟩ : A) = 1 - ⟨_, hεA⟩ := Subtype.ext (by push_cast; exact hufval Q hQ)
      rw [e, map_sub, map_one, (IsLocalRing.residue_eq_zero_iff _).2 hεmax, sub_zero]

  have hgR : g ∈ R.toValuationSubring := Place.mem_of_ord_nonneg R hg0' (hgzf R hR).ge
  have hhR : h ∈ R.toValuationSubring := Place.mem_of_ord_nonneg R hh0 (hpole R hR)
  obtain ⟨hprodR, hprodval⟩ := Place.evalAt_prod' R hRrat Z (fun Q => uf Q ^ m Q) (fun Q hQ => pow_mem (hufR Q hQ) _)
  have hzpowR : z ^ (-a) ∈ R.toValuationSubring := by
    rcases Int.eq_nat_or_neg (-a) with ⟨n0, h0 | h0⟩
    · rw [h0, zpow_natCast]; exact pow_mem hzR _
    · rw [h0, zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hzinvR _
  have hzpowval : R.evalAt (z ^ (-a)) = (R.evalAt z) ^ (-a) := by
    rcases Int.eq_nat_or_neg (-a) with ⟨n0, h0 | h0⟩
    · rw [h0, zpow_natCast, Place.evalAt_pow' R hRrat hzR, zpow_natCast]
    · rw [h0, zpow_neg, zpow_natCast, ← inv_pow, Place.evalAt_pow' R hRrat hzinvR, hzinvval, inv_pow, zpow_neg, zpow_natCast]
  have hLHS : R.evalAt h * (R.evalAt z) ^ (-a) = R.evalAt g * ∏ Q ∈ Z, R.evalAt (uf Q) ^ m Q := by
    have h1 : R.evalAt (h * z ^ (-a)) = R.evalAt h * (R.evalAt z) ^ (-a) := by
      rw [Place.evalAt_mul' R hRrat hhR hzpowR, hzpowval]
    have h2 : R.evalAt (g * ∏ Q ∈ Z, uf Q ^ m Q) = R.evalAt g * ∏ Q ∈ Z, R.evalAt (uf Q) ^ m Q := by
      rw [Place.evalAt_mul' R hRrat hgR hprodR, hprodval]
      congr 1
      exact Finset.prod_congr rfl fun Q hQ => by rw [Place.evalAt_pow' R hRrat (hufR Q hQ)]
    rw [← h1, ← hident, h2]

  have hprodAll : ∀ S : Finset (Place L F), S ⊆ Z → ∃ hA : (∏ Q ∈ S, R.evalAt (uf Q) ^ m Q) ∈ A,
      IsUnit (⟨_, hA⟩ : A) ∧ IsLocalRing.residue A ⟨_, hA⟩ = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      have hA : (∏ Q ∈ (∅ : Finset (Place L F)), R.evalAt (uf Q) ^ m Q) ∈ A := by
        rw [Finset.prod_empty]; exact one_mem _
      have e : (⟨_, hA⟩ : A) = 1 := Subtype.ext (by push_cast; exact Finset.prod_empty)
      exact ⟨hA, by rw [e]; exact isUnit_one, by rw [e, map_one]⟩
    | insert Q0 S hQ0 ih =>
      intro hsub
      obtain ⟨hA0, hu0', hr0⟩ := hufunit Q0 (hsub (Finset.mem_insert_self _ _))
      obtain ⟨hAS, huS, hrS⟩ := ih (fun Q hQ => hsub (Finset.mem_insert_of_mem hQ))
      have hA : (∏ Q ∈ insert Q0 S, R.evalAt (uf Q) ^ m Q) ∈ A := by
        rw [Finset.prod_insert hQ0]; exact mul_mem (pow_mem hA0 _) hAS
      have e : (⟨_, hA⟩ : A) = ⟨_, hA0⟩ ^ m Q0 * ⟨_, hAS⟩ :=
        Subtype.ext (by push_cast; exact Finset.prod_insert hQ0)
      refine ⟨hA, ?_, ?_⟩
      · rw [e]; exact (hu0'.pow _).mul huS
      · rw [e, map_mul, map_pow, hr0, hrS, one_pow, one_mul]
  obtain ⟨hPA, hPunit, hPres⟩ := hprodAll Z (Finset.Subset.refl _)

  have hmemF : R.evalAt h * (R.evalAt z) ^ (-a) ∈ A := by rw [hLHS]; exact mul_mem hgRA hPA
  have eF : (⟨R.evalAt h * (R.evalAt z) ^ (-a), hmemF⟩ : A) = ⟨_, hgRA⟩ * ⟨_, hPA⟩ := Subtype.ext hLHS
  refine ⟨hmemF, ?_, ?_⟩
  · rw [eF]; exact hgRunit.mul hPunit
  · rw [eF, map_mul, hgRres, hPres, mul_one, hgres]

end S_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt (solution)
