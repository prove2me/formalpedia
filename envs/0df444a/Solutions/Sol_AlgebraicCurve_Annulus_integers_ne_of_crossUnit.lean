-- Prove2me | solution 1 for AlgebraicCurve.Annulus.integers_ne_of_crossUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4f2b83ac-2c55-5d2b-8544-2740bd45c212

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_integers_ne_of_crossUnit
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace FarDistinct

section ValGroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem pow_lt_pow_of_lt {a b : Γ} (hb : 0 < b) (hab : a < b) : ∀ n : ℕ, n ≠ 0 → a ^ n < b ^ n := by
  intro n hn
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simpa using hab
    · calc a ^ (n + 1) = a ^ n * a := pow_succ a n
        _ ≤ b ^ n * a := mul_le_mul_left (ih hpos.ne').le a
        _ < b ^ n * b := mul_lt_mul_of_pos_left hab (pow_pos hb n)
        _ = b ^ (n + 1) := (pow_succ b n).symm

theorem zpow_exp_eq_zero {a b : Γ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) {n : ℤ} (h : a ^ n = b ^ n) :
    n = 0 := by
  by_contra hn

  have key : ∀ {c d : Γ}, 0 < c → 0 < d → c ≠ d → ∀ N : ℕ, N ≠ 0 → c ^ N ≠ d ^ N := by
    intro c d hc hd hcd N hN
    rcases lt_or_gt_of_ne hcd with hlt | hgt
    · exact (pow_lt_pow_of_lt hd hlt N hN).ne
    · exact (pow_lt_pow_of_lt hc hgt N hN).ne'
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hN : n.natAbs ≠ 0 := by omega
    apply key ha hb hab n.natAbs hN
    have : (n.natAbs : ℤ) = -n := by omega
    have h' : a ^ (-n) = b ^ (-n) := by rw [zpow_neg, zpow_neg, h]
    rw [← this, zpow_natCast, zpow_natCast] at h'
    exact h'
  · have hN : n.natAbs ≠ 0 := by omega
    apply key ha hb hab n.natAbs hN
    have : (n.natAbs : ℤ) = n := by omega
    rw [← this, zpow_natCast, zpow_natCast] at h
    exact h

end ValGroup

section Main

variable {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]

theorem v_eq_one_of_isUnit {X : L} (h : ∃ hX : X ∈ A, IsUnit (⟨X, hX⟩ : ↥A)) : A.valuation X = 1 := by
  obtain ⟨hX, hu⟩ := h
  exact (A.valuation_eq_one_iff ⟨X, hX⟩).mp hu

theorem place_data (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    P.IsRational ∧ An.param ∈ P.toValuationSubring ∧ P.evalAt An.param ≠ 0 ∧
      0 < A.valuation (P.evalAt An.param) ∧ A.valuation (P.evalAt An.param) < 1 ∧
      A.valuation (An.modulus : L) < A.valuation (P.evalAt An.param) := by
  obtain ⟨hrat, hmem, ⟨hA, hmax⟩, h0, m, hm, hmod⟩ := An.mem_dom P hP
  refine ⟨hrat, hmem, h0, (Valuation.pos_iff _).2 h0, (A.valuation_lt_one_iff ⟨_, hA⟩).1 hmax, ?_⟩
  rw [hmod, Valuation.map_mul]
  calc A.valuation (P.evalAt An.param) * A.valuation (m : L)
      < A.valuation (P.evalAt An.param) * 1 :=
        mul_lt_mul_of_pos_left ((A.valuation_lt_one_iff m).1 hm) ((Valuation.pos_iff _).2 h0)
    _ = A.valuation (P.evalAt An.param) := mul_one _

theorem exists_two_radii [IsAlgClosed L] (An : Annulus A F) (h0 : (An.modulus : L) ≠ 0) :
    ∃ P₁ ∈ An.dom, ∃ P₂ ∈ An.dom, A.valuation (P₁.evalAt An.param) ≠ A.valuation (P₂.evalAt An.param) := by
  set π : L := (An.modulus : L) with hπ
  have hπ1 : A.valuation π < 1 := (A.valuation_lt_one_iff An.modulus).1 An.modulus_mem
  have hπ0 : 0 < A.valuation π := (Valuation.pos_iff _).2 h0
  obtain ⟨c₁, hc₁⟩ := IsAlgClosed.exists_pow_nat_eq π (n := 2) (by norm_num)
  obtain ⟨c₂, hc₂⟩ := IsAlgClosed.exists_pow_nat_eq π (n := 3) (by norm_num)
  have hv₁ : A.valuation c₁ ^ 2 = A.valuation π := by rw [← Valuation.map_pow, hc₁]
  have hv₂ : A.valuation c₂ ^ 3 = A.valuation π := by rw [← Valuation.map_pow, hc₂]
  have hc₁0 : c₁ ≠ 0 := by rintro rfl; apply h0; rw [← hc₁]; norm_num
  have hc₂0 : c₂ ≠ 0 := by rintro rfl; apply h0; rw [← hc₂]; norm_num
  have hlt1 : ∀ {c : L} {n : ℕ}, A.valuation c ^ n = A.valuation π → A.valuation c < 1 := by
    intro c n h
    by_contra hge
    rw [not_lt] at hge
    have : (1 : A.ValueGroup) ≤ A.valuation c ^ n := one_le_pow₀ hge
    rw [h] at this
    exact absurd hπ1 (not_lt.2 this)
  have hc₁1 := hlt1 hv₁
  have hc₂1 := hlt1 hv₂
  have hmemA : ∀ {c : L}, A.valuation c < 1 → c ∈ A := fun h => (A.valuation_le_one_iff _).1 h.le
  have hc₁A := hmemA hc₁1
  have hc₂A := hmemA hc₂1

  have hadm₁ : ∃ m ∈ maximalIdeal ↥A, (An.modulus : L) = (⟨c₁, hc₁A⟩ : ↥A) * m :=
    ⟨⟨c₁, hc₁A⟩, (A.valuation_lt_one_iff _).2 hc₁1, by rw [← hπ, ← hc₁]; simp [pow_two]⟩
  have hadm₂ : ∃ m ∈ maximalIdeal ↥A, (An.modulus : L) = (⟨c₂, hc₂A⟩ : ↥A) * m := by
    refine ⟨⟨c₂ ^ 2, pow_mem hc₂A 2⟩, (A.valuation_lt_one_iff _).2 ?_, by rw [← hπ, ← hc₂]; simp; ring⟩
    show A.valuation (c₂ ^ 2) < 1
    rw [Valuation.map_pow]; exact pow_lt_one₀ zero_le' hc₂1 two_ne_zero
  obtain ⟨P₁, ⟨hP₁, hz₁⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₁, hc₁A⟩ ((A.valuation_lt_one_iff _).2 hc₁1) hc₁0 hadm₁
  obtain ⟨P₂, ⟨hP₂, hz₂⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₂, hc₂A⟩ ((A.valuation_lt_one_iff _).2 hc₂1) hc₂0 hadm₂
  refine ⟨P₁, hP₁, P₂, hP₂, ?_⟩
  rw [hz₁, hz₂]
  show A.valuation c₁ ≠ A.valuation c₂
  intro heq

  have h2 : A.valuation c₂ ^ 2 = A.valuation c₂ ^ 3 := by rw [hv₂, ← hv₁, heq]
  have hne : A.valuation c₂ ≠ 0 := (Valuation.ne_zero_iff _).2 hc₂0
  have : A.valuation c₂ ^ 2 * 1 = A.valuation c₂ ^ 2 * A.valuation c₂ := by rw [mul_one, ← pow_succ, ← h2]
  have := mul_left_cancel₀ (pow_ne_zero 2 hne) this
  exact absurd hc₂1 (by rw [← this]; exact lt_irrefl 1)

theorem v_evalAt_param_recip (An An' : Annulus A F) (hd : An'.dom = An.dom)
    (hp : An'.param * An.param = algebraMap L F (An.modulus : L)) {P : Place L F} (hP : P ∈ An.dom) :
    A.valuation (P.evalAt An'.param) * A.valuation (P.evalAt An.param) = A.valuation (An.modulus : L) := by
  obtain ⟨hrat, hmem, -, -⟩ := An.mem_dom P hP
  obtain ⟨-, hmem', -, -⟩ := An'.mem_dom P (hd ▸ hP)
  rw [← Valuation.map_mul, ← Place.evalAt_mul P hrat hmem' hmem, hp, Place.evalAt_algebraMap]

theorem ord_eq_zero_of_isUnit_evalAt {P : Place L F} (hrat : P.IsRational) {f : F}
    (hmem : f ∈ P.toValuationSubring) (hu : ∃ h : P.evalAt f ∈ A, IsUnit (⟨_, h⟩ : ↥A)) : P.ord f = 0 := by
  obtain ⟨hA, hunit⟩ := hu
  have hne : P.evalAt f ≠ 0 := fun h0 => by
    apply not_isUnit_zero (M₀ := ↥A)
    have : (⟨P.evalAt f, hA⟩ : ↥A) = 0 := Subtype.ext h0
    rwa [this] at hunit
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hne
    have : (0 : F) = algebraMap L F 0 := (map_zero _).symm
    rw [this, Place.evalAt_algebraMap]
  by_contra hord
  rcases lt_or_gt_of_ne hord with hlt | hgt
  ·
    have hinv : f⁻¹ ∈ P.toValuationSubring :=
      Place.mem_of_ord_nonneg P (inv_ne_zero hf0) (by rw [Place.ord_inv]; omega)
    have hu' : IsUnit (⟨f, hmem⟩ : ↥P.toValuationSubring) :=
      ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩
    obtain ⟨u, hu'⟩ := hu'
    have := Place.ord_coe_unit P u
    rw [hu'] at this
    exact hord this
  · have : 1 ≤ P.ord f := by omega
    exact hne ((Place.evalAt_eq_zero_iff_one_le_ord P hrat hf0 hmem).2 this)

end Main

end FarDistinct

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x x' : Place (ResidueField A) Fbar) (hxx' : x ≠ x')
    {FI FI' : Type*} [Field FI] [Algebra (ResidueField A) FI] [Field FI'] [Algebra (ResidueField A) FI']
    (Rx : RegularProlongation A F FI) (Rx' : RegularProlongation A F FI')
    (b : Place (ResidueField A) FI) (b' : Place (ResidueField A) FI')
    (An An' Bn Bn' : Annulus A F)

    (hAd : An'.dom = An.dom) (hAp : An'.param * An.param = algebraMap L F (An.modulus : L))
    (hBd : Bn'.dom = Bn.dom) (hBp : Bn'.param * Bn.param = algebraMap L F (Bn.modulus : L))
    (hAm0 : (An.modulus : L) ≠ 0) (hBm0 : (Bn.modulus : L) ≠ 0)

    (hAnear : ∃ hz : An.param ∈ R.integers, x.ord (R.residue ⟨An.param, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
        ∀ P ∈ An.dom, ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x.ord (R.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (hBnear : ∃ hz : Bn.param ∈ R.integers, x'.ord (R.residue ⟨Bn.param, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ Bn.dom, P.ord f = 0) →
        ∀ P ∈ Bn.dom, ∃ h : P.evalAt f * (P.evalAt Bn.param) ^ (-(x'.ord (R.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    (hAfar : ∃ hz : An'.param ∈ Rx.integers, b.ord (Rx.residue ⟨An'.param, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ Rx.integers), Rx.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord f = 0) →
        ∀ P ∈ An'.dom, ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(b.ord (Rx.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (hBfar : ∃ hz : Bn'.param ∈ Rx'.integers, b'.ord (Rx'.residue ⟨Bn'.param, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ Rx'.integers), Rx'.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ Bn'.dom, P.ord f = 0) →
        ∀ P ∈ Bn'.dom, ∃ h : P.evalAt f * (P.evalAt Bn'.param) ^ (-(b'.ord (Rx'.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    (g : F) (hg : g ∈ R.integers) (hg0 : R.residue ⟨g, hg⟩ ≠ 0) (hgx : x.ord (R.residue ⟨g, hg⟩) ≠ 0)
    (hgA : ∀ P ∈ An.dom, P.ord g = 0)
    (hgB : ∀ P ∈ Bn.dom, g ∈ P.toValuationSubring ∧ ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A)) :
    Rx.integers ≠ Rx'.integers := by
  classical
  intro hO
  have hg_ne : g ≠ 0 := by
    intro h0; apply hg0
    have h' : (⟨g, hg⟩ : ↥R.integers) = 0 := Subtype.ext h0
    rw [h', map_zero]

  obtain ⟨c, hcg, hcres⟩ := Rx.exists_smul_mem g hg_ne
  have hc0 : c ≠ 0 := by
    intro h; apply hcres
    have h' : (⟨c • g, hcg⟩ : ↥Rx.integers) = 0 := Subtype.ext (by simp [h])
    rw [h', map_zero]
  have hcg' : c • g ∈ Rx'.integers := hO ▸ hcg
  have hcres' : Rx'.residue ⟨c • g, hcg'⟩ ≠ 0 := by
    apply Rx'.residue_ne_zero_of_isUnit
    have hu := (Rx.isUnit_of_residue_ne_zero hcres).map (ValuationSubring.inclusion Rx.integers Rx'.integers hO.le)
    have e : (ValuationSubring.inclusion Rx.integers Rx'.integers hO.le) ⟨c • g, hcg⟩ = ⟨c • g, hcg'⟩ := Subtype.ext rfl
    rw [e] at hu
    exact hu
  have hsmul : c • g = algebraMap L F c * g := Algebra.smul_def c g
  have hac0 : algebraMap L F c ≠ 0 := (map_ne_zero _).2 hc0
  have hord_cg : ∀ P : Place L F, P.ord g = 0 → P.ord (c • g) = 0 := fun P hP => by
    rw [hsmul, Place.ord_mul P hac0 hg_ne, Place.ord_algebraMap, hP, add_zero]
  have heval_cg : ∀ P : Place L F, P.IsRational → g ∈ P.toValuationSubring →
      P.evalAt (c • g) = c * P.evalAt g := fun P hP hgP => by
    rw [hsmul, Place.evalAt_mul P hP (P.algebraMap_mem' c) hgP, Place.evalAt_algebraMap]

  obtain ⟨hzB', -, hBlaw⟩ := hBfar
  have hgB0 : ∀ P ∈ Bn.dom, P.ord g = 0 := fun P hP =>
    FarDistinct.ord_eq_zero_of_isUnit_evalAt A (Bn.mem_dom P hP).1 (hgB P hP).1 (hgB P hP).2
  have hBval : ∀ P ∈ Bn.dom, A.valuation c * A.valuation (P.evalAt Bn.param) ^ b'.ord (Rx'.residue ⟨c • g, hcg'⟩) =
      A.valuation (Bn.modulus : L) ^ b'.ord (Rx'.residue ⟨c • g, hcg'⟩) := by
    intro P hP
    obtain ⟨hrat, hzmem, hz0, hzpos, -, -⟩ := FarDistinct.place_data A Bn hP
    have hP' : P ∈ Bn'.dom := by rw [hBd]; exact hP
    have h1 := FarDistinct.v_eq_one_of_isUnit A
      (hBlaw (c • g) hcg' hcres' (fun Q hQ => hord_cg Q (hgB0 Q (by rw [← hBd]; exact hQ))) P hP')
    have h2 := FarDistinct.v_eq_one_of_isUnit A (hgB P hP).2
    have hrec := FarDistinct.v_evalAt_param_recip A Bn Bn' hBd hBp hP
    have hz'0 : A.valuation (P.evalAt Bn'.param) ≠ 0 := by
      intro h; rw [h, zero_mul] at hrec; exact (Valuation.ne_zero_iff _).2 hBm0 hrec.symm
    rw [heval_cg P hrat (hgB P hP).1, Valuation.map_mul, Valuation.map_mul, h2, mul_one, map_zpow₀, zpow_neg,
      mul_inv_eq_one₀ (zpow_ne_zero _ hz'0)] at h1
    rw [h1, ← mul_zpow, hrec]
  obtain ⟨P₁, hP₁, P₂, hP₂, hne12⟩ := FarDistinct.exists_two_radii A Bn hBm0
  have hm'0 : b'.ord (Rx'.residue ⟨c • g, hcg'⟩) = 0 := by
    have hvc : A.valuation c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
    have : A.valuation (P₁.evalAt Bn.param) ^ b'.ord (Rx'.residue ⟨c • g, hcg'⟩) =
        A.valuation (P₂.evalAt Bn.param) ^ b'.ord (Rx'.residue ⟨c • g, hcg'⟩) :=
      mul_left_cancel₀ hvc ((hBval P₁ hP₁).trans (hBval P₂ hP₂).symm)
    exact FarDistinct.zpow_exp_eq_zero (FarDistinct.place_data A Bn hP₁).2.2.2.1
      (FarDistinct.place_data A Bn hP₂).2.2.2.1 hne12 this
  have hvc1 : A.valuation c = 1 := by
    have e1 := hBval P₁ hP₁
    rw [hm'0, zpow_zero, zpow_zero, mul_one] at e1
    exact e1

  obtain ⟨hzA, -, hAnearlaw⟩ := hAnear
  obtain ⟨hzA', -, hAfarlaw⟩ := hAfar
  have hAval : ∀ P ∈ An.dom,
      A.valuation (P.evalAt An.param) ^ (x.ord (R.residue ⟨g, hg⟩) + b.ord (Rx.residue ⟨c • g, hcg⟩)) =
        A.valuation (An.modulus : L) ^ b.ord (Rx.residue ⟨c • g, hcg⟩) := by
    intro P hP
    obtain ⟨hrat, hzmem, hz0, hzpos, -, -⟩ := FarDistinct.place_data A An hP
    have hgmem : g ∈ P.toValuationSubring := Place.mem_of_ord_nonneg P hg_ne (le_of_eq (hgA P hP).symm)
    have hP' : P ∈ An'.dom := by rw [hAd]; exact hP
    have hnear := FarDistinct.v_eq_one_of_isUnit A (hAnearlaw g hg hg0 hgA P hP)
    have hfar := FarDistinct.v_eq_one_of_isUnit A
      (hAfarlaw (c • g) hcg hcres (fun Q hQ => hord_cg Q (hgA Q (by rw [← hAd]; exact hQ))) P hP')
    have hrec := FarDistinct.v_evalAt_param_recip A An An' hAd hAp hP
    have hz'0 : A.valuation (P.evalAt An'.param) ≠ 0 := by
      intro h; rw [h, zero_mul] at hrec; exact (Valuation.ne_zero_iff _).2 hAm0 hrec.symm
    rw [Valuation.map_mul, map_zpow₀, zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ hzpos.ne')] at hnear
    rw [heval_cg P hrat hgmem, Valuation.map_mul, Valuation.map_mul, hvc1, one_mul, hnear, map_zpow₀, zpow_neg,
      mul_inv_eq_one₀ (zpow_ne_zero _ hz'0)] at hfar
    have : A.valuation (P.evalAt An.param) ^ x.ord (R.residue ⟨g, hg⟩) *
        A.valuation (P.evalAt An.param) ^ b.ord (Rx.residue ⟨c • g, hcg⟩) =
        (A.valuation (P.evalAt An'.param) * A.valuation (P.evalAt An.param)) ^ b.ord (Rx.residue ⟨c • g, hcg⟩) := by
      rw [mul_zpow, hfar]
    rw [← zpow_add₀ hzpos.ne', hrec] at this
    exact this
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hneQ⟩ := FarDistinct.exists_two_radii A An hAm0
  have hkm : x.ord (R.residue ⟨g, hg⟩) + b.ord (Rx.residue ⟨c • g, hcg⟩) = 0 :=
    FarDistinct.zpow_exp_eq_zero (FarDistinct.place_data A An hQ₁).2.2.2.1
      (FarDistinct.place_data A An hQ₂).2.2.2.1 hneQ ((hAval Q₁ hQ₁).trans (hAval Q₂ hQ₂).symm)
  have hm0 : b.ord (Rx.residue ⟨c • g, hcg⟩) = 0 := by
    have e := hAval Q₁ hQ₁
    rw [hkm, zpow_zero] at e
    have hπ0 : 0 < A.valuation (An.modulus : L) := (Valuation.pos_iff _).2 hAm0
    have hπ1 : A.valuation (An.modulus : L) < 1 := (A.valuation_lt_one_iff An.modulus).1 An.modulus_mem
    exact zpow_right_injective₀ hπ0 hπ1.ne (e.symm.trans (zpow_zero _).symm)
  apply hgx
  omega

end S_AlgebraicCurve_Annulus_integers_ne_of_crossUnit
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_integers_ne_of_crossUnit (solution)
