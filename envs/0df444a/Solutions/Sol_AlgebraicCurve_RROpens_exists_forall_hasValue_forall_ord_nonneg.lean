-- Prove2me | solution 1 for AlgebraicCurve.RROpens.exists_forall_hasValue_forall_ord_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e4427227-f2e7-5eb3-9bb5-112e8bd49995

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RROpens_exists_forall_hasValue_forall_ord_nonneg
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u v

noncomputable section

open IsLocalRing Module

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed LSpace ell mem_lSpace_iff_ord lSpace_mono ConstantsAreBase ell_zero_eq_one_of_constantsAreBase constantsAreBase_of_deg_eq_one lSpace_eq_bot_of_degree_neg"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ResidueField deg ord ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective"
p2m_open "AlgebraicCurve.Place"
section Priv
variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem' {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem'"
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg' {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg'"
namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "mul ne_zero" end HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in

private theorem HasValue.add' {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

private theorem _root_.AlgebraicCurve.Place.hasValue_zero_of_ord_pos' {g : F} (hg0 : g ≠ 0) (hg : 0 < v.ord g) :
    v.HasValue g 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg' hg0 hg.le
  refine ⟨hmem, ?_⟩
  rw [map_zero, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h0 := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at h0
  change v.ord g = 0 at h0
  omega

p2m_export "AlgebraicCurve.Place" "hasValue_zero_of_ord_pos'"

private theorem _root_.AlgebraicCurve.Place.hasValue_sum' {ι : Type*} (s : Finset ι) (f : ι → F) (a : ι → K)
    (h : ∀ i ∈ s, v.HasValue (f i) (a i)) :
    v.HasValue (∑ i ∈ s, f i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (v.hasValue_algebraMap 0)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact HasValue.add' v (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

p2m_export "AlgebraicCurve.Place" "hasValue_sum'"
end Priv
end Place

namespace RROpensInterpImpl

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

private theorem finite_lSpace [IsAlgClosed K] [IsCurveOver K F] {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) (D : Divisor K F) : Module.Finite K (LSpace D) := by
  set n : ℕ := ((g : ℤ) - Divisor.degree D).toNat with hn
  set D' : Divisor K F := D + (n : ℤ) • Finsupp.single P 1 with hD'
  have hdeg : (g : ℤ) ≤ Divisor.degree D' := by
    have h1 : (1 : ℤ) ≤ (P.deg : ℤ) := by
      rw [IsCurveOver.deg_eq_one_of_isAlgClosed P]; norm_num
    have hn0 : (g : ℤ) - Divisor.degree D ≤ (n : ℤ) := by
      rw [hn]; exact Int.self_le_toNat _
    rw [hD', map_add, map_zsmul, Divisor.degree_single, one_mul, smul_eq_mul]
    nlinarith [Int.natCast_nonneg n]
  have hpos : 0 < finrank K (LSpace D') := by
    have h := hRR D'
    have h0 : (0 : ℤ) ≤ (ell (Kc - D') : ℤ) := Int.natCast_nonneg _
    have : (1 : ℤ) ≤ (ell D' : ℤ) := by linarith
    have h' : 1 ≤ ell D' := by exact_mod_cast this
    exact h'
  haveI : Module.Finite K (LSpace D') := Module.finite_of_finrank_pos hpos
  have hle : D ≤ D' := by
    rw [Finsupp.le_def]; intro v
    rw [hD', Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have : (0 : ℤ) ≤ Finsupp.single P 1 v := by
      rcases eq_or_ne v P with rfl | hv
      · simp
      · simp [Finsupp.single_eq_of_ne hv]
    nlinarith [Int.natCast_nonneg n]
  exact Submodule.finiteDimensional_of_le (lSpace_mono hle)

open Classical in

private theorem coeff_aux (n : ℕ) (P₀ : Place K F) (A : Finset (Place K F)) (w : Place K F) :
    (((n : ℤ) • Finsupp.single P₀ (1 : ℤ) - ∑ a ∈ A, Finsupp.single a (1 : ℤ) : Divisor K F) w)
      = (if P₀ = w then (n : ℤ) else 0) - (if w ∈ A then 1 else 0) := by
  rw [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']

private theorem ell_aux [IsAlgClosed K] [IsCurveOver K F] {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P₀ : Place K F) (A : Finset (Place K F)) (n : ℕ) (hA : A.card + 2 * g ≤ n + 1) :
    (ell (((n : ℤ)) • Finsupp.single P₀ (1 : ℤ) - ∑ a ∈ A, Finsupp.single a (1 : ℤ)) : ℤ)
      = n - A.card + 1 - g := by
  classical
  set D : Divisor K F :=
    ((n : ℤ)) • Finsupp.single P₀ (1 : ℤ) - ∑ a ∈ A, Finsupp.single a (1 : ℤ) with hD

  have hC : ConstantsAreBase K F :=
    constantsAreBase_of_deg_eq_one P₀ (IsCurveOver.deg_eq_one_of_isAlgClosed P₀)
  have hell0 : ell (0 : Divisor K F) = 1 := ell_zero_eq_one_of_constantsAreBase hC
  have hellK : ell Kc = g := by
    have h := hRR 0
    rw [sub_zero, hell0, map_zero] at h
    push_cast at h
    omega
  have hdegK : Divisor.degree Kc = 2 * (g : ℤ) - 2 := by
    have h := hRR Kc
    rw [sub_self, hell0, hellK] at h
    push_cast at h
    omega
  have hdegA : Divisor.degree (∑ a ∈ A, Finsupp.single a (1 : ℤ) : Divisor K F) = (A.card : ℤ) := by
    rw [map_sum]
    simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have hdegD : Divisor.degree D = (n : ℤ) - A.card := by
    rw [hD, map_sub, map_zsmul, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed P₀,
      hdegA]
    push_cast
    ring
  have hneg : ell (Kc - D) = 0 := by
    rw [ell, lSpace_eq_bot_of_degree_neg, finrank_bot]
    rw [map_sub, hdegK, hdegD]
    have : (A.card : ℤ) + 2 * g ≤ n + 1 := by exact_mod_cast hA
    omega
  have h := hRR D
  rw [hneg, hdegD] at h
  push_cast at h ⊢
  linarith

private theorem exists_section_aux [IsAlgClosed K] [IsCurveOver K F] {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (E : Finset (Place K F)) (P₀ : Place K F) (hP₀ : P₀ ∉ E) (e : Place K F) (he : e ∈ E) :
    ∃ u : F, u ≠ 0 ∧ e.ord u = 0 ∧ (∀ e' ∈ E, e' ≠ e → 0 < e'.ord u) ∧
      ∀ w : Place K F, w ≠ P₀ → 0 ≤ w.ord u := by
  classical
  have hc : 1 ≤ E.card := Finset.card_pos.mpr ⟨e, he⟩
  have hP₀e : P₀ ≠ e := fun h => hP₀ (h.symm ▸ he)

  let n : ℕ := 2 * g + E.card
  let D₁ : Divisor K F := ((n : ℤ)) • Finsupp.single P₀ (1 : ℤ) - ∑ a ∈ E.erase e, Finsupp.single a (1 : ℤ)
  let D₂ : Divisor K F := ((n : ℤ)) • Finsupp.single P₀ (1 : ℤ) - ∑ a ∈ E, Finsupp.single a (1 : ℤ)
  have hD₁w : ∀ w, D₁ w = (if P₀ = w then (n : ℤ) else 0) - (if w ∈ E.erase e then 1 else 0) :=
    fun w => coeff_aux n P₀ (E.erase e) w
  have hD₂w : ∀ w, D₂ w = (if P₀ = w then (n : ℤ) else 0) - (if w ∈ E then 1 else 0) :=
    fun w => coeff_aux n P₀ E w
  have h₁ : (ell D₁ : ℤ) = n - (E.erase e).card + 1 - g :=
    ell_aux hRR P₀ (E.erase e) n (by rw [Finset.card_erase_of_mem he]; omega)
  have h₂ : (ell D₂ : ℤ) = n - E.card + 1 - g := ell_aux hRR P₀ E n (by omega)
  rw [Finset.card_erase_of_mem he, Nat.cast_sub hc] at h₁
  have hlt : ell D₂ < ell D₁ := by
    have : (ell D₂ : ℤ) < ell D₁ := by rw [h₁, h₂]; push_cast; linarith
    exact_mod_cast this
  haveI := finite_lSpace hRR P₀ D₁

  have hle : LSpace D₂ ≤ LSpace D₁ := by
    refine lSpace_mono ?_
    intro w
    rw [hD₁w, hD₂w]
    by_cases hw : w ∈ E
    · rw [if_pos hw]
      split_ifs <;> omega
    · rw [if_neg hw, if_neg (fun h => hw (Finset.mem_of_mem_erase h))]
  have hne : LSpace D₂ ≠ LSpace D₁ := by
    intro h
    have : ell D₂ = ell D₁ := by
      show Module.finrank K (LSpace D₂) = Module.finrank K (LSpace D₁)
      rw [h]
    omega
  obtain ⟨u, hu₁, hu₂⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have hu0 : u ≠ 0 := fun h => hu₂ (h ▸ (LSpace D₂).zero_mem)
  have hord₁ := (mem_lSpace_iff_ord.mp hu₁).resolve_left hu0
  refine ⟨u, hu0, ?_, ?_, ?_⟩
  ·
    have hge : 0 ≤ e.ord u := by
      have h := hord₁ e
      rw [hD₁w, if_neg hP₀e, if_neg (Finset.notMem_erase e E)] at h
      simpa using h
    by_contra hne0
    apply hu₂
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun w => ?_
    by_cases hwe : w = e
    · rw [hwe, hD₂w, if_neg hP₀e, if_pos he]
      omega
    · have h := hord₁ w
      rw [hD₁w] at h
      rw [hD₂w]
      by_cases hwE : w ∈ E
      · rw [if_pos (Finset.mem_erase.mpr ⟨hwe, hwE⟩)] at h
        rw [if_pos hwE]
        exact h
      · rw [if_neg (fun h' => hwE (Finset.mem_of_mem_erase h'))] at h
        rw [if_neg hwE]
        exact h
  · intro e' he' hne'
    have hP₀e' : P₀ ≠ e' := fun h => hP₀ (h.symm ▸ he')
    have h := hord₁ e'
    rw [hD₁w, if_neg hP₀e', if_pos (Finset.mem_erase.mpr ⟨hne', he'⟩)] at h
    simp at h
    exact h
  · intro w hw
    have h := hord₁ w
    rw [hD₁w, if_neg (Ne.symm hw)] at h
    split_ifs at h <;> simp at h <;> omega

theorem exists_forall_hasValue_forall_ord_nonneg_impl [IsAlgClosed K] [IsCurveOver K F]
    (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (E : Finset (Place K F)) (c : Place K F → K) (hc : ∀ e ∈ E, c e ≠ 0)
    (P₀ : Place K F) (hP₀ : P₀ ∉ E) :
    ∃ h : F, h ≠ 0 ∧ (∀ e ∈ E, e.HasValue h (c e)) ∧
      ∀ v : Place K F, v ≠ P₀ → 0 ≤ v.ord h := by
  classical
  rcases E.eq_empty_or_nonempty with hE | hE
  · refine ⟨1, one_ne_zero, by simp [hE], fun v _ => by simp⟩

  have key : ∀ e ∈ E, ∃ u : F, e.HasValue u 1 ∧ (∀ e' ∈ E, e' ≠ e → e'.HasValue u 0) ∧
      ∀ w : Place K F, w ≠ P₀ → 0 ≤ w.ord u := by
    intro e he
    obtain ⟨u, hu0, hue, hue', hureg⟩ := exists_section_aux hRR E P₀ hP₀ e he

    obtain ⟨hum, huunit⟩ := e.exists_isUnit_of_ord_eq_zero hu0 hue
    have hsurj : Function.Surjective (algebraMap K e.ResidueField) := by
      haveI : Module.Finite K e.ResidueField := IsCurveOver.finite_residueField e
      haveI : Algebra.IsIntegral K e.ResidueField := Algebra.IsIntegral.of_finite K _
      exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := e.ResidueField)).2
    obtain ⟨a, ha, ha0'⟩ := e.exists_hasValue_of_surjective hsurj hum
    have ha0 : a ≠ 0 := ha0' huunit
    refine ⟨algebraMap K F a⁻¹ * u, ?_, ?_, ?_⟩
    · have := (e.hasValue_algebraMap a⁻¹).mul ha
      rwa [inv_mul_cancel₀ ha0] at this
    · intro e' he' hne
      have h0 : e'.HasValue u 0 := e'.hasValue_zero_of_ord_pos' hu0 (hue' e' he' hne)
      simpa using (e'.hasValue_algebraMap a⁻¹).mul h0
    · intro w hw
      have hmem : algebraMap K F a⁻¹ * u ∈ w.toValuationSubring :=
        mul_mem (w.algebraMap_mem' _) (w.mem_of_ord_nonneg' hu0 (hureg w hw))
      exact w.ord_nonneg_of_mem' hmem
  choose! u hu using key
  refine ⟨∑ e ∈ E, algebraMap K F (c e) * u e, ?_, ?_, ?_⟩
  ·
    obtain ⟨e₀, he₀⟩ := hE
    have hval : e₀.HasValue (∑ e ∈ E, algebraMap K F (c e) * u e) (c e₀) := by
      have := e₀.hasValue_sum' E (fun e => algebraMap K F (c e) * u e)
        (fun e => if e = e₀ then c e₀ else 0) ?_
      · simpa [Finset.sum_ite_eq', he₀] using this
      · intro e he
        by_cases hee : e = e₀
        · subst hee
          simpa using (e.hasValue_algebraMap (c e)).mul (hu e he).1
        · show e₀.HasValue (algebraMap K F (c e) * u e) (if e = e₀ then c e₀ else 0)
          rw [if_neg hee]
          simpa using (e₀.hasValue_algebraMap (c e)).mul ((hu e he).2.1 e₀ he₀ (Ne.symm hee))
    exact hval.ne_zero (hc e₀ he₀)
  · intro e₀ he₀
    have := e₀.hasValue_sum' E (fun e => algebraMap K F (c e) * u e)
      (fun e => if e = e₀ then c e₀ else 0) ?_
    · simpa [Finset.sum_ite_eq', he₀] using this
    · intro e he
      by_cases hee : e = e₀
      · subst hee
        simpa using (e.hasValue_algebraMap (c e)).mul (hu e he).1
      · show e₀.HasValue (algebraMap K F (c e) * u e) (if e = e₀ then c e₀ else 0)
        rw [if_neg hee]
        simpa using (e₀.hasValue_algebraMap (c e)).mul ((hu e he).2.1 e₀ he₀ (Ne.symm hee))
  · intro w hw
    apply w.ord_nonneg_of_mem'
    refine sum_mem fun e he => mul_mem (w.algebraMap_mem' _) ?_

    rcases eq_or_ne (u e) 0 with h0 | h0
    · rw [h0]; exact zero_mem _
    · exact w.mem_of_ord_nonneg' h0 ((hu e he).2.2 w hw)

end RROpensInterpImpl

end AlgebraicCurve

end

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RROpens_exists_forall_hasValue_forall_ord_nonneg.AlgebraicCurve"

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (E : Finset (Place K F)) (c : Place K F → K) (hc : ∀ e ∈ E, c e ≠ 0)
    (P₀ : Place K F) (hP₀ : P₀ ∉ E) :
    ∃ h : F, h ≠ 0 ∧ (∀ e ∈ E, e.HasValue h (c e)) ∧
      ∀ v : Place K F, v ≠ P₀ → 0 ≤ v.ord h :=
  AlgebraicCurve.RROpensInterpImpl.exists_forall_hasValue_forall_ord_nonneg_impl Kc g hRR E c hc P₀ hP₀

end S_AlgebraicCurve_RROpens_exists_forall_hasValue_forall_ord_nonneg
end P2MW
export P2MW.S_AlgebraicCurve_RROpens_exists_forall_hasValue_forall_ord_nonneg (solution)
