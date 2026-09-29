-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/94c0f4a0-bd23-552b-a9cb-58c0a07ac6b2

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits
import Theorems.Thm_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.AlgebraicCurve IsLocalRing Polynomial"
open scoped Classical

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation Place Place.ord_inv Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed LSpace ConstantsAreBase RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord constantsAreBase_of_deg_eq_one"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero integers residue_algebraMap algebraMap_mem_iff residue existsUnique_place_forall_residue_sub_mem_nonunits ord_residue_le_sum_ord_of_isIntegral_adjoin"
namespace SOSR
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (P : Place K F) {u : F} (hu : u ∈ P.toValuationSubring) :
    0 ≤ P.ord u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp
  by_cases h : IsUnit (⟨u, hu⟩ : P.toValuationSubring)
  · obtain ⟨w, hw⟩ := h
    have := P.ord_coe_unit w
    rw [hw] at this
    exact this.symm.le
  · exact ((P.mem_maximalIdeal_iff_ord_pos hu0 hu).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr h)).le

theorem mem_of_ord_pos (P : Place K F) {u : F} (hu : 0 < P.ord u) : u ∈ P.toValuationSubring := by
  by_contra h
  have hinv : u⁻¹ ∈ P.toValuationSubring := (P.toValuationSubring.mem_or_inv_mem u).resolve_left h
  have := ord_nonneg_of_mem P hinv
  rw [Place.ord_inv] at this
  omega

theorem ord_pos_of_mem_nonunits (P : Place K F) {u : F} (hu : u ∈ P.toValuationSubring.nonunits)
    (hu0 : u ≠ 0) : 0 < P.ord u := by
  have hmem : u ∈ P.toValuationSubring := ValuationSubring.nonunits_subset hu
  have : (⟨u, hmem⟩ : P.toValuationSubring) ∈ maximalIdeal _ :=
    ValuationSubring.coe_mem_nonunits_iff.mp hu
  exact (P.mem_maximalIdeal_iff_ord_pos hu0 hmem).mp this

theorem mem_nonunits_of_ord_pos (P : Place K F) {u : F} (hu : 0 < P.ord u) :
    u ∈ P.toValuationSubring.nonunits := by
  have hmem := mem_of_ord_pos P hu
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have : (⟨u, hmem⟩ : P.toValuationSubring) ∈ maximalIdeal _ :=
    (P.mem_maximalIdeal_iff_ord_pos hu0 hmem).mpr hu
  exact ValuationSubring.coe_mem_nonunits_iff.mpr this

theorem ord_eq_zero_of_isUnit (P : Place K F) {u : P.toValuationSubring} (hu : IsUnit u) :
    P.ord (u : F) = 0 := by
  obtain ⟨w, rfl⟩ := hu
  exact P.ord_coe_unit w

theorem isUnit_algebraMap (P : Place K F) {c : K} (hc : c ≠ 0) :
    IsUnit (⟨algebraMap K F c, P.algebraMap_mem' c⟩ : P.toValuationSubring) := by
  refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F c⁻¹, P.algebraMap_mem' c⁻¹⟩, ?_⟩
  ext
  simp [hc]

theorem ord_algebraMap_eq_zero (P : Place K F) (c : K) : P.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact ord_eq_zero_of_isUnit P (isUnit_algebraMap P hc)

theorem isUnit_add_of_mem_maximalIdeal (P : Place K F) (a b : P.toValuationSubring)
    (ha : a ∈ maximalIdeal _) (hb : IsUnit b) : IsUnit (a + b) := by
  by_contra h
  have h1 := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 := sub_mem h1 ha
  rw [add_sub_cancel_left] at h2
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 hb

theorem isUnit_nonunit_add_algebraMap (P : Place K F) {m : F}
    (hm : m ∈ P.toValuationSubring.nonunits) {c : K} (hc : c ≠ 0) :
    IsUnit ((⟨m, ValuationSubring.nonunits_subset hm⟩ : P.toValuationSubring) +
      ⟨algebraMap K F c, P.algebraMap_mem' c⟩) :=
  isUnit_add_of_mem_maximalIdeal P _ _ (ValuationSubring.coe_mem_nonunits_iff.mp hm)
    (isUnit_algebraMap P hc)

theorem ord_add_algebraMap_eq_zero (P : Place K F) {m : F} (hm : m ∈ P.toValuationSubring.nonunits)
    {c : K} (hc : c ≠ 0) : P.ord (m + algebraMap K F c) = 0 := by
  have := ord_eq_zero_of_isUnit P (isUnit_nonunit_add_algebraMap P hm hc)
  exact this

theorem mem_of_isIntegral_adjoin (P : Place K F) {j u : F} (hj : j ∈ P.toValuationSubring)
    (hu : IsIntegral (Algebra.adjoin K {j}) u) : u ∈ P.toValuationSubring := by
  obtain ⟨p, hpm, hpev⟩ := hu
  have hle : ∀ y : F, y ∈ Algebra.adjoin K {j} → y ∈ P.toValuationSubring := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff.mp hz]; exact hj
    | algebraMap c => exact P.algebraMap_mem' c
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  refine P.mem_of_eval_monic_eq_zero (P := p.map (algebraMap (Algebra.adjoin K {j}) F))
    (hpm.map _) (fun i => ?_) ?_
  · rw [coeff_map]; exact hle _ (p.coeff i).2
  · rwa [eval_map]

end PlaceFacts

section Zsum

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]

def divOf (u : F) : Divisor K F :=
  if hu : u = 0 then 0 else (HasPrincipalDivisors.exists_divisor u hu).choose

variable {K}

theorem divOf_apply (u : F) (P : Place K F) : divOf K u P = P.ord u := by
  unfold divOf
  split_ifs with hu
  · subst hu
    simp
  · exact (HasPrincipalDivisors.exists_divisor u hu).choose_spec.1 P

theorem mem_support_divOf {u : F} {P : Place K F} : P ∈ (divOf K u).support ↔ P.ord u ≠ 0 := by
  rw [Finsupp.mem_support_iff, divOf_apply]

def zsum (I : Place K F → Prop) (u : F) : ℤ :=
  ∑ P ∈ (divOf K u).support.filter I, P.ord u

theorem zsum_eq_sum_filter (I : Place K F → Prop) (u : F) (S : Finset (Place K F))
    (hS : ∀ P, I P → P.ord u ≠ 0 → P ∈ S) :
    zsum I u = ∑ P ∈ S.filter I, P.ord u := by
  unfold zsum
  apply Finset.sum_subset
  · intro P hP
    rw [Finset.mem_filter] at hP ⊢
    exact ⟨hS P hP.2 (mem_support_divOf.mp hP.1), hP.2⟩
  · intro P hPS hPn
    rw [Finset.mem_filter] at hPS hPn
    by_contra h
    exact hPn ⟨mem_support_divOf.mpr h, hPS.2⟩

theorem zsum_eq_sum (I : Place K F → Prop) (u : F) (T : Finset (Place K F))
    (hT : ∀ P, P ∈ T ↔ (P.ord u ≠ 0 ∧ I P)) : zsum I u = ∑ P ∈ T, P.ord u := by
  unfold zsum
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext P
  rw [Finset.mem_filter, mem_support_divOf, hT]

theorem zsum_mul (I : Place K F → Prop) {u w : F} (hu : u ≠ 0) (hw : w ≠ 0) :
    zsum I (u * w) = zsum I u + zsum I w := by
  set S : Finset (Place K F) :=
    (divOf K (u * w)).support ∪ (divOf K u).support ∪ (divOf K w).support with hS
  have h1 : zsum I (u * w) = ∑ P ∈ S.filter I, P.ord (u * w) :=
    zsum_eq_sum_filter I (u * w) S fun P _ h =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (mem_support_divOf.mpr h))
  have h2 : zsum I u = ∑ P ∈ S.filter I, P.ord u :=
    zsum_eq_sum_filter I u S fun P _ h =>
      Finset.mem_union_left _ (Finset.mem_union_right _ (mem_support_divOf.mpr h))
  have h3 : zsum I w = ∑ P ∈ S.filter I, P.ord w :=
    zsum_eq_sum_filter I w S fun P _ h => Finset.mem_union_right _ (mem_support_divOf.mpr h)
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun P _ => P.ord_mul hu hw

theorem zsum_eq_zero (I : Place K F → Prop) {u : F} (h : ∀ P, I P → P.ord u = 0) :
    zsum I u = 0 := by
  unfold zsum
  refine Finset.sum_eq_zero fun P hP => ?_
  rw [Finset.mem_filter] at hP
  exact h P hP.2

theorem zsum_nonneg (I : Place K F → Prop) {u : F} (h : ∀ P, I P → 0 ≤ P.ord u) :
    0 ≤ zsum I u := by
  unfold zsum
  exact Finset.sum_nonneg fun P hP => h P (Finset.mem_filter.mp hP).2

theorem zsum_one (I : Place K F → Prop) : zsum I (1 : F) = 0 :=
  zsum_eq_zero I fun P _ => P.ord_one

theorem exists_of_zsum_ne_zero (I : Place K F → Prop) {u : F} (h : zsum I u ≠ 0) :
    ∃ P, I P ∧ P.ord u ≠ 0 := by
  by_contra hne
  push Not at hne
  exact h (zsum_eq_zero I hne)

theorem zsum_multiset_prod (I : Place K F → Prop) (s : Multiset F) (hs : (0 : F) ∉ s) :
    zsum I s.prod = (s.map (zsum I)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [zsum_one]
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    have ha : a ≠ 0 := fun h => hs (h ▸ Multiset.mem_cons_self a s)
    have hs' : (0 : F) ∉ s := fun h => hs (Multiset.mem_cons_of_mem h)
    rw [zsum_mul I ha (Multiset.prod_ne_zero hs'), ih hs']

end Zsum

section Degree

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]

theorem zsum_sub_algebraMap (v₀ : Place K F) (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] (β : K)
    (I : Place K F → Prop) (hI₁ : ∀ P, I P → t ∈ P.toValuationSubring)
    (hI₂ : ∀ P, 0 < P.ord (t - algebraMap K F β) → I P) :
    zsum I (t - algebraMap K F β) =
      Module.finrank (IntermediateField.adjoin K ({t} : Set F)) F := by
  set s : F := t - algebraMap K F β with hs
  have hs_tr : Transcendental K s := by
    intro h
    apply ht
    have := h.add (isAlgebraic_algebraMap (A := F) β)
    simpa [hs] using this
  have hy : Transcendental K s⁻¹ := fun h => hs_tr (IsAlgebraic.inv_iff.mp h)
  have hadj : IntermediateField.adjoin K ({s⁻¹} : Set F) =
      IntermediateField.adjoin K ({t} : Set F) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (sub_mem (IntermediateField.mem_adjoin_simple_self K t) (algebraMap_mem _ β))
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h1 : s ∈ IntermediateField.adjoin K ({s⁻¹} : Set F) := by
        have := inv_mem (IntermediateField.mem_adjoin_simple_self K s⁻¹)
        rwa [inv_inv] at this
      have h2 : t = s + algebraMap K F β := by simp [hs]
      rw [h2]
      exact add_mem h1 (algebraMap_mem _ β)
  haveI : FiniteDimensional (IntermediateField.adjoin K ({s⁻¹} : Set F)) F := by
    rw [hadj]; infer_instance
  have hC : ConstantsAreBase K F :=
    AlgebraicCurve.constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) := by
    have h : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
    rw [h]
    infer_instance
  set D : Divisor K F := (divOf K s).filter I with hD
  have hDapply : ∀ P, D P = max 0 (-P.ord s⁻¹) := by
    intro P
    rw [Place.ord_inv, neg_neg, hD, Finsupp.filter_apply, divOf_apply]
    by_cases hIP : I P
    · rw [if_pos hIP]
      have : 0 ≤ P.ord s := ord_nonneg_of_mem P (sub_mem (hI₁ P hIP) (P.algebraMap_mem' β))
      rw [max_eq_right this]
    · rw [if_neg hIP]
      have : P.ord s ≤ 0 := not_lt.mp fun h => hIP (hI₂ P h)
      rw [max_eq_left this]
  have hdeg := AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord s⁻¹ hy D hDapply
  rw [hadj] at hdeg
  rw [← hdeg]
  have hdegD : Divisor.degree D = ∑ P ∈ D.support, D P := by
    simp only [Divisor.degree, Finsupp.liftAddHom_apply, AddMonoidHom.coe_mulRight,
      IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one, Finsupp.sum]
  rw [hdegD, hD, Finsupp.support_filter]
  unfold zsum
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Finset.mem_filter] at hP
  rw [Finsupp.filter_apply_pos _ _ hP.2, divOf_apply]

end Degree

section Cofactor

variable {R₀ S : Type*} [CommRing R₀] [Nontrivial R₀] [CommRing S] [IsDomain S] [Algebra R₀ S]

theorem exists_cofactor {f : S} (hf0 : f ≠ 0) (hfi : IsIntegral R₀ f) :
    ∃ g : S, IsIntegral R₀ g ∧ ∃ c : R₀, c ≠ 0 ∧ f * g = algebraMap R₀ S c := by
  have key : ∀ n : ℕ, ∀ q : R₀[X], q.natDegree ≤ n → q ≠ 0 → aeval f q = 0 →
      ∃ q' : R₀[X], aeval f q' = 0 ∧ q'.coeff 0 ≠ 0 := by
    intro n
    induction n with
    | zero =>
      intro q hq hq0 hfq
      refine ⟨q, hfq, fun h => hq0 ?_⟩
      rw [Polynomial.eq_C_of_natDegree_le_zero hq, h, map_zero]
    | succ n ih =>
      intro q hq hq0 hfq
      by_cases hc : q.coeff 0 = 0
      · have hdx : q.divX * X = q := by
          conv_rhs => rw [← Polynomial.divX_mul_X_add q, hc, map_zero, add_zero]
        have hdx0 : q.divX ≠ 0 := by
          intro h
          apply hq0
          rw [← hdx, h, zero_mul]
        have hfdx : aeval f q.divX = 0 := by
          have : aeval f q.divX * f = 0 := by
            have := congrArg (aeval f) hdx
            rw [map_mul, aeval_X] at this
            rw [this, hfq]
          exact (mul_eq_zero.mp this).resolve_right hf0
        exact ih q.divX
          (by rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]; omega) hdx0 hfdx
      · exact ⟨q, hfq, hc⟩
  obtain ⟨p, hpm, hp⟩ := hfi
  obtain ⟨q, hq, hqc⟩ :=
    key p.natDegree p le_rfl hpm.ne_zero (by rwa [← Polynomial.aeval_def] at hp)
  refine ⟨-aeval f q.divX, ?_, q.coeff 0, hqc, ?_⟩
  · exact (IsIntegral.of_mem_of_fg _ (IsIntegral.fg_adjoin_singleton ⟨p, hpm, hp⟩) _
      (Polynomial.aeval_mem_adjoin_singleton R₀ f)).neg
  · have h := congrArg (aeval f) (Polynomial.divX_mul_X_add q)
    rw [map_add, map_mul, aeval_X, aeval_C, hq] at h
    linear_combination (-1 : S) * h

end Cofactor

section Setting

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
  (R : RegularProlongation A F Fbar) (x : R.integers)

local notation "k" => IsLocalRing.ResidueField A

def Dom (P : Place L F) : Prop :=
  ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits

def Fnt (Q : Place k Fbar) : Prop := R.residue x ∈ Q.toValuationSubring

def Red (P : Place L F) (Q : Place k Fbar) : Prop :=
  ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
    ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
      R.residue h - algebraMap k Fbar (IsLocalRing.residue A a) ∈ Q.toValuationSubring.nonunits

def cst (r : L) (hr : r ∈ A) : R.integers :=
  ⟨algebraMap L F r, (R.algebraMap_mem_iff r).mpr hr⟩

def phi (r : L) : R.integers :=
  if hr : r ∈ A then x - cst R r hr
  else 1 - cst R r⁻¹ ((A.mem_or_inv_mem r).resolve_left hr) * x

variable (A) in

def kappa (r : L) : L := if r ∈ A then 1 else -r

variable {R x}

@[scoped simp] theorem coe_cst (r : L) (hr : r ∈ A) : (cst R r hr : F) = algebraMap L F r := rfl

theorem residue_cst (r : L) (hr : r ∈ A) :
    R.residue (cst R r hr) = algebraMap k Fbar (IsLocalRing.residue A ⟨r, hr⟩) :=
  R.residue_algebraMap ⟨r, hr⟩

theorem mem_of_dom {P : Place L F} (hd : Dom R x P) : (x : F) ∈ P.toValuationSubring := by
  obtain ⟨a, ha⟩ := hd
  have h1 := ValuationSubring.nonunits_subset ha
  have h2 := P.algebraMap_mem' (a : L)
  simpa using add_mem h1 h2

theorem residue_ne_algebraMap (hx : Transcendental k (R.residue x)) (β : k) :
    R.residue x - algebraMap k Fbar β ≠ 0 := by
  intro h
  apply hx
  rw [sub_eq_zero.mp h]
  exact isAlgebraic_algebraMap β

theorem coe_multiset_prod (m : Multiset R.integers) :
    ((m.prod : R.integers) : F) = (m.map ((↑) : R.integers → F)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [ih]

theorem inv_mem_of_not_mem {r : L} (hr : r ∉ A) : r⁻¹ ∈ A :=
  (A.mem_or_inv_mem r).resolve_left hr

theorem ne_zero_of_not_mem {r : L} (hr : r ∉ A) : r ≠ 0 := by
  rintro rfl
  exact hr (zero_mem A)

theorem residue_inv_eq_zero_of_not_mem {r : L} (hr : r ∉ A) :
    IsLocalRing.residue A ⟨r⁻¹, inv_mem_of_not_mem hr⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  by_contra hmax
  have hu : IsUnit (⟨r⁻¹, inv_mem_of_not_mem hr⟩ : A) := by
    by_contra hu
    exact hmax ((IsLocalRing.mem_maximalIdeal _).mpr hu)
  obtain ⟨w, hw⟩ := hu
  apply hr
  have hr0 := ne_zero_of_not_mem hr
  have h1 : (((w⁻¹ : Aˣ) : A) : L) * r⁻¹ = 1 := by
    have h := congrArg (fun z : A => (z : L)) w.inv_mul
    simpa [hw] using h
  have h2 : (((w⁻¹ : Aˣ) : A) : L) = r := by
    calc (((w⁻¹ : Aˣ) : A) : L) = (((w⁻¹ : Aˣ) : A) : L) * r⁻¹ * r := by
          rw [mul_assoc, inv_mul_cancel₀ hr0, mul_one]
      _ = r := by rw [h1, one_mul]
  rw [← h2]
  exact ((w⁻¹ : Aˣ) : A).2

theorem kappa_ne_zero (r : L) : kappa A r ≠ 0 := by
  unfold kappa
  split_ifs with hr
  · exact one_ne_zero
  · exact neg_ne_zero.mpr (ne_zero_of_not_mem hr)

theorem coe_phi_of_mem {r : L} (hr : r ∈ A) : (phi R x r : F) = (x : F) - algebraMap L F r := by
  unfold phi
  rw [dif_pos hr]
  rfl

theorem coe_phi_of_not_mem {r : L} (hr : r ∉ A) :
    (phi R x r : F) = 1 - algebraMap L F r⁻¹ * (x : F) := by
  unfold phi
  rw [dif_neg hr]
  rfl

theorem sub_eq_kappa_mul_phi (r : L) :
    (x : F) - algebraMap L F r = algebraMap L F (kappa A r) * (phi R x r : F) := by
  unfold kappa
  split_ifs with hr
  · rw [coe_phi_of_mem hr, map_one, one_mul]
  · have hr0 := ne_zero_of_not_mem hr
    have : algebraMap L F r ≠ 0 := (_root_.map_ne_zero _).mpr hr0
    rw [coe_phi_of_not_mem hr, map_neg, map_inv₀]
    field_simp
    ring

theorem residue_phi_of_mem {r : L} (hr : r ∈ A) :
    R.residue (phi R x r) = R.residue x - algebraMap k Fbar (IsLocalRing.residue A ⟨r, hr⟩) := by
  unfold phi
  rw [dif_pos hr, map_sub, residue_cst]

theorem residue_phi_of_not_mem {r : L} (hr : r ∉ A) : R.residue (phi R x r) = 1 := by
  unfold phi
  rw [dif_neg hr, map_sub, map_one, map_mul, residue_cst, residue_inv_eq_zero_of_not_mem hr,
    map_zero, zero_mul, sub_zero]

theorem residue_phi_ne_zero (hx : Transcendental k (R.residue x)) (r : L) :
    R.residue (phi R x r) ≠ 0 := by
  by_cases hr : r ∈ A
  · rw [residue_phi_of_mem hr]
    exact residue_ne_algebraMap hx _
  · rw [residue_phi_of_not_mem hr]
    exact one_ne_zero

variable [IsAlgClosed L]

theorem transcendental_coe (hx : Transcendental k (R.residue x)) : Transcendental L (x : F) := by
  intro halg
  have hint : IsIntegral L (x : F) := halg.isIntegral
  have hdeg1 := IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint)
  obtain ⟨r, hr⟩ := minpoly.mem_range_of_degree_eq_one L (x : F) hdeg1
  have hrA : r ∈ A := (R.algebraMap_mem_iff r).mp (by rw [hr]; exact x.2)
  apply hx
  have hxeq : x = cst R r hrA := Subtype.ext hr.symm
  rw [hxeq, residue_cst]
  exact isAlgebraic_algebraMap _

theorem coe_ne_algebraMap (hx : Transcendental k (R.residue x)) (r : L) :
    (x : F) - algebraMap L F r ≠ 0 := by
  intro h
  apply transcendental_coe hx
  rw [sub_eq_zero.mp h]
  exact isAlgebraic_algebraMap r

theorem coe_phi_ne_zero (hx : Transcendental k (R.residue x)) (r : L) : (phi R x r : F) ≠ 0 := by
  intro h
  apply coe_ne_algebraMap hx r
  rw [sub_eq_kappa_mul_phi, h, mul_zero]

variable [IsCurveOver L F]

theorem zsum_phi_of_not_mem (hx : Transcendental k (R.residue x)) {r : L} (hr : r ∉ A) :
    zsum (Dom R x) (phi R x r : F) = 0 := by
  refine zsum_eq_zero _ fun P hP => ?_
  obtain ⟨a, ha⟩ := hP
  have hr0 := ne_zero_of_not_mem hr
  have har : (a : L) - r ≠ 0 := by
    intro h
    apply hr
    rw [← sub_eq_zero.mp h]
    exact a.2
  have hsum : ((x : F) - algebraMap L F a) + algebraMap L F ((a : L) - r) =
      (x : F) - algebraMap L F r := by
    rw [map_sub]; ring
  have hphi : (phi R x r : F) = algebraMap L F (-r)⁻¹ * ((x : F) - algebraMap L F r) := by
    have h := sub_eq_kappa_mul_phi (R := R) (x := x) r
    unfold kappa at h
    rw [if_neg hr] at h
    rw [h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (neg_ne_zero.mpr hr0), map_one, one_mul]
  rw [hphi, P.ord_mul ((_root_.map_ne_zero _).mpr (inv_ne_zero (neg_ne_zero.mpr hr0)))
    (coe_ne_algebraMap hx r), ord_algebraMap_eq_zero, ← hsum, ord_add_algebraMap_eq_zero P ha har,
    add_zero]

variable [IsCurveOver (IsLocalRing.ResidueField A) Fbar]

theorem zsum_residue_le (hx : Transcendental k (R.residue x))
    (hfin : 0 < Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin k {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (g : R.integers) (hgi : IsIntegral (Algebra.adjoin L {(x : F)}) (g : F))
    (hg : R.residue g ≠ 0) :
    zsum (Fnt R x) (R.residue g) ≤ zsum (Dom R x) (g : F) := by
  have hE : ∀ P, Dom R x P → ∃! Q : Place k Fbar, Red R x P Q := fun P hP =>
    RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits A R x hx hfin hdeg
      hchart P hP
  set Dg : Divisor L F := divOf L (g : F) with hDg
  set T : Place k Fbar → Finset (Place L F) := fun Q =>
    Dg.support.filter fun P => Dom R x P ∧ Red R x P Q with hT
  have hchild : ∀ Q, Fnt R x Q → Q.ord (R.residue g) ≤ ∑ P ∈ T Q, Dg P := fun Q hQ =>
    RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin A R x hx hfin hdeg hchart g
      hgi hg Q hQ Dg (fun P => divOf_apply _ _) (T Q) (fun P => by
        simp only [hT, Finset.mem_filter, Finsupp.mem_support_iff, Dom, Red])
  set SQ : Finset (Place k Fbar) := (divOf k (R.residue g)).support.filter (Fnt R x) with hSQ
  calc zsum (Fnt R x) (R.residue g)
      = ∑ Q ∈ SQ, Q.ord (R.residue g) := rfl
    _ ≤ ∑ Q ∈ SQ, ∑ P ∈ T Q, Dg P :=
        Finset.sum_le_sum fun Q hQ => hchild Q (Finset.mem_filter.mp hQ).2
    _ = ∑ P ∈ SQ.biUnion T, Dg P := by
        rw [Finset.sum_biUnion]
        intro Q₁ _ Q₂ _ hne
        change Disjoint (T Q₁) (T Q₂)
        refine Finset.disjoint_left.mpr fun P h1 h2 => hne ?_
        simp only [hT, Finset.mem_filter] at h1 h2
        exact (hE P h1.2.1).unique h1.2.2 h2.2.2
    _ ≤ ∑ P ∈ Dg.support.filter (Dom R x), Dg P := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro P hP
          rw [Finset.mem_biUnion] at hP
          obtain ⟨Q, -, hPQ⟩ := hP
          simp only [hT, Finset.mem_filter] at hPQ
          exact Finset.mem_filter.mpr ⟨hPQ.1, hPQ.2.1⟩
        · intro P hP _
          rw [hDg, divOf_apply]
          exact ord_nonneg_of_mem P
            (mem_of_isIntegral_adjoin P (mem_of_dom (Finset.mem_filter.mp hP).2) hgi)
    _ = zsum (Dom R x) (g : F) := by
        unfold zsum
        exact Finset.sum_congr rfl fun P _ => divOf_apply _ _

theorem zsum_phi_le (hx : Transcendental k (R.residue x))
    (hfin : 0 < Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin k {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (r : L) :
    zsum (Dom R x) (phi R x r : F) ≤ zsum (Fnt R x) (R.residue (phi R x r)) := by
  haveI : IsAlgClosed k := ValuationSubring.isAlgClosed_residueField A
  haveI : FiniteDimensional (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  have hxL : Transcendental L (x : F) := transcendental_coe hx
  by_cases hr : r ∈ A
  ·
    rw [residue_phi_of_mem hr, coe_phi_of_mem hr]
    have hRHS_nonneg : 0 ≤ zsum (Fnt R x)
        (R.residue x - algebraMap k Fbar (IsLocalRing.residue A ⟨r, hr⟩)) :=
      zsum_nonneg _ fun Q hQ => ord_nonneg_of_mem Q (sub_mem hQ (Q.algebraMap_mem' _))
    rcases isEmpty_or_nonempty (Place L F) with hempty | hne
    · have h0 : zsum (Dom R x) ((x : F) - algebraMap L F r) = 0 := by
        unfold zsum
        exact Finset.sum_eq_zero fun P _ => (IsEmpty.false P).elim
      rw [h0]
      exact hRHS_nonneg
    · obtain ⟨v₀⟩ := hne
      have hF : zsum (Dom R x) ((x : F) - algebraMap L F r) =
          Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
        zsum_sub_algebraMap v₀ (x : F) hxL r (Dom R x) (fun P hP => mem_of_dom hP)
          (fun P hP => ⟨⟨r, hr⟩, mem_nonunits_of_ord_pos P hP⟩)

      have hn0 : zsum (Dom R x) ((x : F) - algebraMap L F r) ≠ 0 := by
        rw [hF, hdeg]
        exact_mod_cast hfin.ne'
      obtain ⟨P, hP, -⟩ := exists_of_zsum_ne_zero _ hn0
      obtain ⟨Q₀, -, -⟩ := RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits
        A R x hx hfin hdeg hchart P hP
      have hFbar : zsum (Fnt R x)
          (R.residue x - algebraMap k Fbar (IsLocalRing.residue A ⟨r, hr⟩)) =
          Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar :=
        zsum_sub_algebraMap Q₀ (R.residue x) hx _ (Fnt R x) (fun Q hQ => hQ)
          (fun Q hQ => by
            have h1 := mem_of_ord_pos Q hQ
            have h2 := Q.algebraMap_mem' (IsLocalRing.residue A ⟨r, hr⟩)
            have := add_mem h1 h2
            simpa [Fnt] using this)
      rw [hF, hFbar, hdeg]
  · rw [zsum_phi_of_not_mem hx hr, residue_phi_of_not_mem hr, zsum_one]

theorem zsum_eq_zsum_residue (hx : Transcendental k (R.residue x))
    (hfin : 0 < Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank (IntermediateField.adjoin k ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin k {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0) :
    zsum (Dom R x) (f : F) = zsum (Fnt R x) (R.residue f) := by
  have hf0 : (f : F) ≠ 0 := by
    intro h
    apply hf
    rw [show f = 0 from Subtype.ext h, map_zero]

  obtain ⟨g, hgi, c₀, hc₀, hfg⟩ := exists_cofactor hf0 hfi
  have hc₀F : algebraMap (Algebra.adjoin L {(x : F)}) F c₀ = (c₀ : F) := rfl
  rw [hc₀F] at hfg
  obtain ⟨p₁, hp₁⟩ : ∃ p₁ : L[X], aeval (x : F) p₁ = (c₀ : F) := by
    have : (c₀ : F) ∈ (aeval (x : F) : L[X] →ₐ[L] F).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact c₀.2
    exact (AlgHom.mem_range _).mp this
  have hc₀F0 : (c₀ : F) ≠ 0 := fun h => hc₀ (Subtype.ext h)
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    exact hc₀F0 (by rw [← hp₁, map_zero])

  set Φ : R.integers := (p₁.roots.map (phi R x)).prod with hΦ
  set u : L := p₁.leadingCoeff * (p₁.roots.map (kappa A)).prod with hu
  have hu0 : u ≠ 0 := by
    refine mul_ne_zero (leadingCoeff_ne_zero.mpr hp₁0) (Multiset.prod_ne_zero ?_)
    rw [Multiset.mem_map]
    rintro ⟨r, -, hr⟩
    exact kappa_ne_zero r hr
  have hfac : (c₀ : F) = algebraMap L F u * (Φ : F) := by
    rw [← hp₁]
    conv_lhs => rw [(IsAlgClosed.splits p₁).eq_prod_roots]
    rw [map_mul, aeval_C, map_multiset_prod, Multiset.map_map]
    have hfun : ((aeval (x : F) : L[X] →ₐ[L] F) ∘ fun r => X - C r) =
        fun r => algebraMap L F (kappa A r) * (phi R x r : F) := by
      funext r
      simp only [Function.comp_apply, map_sub, aeval_X, aeval_C]
      exact sub_eq_kappa_mul_phi r
    rw [hfun, Multiset.prod_map_mul, hu, hΦ, coe_multiset_prod, Multiset.map_map, map_mul,
      map_multiset_prod, Multiset.map_map]
    simp only [Function.comp_def]
    ring

  have hΦ0 : (Φ : F) ≠ 0 := by
    rw [hΦ, coe_multiset_prod, Multiset.map_map]
    refine Multiset.prod_ne_zero ?_
    rw [Multiset.mem_map]
    rintro ⟨r, -, hr⟩
    exact coe_phi_ne_zero hx r hr
  have hresΦ : R.residue Φ = (p₁.roots.map fun r => R.residue (phi R x r)).prod := by
    rw [hΦ, map_multiset_prod, Multiset.map_map, Function.comp_def]
  have hresΦ0 : R.residue Φ ≠ 0 := by
    rw [hresΦ]
    refine Multiset.prod_ne_zero ?_
    rw [Multiset.mem_map]
    rintro ⟨r, -, hr⟩
    exact residue_phi_ne_zero hx r hr

  obtain ⟨fu, hfu⟩ := R.isUnit_of_residue_ne_zero hf
  set g' : R.integers := ((fu⁻¹ : R.integersˣ) : R.integers) * Φ with hg'
  have hfg' : f * g' = Φ := by
    rw [hg', ← hfu, ← mul_assoc, Units.mul_inv, one_mul]
  have hfg'F : (f : F) * (g' : F) = (Φ : F) := by
    have := congrArg (fun z : R.integers => (z : F)) hfg'
    simpa using this
  have hg'F : (g' : F) = algebraMap L F u⁻¹ * g := by
    apply mul_left_cancel₀ hf0
    rw [hfg'F, mul_left_comm, hfg, hfac, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu0, map_one,
      one_mul]
  have hg'i : IsIntegral (Algebra.adjoin L {(x : F)}) (g' : F) := by
    rw [hg'F]
    have : IsIntegral (Algebra.adjoin L {(x : F)}) (algebraMap L F u⁻¹) := by
      rw [IsScalarTower.algebraMap_apply L (Algebra.adjoin L {(x : F)}) F]
      exact isIntegral_algebraMap
    exact this.mul hgi
  have hresg' : R.residue g' ≠ 0 := by
    intro h
    apply hresΦ0
    rw [← hfg', map_mul, h, mul_zero]
  have hg'0 : (g' : F) ≠ 0 := by
    intro h
    apply hΦ0
    rw [← hfg'F, h, mul_zero]

  have hAf := zsum_residue_le hx hfin hdeg hchart f hfi hf
  have hAg := zsum_residue_le hx hfin hdeg hchart g' hg'i hresg'

  have hΦle : zsum (Dom R x) (Φ : F) ≤ zsum (Fnt R x) (R.residue Φ) := by
    have h1 : zsum (Dom R x) (Φ : F) =
        (p₁.roots.map fun r => zsum (Dom R x) (phi R x r : F)).sum := by
      rw [hΦ, coe_multiset_prod, Multiset.map_map, zsum_multiset_prod, Multiset.map_map]
      · rfl
      · rw [Multiset.mem_map]
        rintro ⟨r, -, hr⟩
        exact coe_phi_ne_zero hx r hr
    have h2 : zsum (Fnt R x) (R.residue Φ) =
        (p₁.roots.map fun r => zsum (Fnt R x) (R.residue (phi R x r))).sum := by
      rw [hresΦ, zsum_multiset_prod, Multiset.map_map]
      · rfl
      · rw [Multiset.mem_map]
        rintro ⟨r, -, hr⟩
        exact residue_phi_ne_zero hx r hr
    rw [h1, h2]
    exact Multiset.sum_map_le_sum_map _ _ fun r _ => zsum_phi_le hx hfin hdeg hchart r

  have hZ : zsum (Dom R x) (f : F) + zsum (Dom R x) (g' : F) = zsum (Dom R x) (Φ : F) := by
    rw [← zsum_mul _ hf0 hg'0, hfg'F]
  have hZbar : zsum (Fnt R x) (R.residue f) + zsum (Fnt R x) (R.residue g') =
      zsum (Fnt R x) (R.residue Φ) := by
    rw [← zsum_mul _ hf hresg', ← map_mul, hfg']
  apply le_antisymm
  · linarith
  · exact hAf

end Setting

end AlgebraicCurve.RegularProlongation.SOSR
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.AlgebraicCurve.RegularProlongation.SOSR"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.AlgebraicCurve.RegularProlongation"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.AlgebraicCurve.RegularProlongation.SOSR"

open AlgebraicCurve.RegularProlongation.SOSR in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (Dbar : Divisor (IsLocalRing.ResidueField A) Fbar)
    (hDbar : ∀ Q, Dbar Q = Q.ord (R.residue f))
    (TP : Finset (Place L F))
    (hTP : ∀ P, P ∈ TP ↔ (D P ≠ 0 ∧
      ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits))
    (TQ : Finset (Place (IsLocalRing.ResidueField A) Fbar))
    (hTQ : ∀ Q, Q ∈ TQ ↔ (Dbar Q ≠ 0 ∧ R.residue x ∈ Q.toValuationSubring)) :
    ∑ P ∈ TP, D P = ∑ Q ∈ TQ, Dbar Q := by
  have h1 : ∑ P ∈ TP, D P = zsum (Dom R x) (f : F) := by
    rw [zsum_eq_sum (Dom R x) (f : F) TP (fun P => by rw [hTP, hD]; exact Iff.rfl)]
    exact Finset.sum_congr rfl fun P _ => hD P
  have h2 : ∑ Q ∈ TQ, Dbar Q = zsum (Fnt R x) (R.residue f) := by
    rw [zsum_eq_sum (Fnt R x) (R.residue f) TQ (fun Q => by rw [hTQ, hDbar]; exact Iff.rfl)]
    exact Finset.sum_congr rfl fun Q _ => hDbar Q
  rw [h1, h2]
  exact zsum_eq_zsum_residue hx hfin hdeg hchart f hfi hf

end S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin (solution)
