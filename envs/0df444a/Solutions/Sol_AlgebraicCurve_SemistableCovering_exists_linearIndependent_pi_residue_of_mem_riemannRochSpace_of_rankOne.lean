-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/9c6981f8-fb15-593c-84b8-5a3c9af67392

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_sub_algebraMap_pos_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
import Theorems.Thm_AlgebraicCurve_Place_exists_sub_algebraMap_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff"
p2m_attr_erase "simp" "ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_SemistableCovering_exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne.AlgebraicCurve"
open scoped IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.coe_algebraMap Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace genusFF IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed LSpace ell mem_lSpace_iff_ord lSpace_mono IsCurveOver.exists_separating_transcendental Place.exists_ord_sub_algebraMap_pos_of_transcendental Place.exists_sub_algebraMap_mem_maximalIdeal"
namespace MultiGe
p2m_open "AlgebraicCurve"

open IsLocalRing

private theorem infinite_place_of_isCurveOver (k Fb : Type*) [Field k] [IsAlgClosed k] [Field Fb] [Algebra k Fb]
    [IsCurveOver k Fb] [Algebra.EssFiniteType k Fb] (hrat : ∀ v : Place k Fb, v.IsRational) :
    Infinite (Place k Fb) := by
  obtain ⟨t, ht, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := k) (F := Fb)
  haveI := hfd; haveI := hsep
  have hex : ∀ c : k, ∃ v : Place k Fb, 0 < v.ord (t - algebraMap k Fb c) := fun c =>
    Place.exists_ord_sub_algebraMap_pos_of_transcendental t ht c
  choose v hv using hex
  have htc : ∀ c : k, t ≠ algebraMap k Fb c := by
    intro c htc
    apply ht
    rw [htc]
    exact isAlgebraic_algebraMap c
  refine Infinite.of_injective v fun c c' hcc' => ?_
  have h1 := ((v c).mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos (hrat _) t c (htc c)).mpr (hv c)
  have h2 := ((v c').mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos (hrat _) t c' (htc c')).mpr (hv c')
  rw [← hcc'] at h2
  exact h1.2.symm.trans h2.2

private theorem mem_valuationSubring_of_ord_nonneg
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0)
    (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hϖ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (ϖ : v.toValuationSubring).2 _)

private theorem one_le_ord_of_mem_maximalIdeal
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {g : v.toValuationSubring}
    (hg : g ∈ maximalIdeal v.toValuationSubring) (hg0 : (g : F) ≠ 0) : 1 ≤ v.ord (g : F) := by
  have hnotunit : ¬ IsUnit g := by
    rw [IsLocalRing.mem_maximalIdeal] at hg
    exact mem_nonunits_iff.mp hg
  have hne : v.adicValuation (g : F) ≠ 1 := fun h => hnotunit ((v.adicValuation_coe_eq_one_iff g).mp h)
  have hle := v.adicValuation_le_one_of_mem g.2
  have hnn : 0 ≤ v.ord (g : F) := (v.adicValuation_le_one_iff.mp hle).resolve_left hg0
  have hne0 : v.ord (g : F) ≠ 0 := by
    intro h0
    apply hne
    rw [v.adicValuation_eq_exp_neg_ord hg0, h0, neg_zero, WithZero.exp_zero]
  omega

private theorem mem_maximalIdeal_of_one_le_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0)
    (h : 1 ≤ v.ord f) :
    (⟨f, mem_valuationSubring_of_ord_nonneg v hf (by omega)⟩ : v.toValuationSubring) ∈
      maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu
  have := v.ord_coe_unit w
  rw [hw] at this
  change v.ord f = 0 at this
  omega

private theorem exists_sub_smul_mem_lSpace_sub_single
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    {D : Divisor K F} {Q : Place K F} (hQ : D Q = 0) {u : F} (hu : u ∈ LSpace D)
    (huQ : Q.ord u = 0) (hu0 : u ≠ 0) {f : F} (hf : f ∈ LSpace D) :
    ∃ c : K, f - c • u ∈ LSpace (D - Finsupp.single Q 1) := by
  classical
  have hdeg : Q.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed Q
  by_cases hf0 : f = 0
  · exact ⟨0, by rw [hf0, zero_smul, sub_zero]; exact Submodule.zero_mem _⟩
  have hfQ : 0 ≤ Q.ord f := by
    have := (mem_lSpace_iff_ord.mp hf).resolve_left hf0 Q
    rwa [hQ, neg_zero] at this
  have hfmem : f ∈ Q.toValuationSubring := mem_valuationSubring_of_ord_nonneg Q hf0 hfQ
  have humem : u ∈ Q.toValuationSubring := mem_valuationSubring_of_ord_nonneg Q hu0 huQ.ge
  obtain ⟨cf, hcf⟩ := Place.exists_sub_algebraMap_mem_maximalIdeal Q hdeg ⟨f, hfmem⟩
  obtain ⟨cu, hcu⟩ := Place.exists_sub_algebraMap_mem_maximalIdeal Q hdeg ⟨u, humem⟩
  have hcu0 : cu ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at hcu
    have h1 := one_le_ord_of_mem_maximalIdeal Q hcu hu0
    change 1 ≤ Q.ord u at h1
    omega
  refine ⟨cf / cu, ?_⟩
  set g : Q.toValuationSubring :=
    (⟨f, hfmem⟩ - algebraMap K Q.toValuationSubring cf) -
      algebraMap K Q.toValuationSubring (cf / cu) * (⟨u, humem⟩ - algebraMap K Q.toValuationSubring cu)
    with hg_def
  have hgmem : g ∈ maximalIdeal Q.toValuationSubring :=
    Ideal.sub_mem _ hcf (Ideal.mul_mem_left _ _ hcu)
  have hgF : (g : F) = f - (cf / cu) • u := by
    rw [hg_def]
    push_cast
    simp only [Place.coe_algebraMap, Algebra.smul_def]
    rw [mul_sub, ← map_mul, div_mul_cancel₀ cf hcu0]
    ring
  have hsubmem : f - (cf / cu) • u ∈ LSpace D :=
    Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hu)
  rw [mem_lSpace_iff_ord]
  by_cases h0 : f - (cf / cu) • u = 0
  · exact Or.inl h0
  right
  intro v
  by_cases hv : v = Q
  · have h1 : 1 ≤ Q.ord (g : F) := one_le_ord_of_mem_maximalIdeal Q hgmem (by rw [hgF]; exact h0)
    rw [hgF] at h1
    rw [hv, Finsupp.sub_apply, Finsupp.single_eq_same, hQ]
    omega
  · have h1 := (mem_lSpace_iff_ord.mp hsubmem).resolve_left h0 v
    rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hv), sub_zero]
    exact h1

private theorem ell_eq_ell_sub_single_add_one
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (D : Divisor K F) [FiniteDimensional K (LSpace D)] {Q : Place K F} (hQ : D Q = 0) {u : F}
    (hu : u ∈ LSpace D) (huQ : Q.ord u = 0) (hu0 : u ≠ 0) :
    ell D = ell (D - Finsupp.single Q 1) + 1 := by
  have hle : D - Finsupp.single Q 1 ≤ D := sub_le_self _ (Finsupp.single_nonneg.mpr zero_le_one)
  have hle' : LSpace (D - Finsupp.single Q 1) ≤ LSpace D := lSpace_mono hle
  haveI : FiniteDimensional K (LSpace (D - Finsupp.single Q 1)) :=
    Submodule.finiteDimensional_of_le hle'
  have hu' : u ∉ LSpace (D - Finsupp.single Q 1) := by
    intro h
    have := (mem_lSpace_iff_ord.mp h).resolve_left hu0 Q
    rw [Finsupp.sub_apply, Finsupp.single_eq_same, hQ, huQ] at this
    omega
  have hlt : LSpace (D - Finsupp.single Q 1) < LSpace D :=
    SetLike.lt_iff_le_and_exists.mpr ⟨hle', u, hu, hu'⟩
  have h1 : ell (D - Finsupp.single Q 1) < ell D := Submodule.finrank_lt_finrank_of_lt hlt
  have hsup : LSpace D ≤ (K ∙ u) ⊔ LSpace (D - Finsupp.single Q 1) := by
    intro f hf
    obtain ⟨c, hc⟩ := exists_sub_smul_mem_lSpace_sub_single hQ hu huQ hu0 hf
    have hf' : f = c • u + (f - c • u) := by abel
    rw [hf']
    exact Submodule.add_mem_sup (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u)) hc
  have h2 : ell D ≤ ell (D - Finsupp.single Q 1) + 1 := by
    calc ell D ≤ Module.finrank K ↥((K ∙ u) ⊔ LSpace (D - Finsupp.single Q 1)) :=
          Submodule.finrank_mono hsup
      _ ≤ Module.finrank K ↥(K ∙ u) + ell (D - Finsupp.single Q 1) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ = ell (D - Finsupp.single Q 1) + 1 := by rw [finrank_span_singleton hu0, add_comm]
  omega

end AlgebraicCurve.MultiGe

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.coe_algebraMap Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace genusFF IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed LSpace ell mem_lSpace_iff_ord lSpace_mono IsCurveOver.exists_separating_transcendental Place.exists_ord_sub_algebraMap_pos_of_transcendental Place.exists_sub_algebraMap_mem_maximalIdeal"
namespace MultiGe
p2m_open "AlgebraicCurve"

open IsLocalRing

private theorem aux
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (k : ℕ) :
    ∀ D : Divisor L F, FiniteDimensional L (LSpace D) → ell D = k →
      ∃ s : Fin k → F, ∃ hs : ∀ j i, s j ∈ (C i).integers,
        (∀ j, s j ∈ LSpace D) ∧
        LinearIndependent (IsLocalRing.ResidueField A) (fun j => fun i => (C i).residue ⟨s j, hs j i⟩) := by
  classical
  have _ := hrk; have _ := hgenus; have _ := hnodes; have _ := hratF; have _ := hw; have _ := hpair; have _ := hπ0
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := A.isAlgClosed_residueField_of_isAlgClosed
  induction k with
  | zero =>
    intro D _ _
    exact ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, linearIndependent_empty_type⟩
  | succ k ih =>
    intro D hFD hD
    haveI := hFD

    have hne : LSpace D ≠ ⊥ := by
      intro hbot
      have h0 : ell D = 0 := by
        unfold ell
        rw [hbot, finrank_bot]
      omega
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne

    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with hn0 | hpos
      · exfalso
        subst hn0
        have hempty : ∀ P : Place L F, False := by
          intro P
          rcases hcover P with ⟨i, -⟩ | ⟨e, -⟩
          · exact i.elim0
          · exact (src e).elim0
        haveI : IsEmpty (Place L F) := ⟨hempty⟩
        haveI : Infinite (Place L F) := infinite_place_of_isCurveOver L F (fun v => (hempty v).elim)
        exact (hempty (Classical.arbitrary (Place L F))).elim
      · exact hpos

    have hsc : ∀ i, ∃ c : L, ∃ h : c • f ∈ (C i).integers, (C i).residue ⟨c • f, h⟩ ≠ 0 :=
      fun i => (C i).exists_smul_mem f hf0
    choose c hc hcres using hsc
    have hc0 : ∀ i, c i ≠ 0 := by
      intro i h0
      apply hcres i
      have : (⟨c i • f, hc i⟩ : (C i).integers) = 0 := Subtype.ext (by simp [h0])
      rw [this, map_zero]
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => A.valuation (c i))
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    set u : F := c i₀ • f with hu_def
    have hratio : ∀ i, c i₀ / c i ∈ A := by
      intro i
      rw [← A.valuation_le_one_iff, map_div₀, div_le_one₀ ((Valuation.pos_iff _).mpr (hc0 i))]
      exact hi₀ i (Finset.mem_univ i)
    have huint : ∀ i, u ∈ (C i).integers := by
      intro i
      have : u = algebraMap L F (c i₀ / c i) * (c i • f) := by
        rw [hu_def, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hc0 i)]
      rw [this]
      exact mul_mem (((C i).algebraMap_mem_iff _).mpr (hratio i)) (hc i)
    have hures : (C i₀).residue ⟨u, huint i₀⟩ ≠ 0 := by
      have : (⟨u, huint i₀⟩ : (C i₀).integers) = ⟨c i₀ • f, hc i₀⟩ := Subtype.ext rfl
      rw [this]; exact hcres i₀
    have huD : u ∈ LSpace D := (LSpace D).smul_mem (c i₀) hf
    have hu0 : u ≠ 0 := smul_ne_zero (hc0 i₀) hf0

    obtain ⟨E, hE, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) u hu0

    haveI : Infinite (Place (IsLocalRing.ResidueField A) (Fbar i₀)) :=
      infinite_place_of_isCurveOver (IsLocalRing.ResidueField A) (Fbar i₀) (hratBar i₀)
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
      ((C i₀).nodes ∪ E.support.image (C i₀).placeMap ∪ D.support.image (C i₀).placeMap)
    simp only [Finset.mem_union, not_or] at hy
    obtain ⟨⟨hyn, hyE⟩, hyD⟩ := hy

    obtain ⟨T, hT, -, -, -, huniq⟩ := hdisc i₀ y hyn
    obtain ⟨Q, ⟨hQdom, hQmap, -⟩, -⟩ := huniq π hπ
    have hQE : Q ∉ E.support := fun h0 => hyE (Finset.mem_image.mpr ⟨Q, h0, hQmap⟩)
    have hQD : Q ∉ D.support := fun h0 => hyD (Finset.mem_image.mpr ⟨Q, h0, hQmap⟩)
    have hDQ : D Q = 0 := Finsupp.notMem_support_iff.mp hQD
    have huQ : Q.ord u = 0 := by rw [← hE Q]; exact Finsupp.notMem_support_iff.mp hQE

    have hres_ord : y.ord ((C i₀).residue ⟨u, huint i₀⟩) = 0 := by
      have hmap := (C i₀).mapDomain_placeMap ⟨u, huint i₀⟩ hures (E.filter fun P => P ∈ (C i₀).dom)
        (fun P hP => by rw [Finsupp.filter_apply, if_pos hP, hE]) (fun P hP => by rw [Finsupp.filter_apply, if_neg hP])
        y hyn
      rw [← hmap]
      apply Finsupp.notMem_support_iff.mp
      intro h0
      obtain ⟨P, hP, hPy⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h0)
      rw [Finsupp.support_filter, Finset.mem_filter] at hP
      exact hyE (Finset.mem_image.mpr ⟨P, hP.1, hPy⟩)

    have hell : ell (D - Finsupp.single Q 1) = k := by
      have := ell_eq_ell_sub_single_add_one D hDQ huD huQ hu0
      omega
    have hle : D - Finsupp.single Q 1 ≤ D := sub_le_self _ (Finsupp.single_nonneg.mpr zero_le_one)
    haveI : FiniteDimensional L (LSpace (D - Finsupp.single Q 1)) :=
      Submodule.finiteDimensional_of_le (lSpace_mono hle)
    obtain ⟨s, hs, hs1, hs2⟩ := ih (D - Finsupp.single Q 1) inferInstance hell

    have hvan : ∀ j, (C i₀).residue ⟨s j, hs j i₀⟩ ≠ 0 →
        y.adicValuation ((C i₀).residue ⟨s j, hs j i₀⟩) < 1 := by
      intro j hj
      have ht0 : s j ≠ 0 := by
        intro h0; apply hj
        have : (⟨s j, hs j i₀⟩ : (C i₀).integers) = 0 := Subtype.ext h0
        rw [this, map_zero]
      obtain ⟨Dt, hDt, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (s j) ht0
      have hmap := (C i₀).mapDomain_placeMap ⟨s j, hs j i₀⟩ hj (Dt.filter fun P => P ∈ (C i₀).dom)
        (fun P hP => by rw [Finsupp.filter_apply, if_pos hP, hDt]) (fun P hP => by rw [Finsupp.filter_apply, if_neg hP])
        y hyn
      have hordt := (mem_lSpace_iff_ord.mp (hs1 j)).resolve_left ht0

      have hQt : 1 ≤ Q.ord (s j) := by
        have := hordt Q
        rw [Finsupp.sub_apply, Finsupp.single_eq_same, hDQ] at this
        omega
      have hge : 1 ≤ Finsupp.mapDomain (C i₀).placeMap (Dt.filter fun P => P ∈ (C i₀).dom) y := by
        simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
        have hQs : Q ∈ (Dt.filter fun P => P ∈ (C i₀).dom).support := by
          rw [Finsupp.mem_support_iff, Finsupp.filter_apply, if_pos hQdom, hDt]; omega
        refine le_trans ?_ (Finset.single_le_sum (f := fun P => if (C i₀).placeMap P = y then
          (Dt.filter fun P => P ∈ (C i₀).dom) P else 0) (fun P hP => ?_) hQs)
        · show 1 ≤ (if (C i₀).placeMap Q = y then (Dt.filter fun P => P ∈ (C i₀).dom) Q else 0)
          rw [if_pos hQmap, Finsupp.filter_apply, if_pos hQdom, hDt]; exact hQt
        · skip
          split_ifs with hPy
          · rw [Finsupp.support_filter, Finset.mem_filter] at hP
            rw [Finsupp.filter_apply, if_pos hP.2, hDt]
            have hPD : P ∉ D.support := fun h0 => hyD (Finset.mem_image.mpr ⟨P, h0, hPy⟩)
            have := hordt P
            rw [Finsupp.sub_apply, Finsupp.notMem_support_iff.mp hPD, Finsupp.single_apply] at this
            split_ifs at this <;> omega
          · exact le_refl _
      rw [hmap] at hge
      rw [y.adicValuation_eq_exp_neg_ord hj, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega

    have hs' : ∀ (j : Fin (k + 1)) i, (Fin.cons u s : Fin (k + 1) → F) j ∈ (C i).integers := fun j i =>
      Fin.cases (motive := fun j => (Fin.cons u s : Fin (k + 1) → F) j ∈ (C i).integers) (huint i) (fun j' => hs j' i) j
    refine ⟨Fin.cons u s, hs', fun j => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j' => ?_) j
      · exact huD
      · exact lSpace_mono hle (hs1 j')
    · have hcomp : (fun j => fun i => (C i).residue ⟨(Fin.cons u s : Fin (k + 1) → F) j, hs' j i⟩) =
          Fin.cons (fun i => (C i).residue ⟨u, huint i⟩) (fun j' => fun i => (C i).residue ⟨s j', hs j' i⟩) := by
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · rfl
        · rfl
      rw [hcomp, linearIndependent_finCons]
      refine ⟨hs2, fun hmem => ?_⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
      have ha₀ := congrFun ha i₀
      simp only [Finset.sum_apply, Pi.smul_apply] at ha₀

      have hlt : y.adicValuation (∑ j, a j • (C i₀).residue ⟨s j, hs j i₀⟩) < 1 := by
        apply Finset.sum_induction _ (fun x => y.adicValuation x < 1)
        · intro x₁ x₂ h₁ h₂; exact Valuation.map_add_lt _ h₁ h₂
        · simp
        · intro j _
          by_cases hj : (C i₀).residue ⟨s j, hs j i₀⟩ = 0
          · rw [hj, smul_zero, map_zero]; exact zero_lt_one
          · rw [Algebra.smul_def, map_mul]
            calc y.adicValuation (algebraMap _ _ (a j)) * y.adicValuation ((C i₀).residue ⟨s j, hs j i₀⟩)
                ≤ 1 * y.adicValuation ((C i₀).residue ⟨s j, hs j i₀⟩) :=
                  mul_le_mul_left (y.adicValuation_algebraMap_le_one (a j)) _
              _ < 1 := by rw [one_mul]; exact hvan j hj
      rw [ha₀, y.adicValuation_eq_exp_neg_ord hures, hres_ord, neg_zero, WithZero.exp_zero] at hlt
      exact lt_irrefl _ hlt

end AlgebraicCurve.MultiGe

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (D : Divisor L F)
    :
    ∃ s : Fin (Module.finrank L (riemannRochSpace D)) → F,
      ∃ hs : ∀ j i, s j ∈ (C i).integers,
        (∀ j, s j ∈ riemannRochSpace D) ∧
        LinearIndependent (IsLocalRing.ResidueField A) (fun j => fun i => (C i).residue ⟨s j, hs j i⟩)  := by
  classical
  by_cases hfd : FiniteDimensional L (LSpace D)
  · obtain ⟨s, hs, h1, h2⟩ := AlgebraicCurve.MultiGe.aux A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt
      w hpair hw hatt hnodes hcover hdisc hgenus (ell D) D hfd rfl
    exact ⟨s, hs, h1, h2⟩
  · have h0 : Module.finrank L (riemannRochSpace D) = 0 := Module.finrank_of_not_finite hfd
    haveI : IsEmpty (Fin (Module.finrank L (riemannRochSpace D))) := ⟨fun j => absurd j.2 (by omega)⟩
    exact ⟨fun _ => 0, fun _ i => zero_mem _, fun _ => zero_mem _, linearIndependent_empty_type⟩

end S_AlgebraicCurve_SemistableCovering_exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne (solution)
