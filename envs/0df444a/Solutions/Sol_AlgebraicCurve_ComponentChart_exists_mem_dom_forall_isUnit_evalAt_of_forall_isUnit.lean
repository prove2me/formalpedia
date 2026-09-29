-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.exists_mem_dom_forall_isUnit_evalAt_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/2cbfd25d-c439-523f-95d1-7c4bbb2a75ef

import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_exists_mem_dom_forall_isUnit_evalAt_of_forall_isUnit
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace ChartUnitAux

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isUnit_of_ord_eq_zero (v : Place K F) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ hm : f ∈ v.toValuationSubring, IsUnit (⟨f, hm⟩ : v.toValuationSubring) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hϖ
  rw [h, zpow_zero, mul_one] at hu
  refine ⟨hu ▸ (u : v.toValuationSubring).2, ?_⟩
  have : (⟨f, hu ▸ (u : v.toValuationSubring).2⟩ : v.toValuationSubring) = (u : v.toValuationSubring) :=
    Subtype.ext hu
  rw [this]
  exact Units.isUnit u

theorem mem_of_ord_eq_zero (v : Place K F) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    f ∈ v.toValuationSubring :=
  (isUnit_of_ord_eq_zero v hf h).1

theorem isUnit_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  by_contra hu
  apply h
  have hmem : (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
    (IsLocalRing.mem_maximalIdeal _).mpr hu
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  have key := v.algebraMap_evalAt hv hf
  rw [hres] at key
  exact (algebraMap K v.ResidueField).injective (by rw [key, map_zero])

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  obtain ⟨u, hu⟩ := isUnit_of_evalAt_ne_zero v hv hf h
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem evalAt_sub (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply (algebraMap K v.ResidueField).injective
  rw [map_sub, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    v.algebraMap_evalAt hv (sub_mem hf hg)]
  rfl

theorem evalAt_pow (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (n : ℕ) : v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp [Place.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul hv (pow_mem hf n) hf, ih]

theorem ord_prod {ι : Type*} (v : Place K F) (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem zpow_mem_and_inv_mem (V : ValuationSubring F) {u : F} (hu : u ∈ V) (hu' : u⁻¹ ∈ V) (n : ℤ) :
    u ^ n ∈ V ∧ (u ^ n)⁻¹ ∈ V := by
  rcases n with (n | n)
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact ⟨pow_mem hu n, by rw [← inv_pow]; exact pow_mem hu' n⟩
  · simp only [zpow_negSucc]
    exact ⟨by rw [← inv_pow]; exact pow_mem hu' (n + 1), by rw [inv_inv]; exact pow_mem hu (n + 1)⟩

theorem prod_mem_and_inv_mem {ι : Type*} (V : ValuationSubring F) (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ V ∧ (f i)⁻¹ ∈ V) :
    (∏ i ∈ s, f i) ∈ V ∧ (∏ i ∈ s, f i)⁻¹ ∈ V := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [one_mem]
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha]
    refine ⟨mul_mem h1.1 h2.1, ?_⟩
    rw [mul_inv]
    exact mul_mem h1.2 h2.2

end ChartUnitAux

open ChartUnitAux in

theorem solution
    {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (hfin : ∀ f : F, f ≠ 0 → Set.Finite {P : Place L F | P.ord f ≠ 0})
    (hfinb : ∀ g : Fbar, g ≠ 0 → Set.Finite {Q : Place (ResidueField A) Fbar | Q.ord g ≠ 0})
    (hinf : Set.Infinite (Set.univ : Set (Place (ResidueField A) Fbar)))
    (C : ComponentChart A F Fbar) (hrat : ∀ P ∈ C.dom, P.IsRational)
    {ι : Type} [Fintype ι] (f : ι → F) (hf : ∀ i, ∃ h : f i ∈ C.integers, IsUnit (⟨f i, h⟩ : C.integers)) :
    ∃ P ∈ C.dom, ∀ i, f i ∈ P.toValuationSubring ∧ ∃ h : P.evalAt (f i) ∈ A, IsUnit (⟨_, h⟩ : A) := by
  classical

  have hfne : ∀ i, f i ≠ 0 := by
    intro i h0
    obtain ⟨h, hu⟩ := hf i
    apply hu.ne_zero
    exact Subtype.ext h0
  have hres : ∀ i, C.residue ⟨f i, (hf i).1⟩ ≠ 0 := by
    intro i h0
    obtain ⟨h, hu⟩ := hf i
    have hker : (⟨f i, h⟩ : C.integers) ∈ RingHom.ker C.residue := h0
    rw [C.ker_residue] at hker
    exact (IsLocalRing.mem_maximalIdeal _).mp hker hu

  set B₁ : Set (Place (ResidueField A) Fbar) := ⋃ i, {Q | Q.ord (C.residue ⟨f i, (hf i).1⟩) ≠ 0} with hB₁
  set B₂ : Set (Place (ResidueField A) Fbar) := ⋃ i, C.placeMap '' {P | P.ord (f i) ≠ 0} with hB₂
  have hB₁f : B₁.Finite := Set.finite_iUnion fun i => hfinb _ (hres i)
  have hB₂f : B₂.Finite := Set.finite_iUnion fun i => (hfin _ (hfne i)).image _
  have hBf : ((C.nodes : Set _) ∪ B₁ ∪ B₂).Finite := ((C.nodes.finite_toSet).union hB₁f).union hB₂f
  obtain ⟨Qb, -, hQb⟩ := (hinf.diff hBf).nonempty
  simp only [Set.mem_union, not_or, Finset.mem_coe] at hQb
  obtain ⟨⟨hQnode, hQB₁⟩, hQB₂⟩ := hQb

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Qb.toValuationSubring
  have hϖne : ((ϖ : Qb.toValuationSubring) : Fbar) ≠ 0 := by
    intro h0; exact hϖ.ne_zero (Subtype.ext h0)
  have hϖord : Qb.ord ((ϖ : Qb.toValuationSubring) : Fbar) = 1 := Qb.ord_coe_irreducible hϖ
  obtain ⟨u, hu⟩ := C.residue_surjective ((ϖ : Qb.toValuationSubring) : Fbar)
  have hune : C.residue u ≠ 0 := by rw [hu]; exact hϖne
  have huF : (u : F) ≠ 0 := by
    intro h0; apply hune
    have : u = 0 := Subtype.ext h0
    rw [this, map_zero]

  set S : Finset (Place L F) := (hfin (u : F) huF).toFinset.filter (fun P => P ∈ C.dom) with hSdef
  set D : Divisor L F := ∑ P ∈ S, Finsupp.single P (P.ord (u : F)) with hDdef
  have hDapply : ∀ P, D P = if P ∈ S then P.ord (u : F) else 0 := by
    intro P
    simp only [hDdef, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hD1 : ∀ P ∈ C.dom, D P = P.ord (u : F) := by
    intro P hP
    rw [hDapply]
    by_cases hPS : P ∈ S
    · rw [if_pos hPS]
    · rw [if_neg hPS]
      by_contra h
      exact hPS (by rw [Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨fun h' => h h'.symm, hP⟩)
  have hD2 : ∀ P, P ∉ C.dom → D P = 0 := by
    intro P hP
    rw [hDapply, if_neg]
    intro hPS
    rw [Finset.mem_filter] at hPS
    exact hP hPS.2
  have hmap := C.mapDomain_placeMap u hune D hD1 hD2 Qb hQnode
  rw [hu, hϖord] at hmap

  have hsupp : Qb ∈ (Finsupp.mapDomain C.placeMap D).support := by
    rw [Finsupp.mem_support_iff, hmap]; exact one_ne_zero
  obtain ⟨P, hPD, hPQ⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hsupp)
  have hPdom : P ∈ C.dom := by
    by_contra h
    rw [Finsupp.mem_support_iff, hD2 P h] at hPD
    exact hPD rfl
  refine ⟨P, hPdom, fun i => ?_⟩

  have hfib : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → f i ∈ w.toValuationSubring := by
    intro w hw hwP
    apply mem_of_ord_eq_zero w (hfne i)
    by_contra hord
    apply hQB₂
    rw [hB₂, Set.mem_iUnion]
    exact ⟨i, w, hord, by rw [hwP, hPQ]⟩
  obtain ⟨hm, hA, hcomp⟩ := C.pointwise P hPdom (hrat P hPdom) (f i) (hf i).1 hfib
  refine ⟨hfib P hPdom rfl, hA, ?_⟩

  by_contra hnu
  have hmax : (⟨P.evalAt (f i), hA⟩ : A) ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have hres0 : IsLocalRing.residue A ⟨P.evalAt (f i), hA⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  rw [hres0, map_zero] at hcomp

  have hordQ : Qb.ord (C.residue ⟨f i, (hf i).1⟩) = 0 := by
    by_contra h
    apply hQB₁
    rw [hB₁, Set.mem_iUnion]
    exact ⟨i, h⟩
  subst hPQ
  obtain ⟨hm', hunit⟩ := isUnit_of_ord_eq_zero (C.placeMap P) (hres i) hordQ
  exact (IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp hcomp.symm) hunit

end S_AlgebraicCurve_ComponentChart_exists_mem_dom_forall_isUnit_evalAt_of_forall_isUnit
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_exists_mem_dom_forall_isUnit_evalAt_of_forall_isUnit (solution)
