-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/31d0865b-e264-518d-bb26-310436d82a6e

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits
import Theorems.Thm_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective.AlgebraicCurve IsLocalRing Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation Place Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "integers residue_algebraMap algebraMap_mem_iff residue existsUnique_place_forall_residue_sub_mem_nonunits ord_residue_le_sum_ord_of_isIntegral_adjoin sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin"
namespace AJDM
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

section places

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem mem_of_isIntegral_adjoin (P : Place L F) {j f : F} (hj : j ∈ P.toValuationSubring)
    (hf : IsIntegral (Algebra.adjoin L {j}) f) : f ∈ P.toValuationSubring := by
  obtain ⟨p, hpm, hpev⟩ := hf
  have hle : ∀ y : F, y ∈ Algebra.adjoin L {j} → y ∈ P.toValuationSubring := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff.mp hz]; exact hj
    | algebraMap c => exact P.algebraMap_mem' c
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  refine P.mem_of_eval_monic_eq_zero (P := p.map (algebraMap (Algebra.adjoin L {j}) F))
    (hpm.map _) (fun i => ?_) ?_
  · rw [coeff_map]; exact hle _ (p.coeff i).2
  · rwa [eval_map]

theorem ord_nonneg_of_mem (P : Place L F) {f : F} (hf : f ∈ P.toValuationSubring) :
    0 ≤ P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  by_cases hu : IsUnit (⟨f, hf⟩ : P.toValuationSubring)
  · obtain ⟨u, hu⟩ := hu
    have := P.ord_coe_unit u
    rw [hu] at this
    exact this.symm.le
  · exact ((P.mem_maximalIdeal_iff_ord_pos hf0 hf).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr hu)).le

end places

section main

variable {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

def Dom (y : F) (P : Place L F) : Prop :=
  ∃ a : A, y - algebraMap L F a ∈ P.toValuationSubring.nonunits

def Red (R : RegularProlongation A F Fbar) (y : F) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) : Prop :=
  ∀ h : R.integers, IsIntegral (Algebra.adjoin L {y}) (h : F) →
    ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
      R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
        Q.toValuationSubring.nonunits

variable {A}

theorem isIntegral_of_mem {y h : F} (hh : h ∈ Algebra.adjoin L {y}) :
    IsIntegral (Algebra.adjoin L {y}) h :=
  isIntegral_algebraMap (x := (⟨h, hh⟩ : Algebra.adjoin L {y}))

theorem isIntegral_self (y : F) : IsIntegral (Algebra.adjoin L {y}) y :=
  isIntegral_of_mem (Algebra.self_mem_adjoin_singleton L y)

theorem mem_of_dom {y : F} {P : Place L F} (hd : Dom A y P) : y ∈ P.toValuationSubring := by
  obtain ⟨a, ha⟩ := hd
  have h1 := ValuationSubring.nonunits_subset ha
  have h2 := P.algebraMap_mem' (a : L)
  simpa using add_mem h1 h2

theorem residue_mem_of_red (R : RegularProlongation A F Fbar) (y : R.integers) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hd : Dom A (y : F) P)
    (hred : Red A R y P Q) : R.residue y ∈ Q.toValuationSubring := by
  obtain ⟨a, ha⟩ := hd
  have h1 := ValuationSubring.nonunits_subset (hred y (isIntegral_self (y : F)) a ha)
  have h2 := Q.algebraMap_mem' (IsLocalRing.residue A a)
  simpa using add_mem h1 h2

variable [IsAlgClosed L] [IsCurveOver L F] [IsCurveOver (IsLocalRing.ResidueField A) Fbar]

theorem integral_case (R : RegularProlongation A F Fbar)
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
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (T : Finset (Place L F))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧ Dom A (x : F) P ∧ Red A R (x : F) P Q)) :
    ∑ P ∈ T, D P = Q.ord (R.residue f) := by
  classical
  set k := IsLocalRing.ResidueField A

  obtain ⟨Dbar, hDbar, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) (R.residue f) hf

  have hE : ∀ P : Place L F, Dom A (x : F) P → ∃! Q', Red A R (x : F) P Q' := fun P hP =>
    RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits
      A R x hx hfin hdeg hchart P hP
  let ρ : Place L F → Place k Fbar := fun P =>
    if h : Dom A (x : F) P then (hE P h).exists.choose else Q
  have hρ : ∀ P, Dom A (x : F) P → Red A R (x : F) P (ρ P) := fun P h => by
    simp only [ρ, dif_pos h]
    exact (hE P h).exists.choose_spec
  have hρeq : ∀ P Q', Dom A (x : F) P → (Red A R (x : F) P Q' ↔ ρ P = Q') := fun P Q' h =>
    ⟨fun hred => (hE P h).unique (hρ P h) hred, fun he => he ▸ hρ P h⟩

  have hnonneg : ∀ P, Dom A (x : F) P → 0 ≤ D P := fun P hP => by
    rw [hD]
    exact ord_nonneg_of_mem P (mem_of_isIntegral_adjoin P (mem_of_dom hP) hfi)

  let TP : Finset (Place L F) := D.support.filter fun P => Dom A (x : F) P
  let TQ : Finset (Place k Fbar) := Dbar.support.filter fun Q' => R.residue x ∈ Q'.toValuationSubring
  have hTP : ∀ P, P ∈ TP ↔ (D P ≠ 0 ∧ Dom A (x : F) P) := fun P => by
    simp only [TP, Finset.mem_filter, Finsupp.mem_support_iff]
  have hTQ : ∀ Q', Q' ∈ TQ ↔ (Dbar Q' ≠ 0 ∧ R.residue x ∈ Q'.toValuationSubring) := fun Q' => by
    simp only [TQ, Finset.mem_filter, Finsupp.mem_support_iff]

  have hfib : ∀ Q' P, P ∈ TP.filter (fun P => ρ P = Q') ↔
      (D P ≠ 0 ∧ Dom A (x : F) P ∧ Red A R (x : F) P Q') := fun Q' P => by
    rw [Finset.mem_filter, hTP]
    constructor
    · rintro ⟨⟨h0, hd⟩, he⟩; exact ⟨h0, hd, (hρeq P Q' hd).mpr he⟩
    · rintro ⟨h0, hd, hred⟩; exact ⟨⟨h0, hd⟩, (hρeq P Q' hd).mp hred⟩

  have hMle : ∀ Q', R.residue x ∈ Q'.toValuationSubring →
      Dbar Q' ≤ ∑ P ∈ TP.filter (fun P => ρ P = Q'), D P := fun Q' hQ' => by
    rw [hDbar]
    exact RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin A R x hx hfin hdeg
      hchart f hfi hf Q' hQ' D hD _ (hfib Q')

  have hG : ∑ P ∈ TP, D P = ∑ Q' ∈ TQ, Dbar Q' :=
    RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin A R x hx hfin hdeg
      hchart f hfi hf D hD Dbar hDbar TP hTP TQ hTQ

  let TP' : Finset (Place L F) := TP.filter fun P => ρ P ∈ TQ
  have h12 : ∑ Q' ∈ TQ, Dbar Q' ≤ ∑ Q' ∈ TQ, ∑ P ∈ TP.filter (fun P => ρ P = Q'), D P :=
    Finset.sum_le_sum fun Q' hQ' => hMle Q' ((hTQ Q').mp hQ').2
  have h23 : ∑ Q' ∈ TQ, ∑ P ∈ TP.filter (fun P => ρ P = Q'), D P = ∑ P ∈ TP', D P := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := TP') (t := TQ) (g := ρ)
      (fun P hP => (Finset.mem_filter.mp hP).2)]
    refine Finset.sum_congr rfl fun Q' hQ' => Finset.sum_congr ?_ fun _ _ => rfl
    ext P
    simp only [TP', Finset.mem_filter]
    constructor
    · rintro ⟨hP, he⟩; exact ⟨⟨hP, he ▸ hQ'⟩, he⟩
    · rintro ⟨⟨hP, -⟩, he⟩; exact ⟨hP, he⟩
  have h34 : ∑ P ∈ TP', D P ≤ ∑ P ∈ TP, D P :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun P hP _ => hnonneg P ((hTP P).mp hP).2
  have h31 : ∑ P ∈ TP', D P = ∑ Q' ∈ TQ, Dbar Q' :=
    le_antisymm (h34.trans hG.le) (h12.trans h23.le)

  have hterm : ∀ Q' ∈ TQ, Dbar Q' = ∑ P ∈ TP.filter (fun P => ρ P = Q'), D P := by
    have heq : ∑ Q' ∈ TQ, Dbar Q' = ∑ Q' ∈ TQ, ∑ P ∈ TP.filter (fun P => ρ P = Q'), D P :=
      le_antisymm h12 (h23.trans_le h31.le)
    exact (Finset.sum_eq_sum_iff_of_le fun Q' hQ' => hMle Q' ((hTQ Q').mp hQ').2).mp heq

  have hall : ∀ P ∈ TP, ρ P ∈ TQ := by
    intro P hP
    by_contra hnot
    have hsplit := Finset.sum_filter_add_sum_filter_not TP (fun P => ρ P ∈ TQ) (fun P => D P)
    have hzero : ∑ P ∈ TP.filter (fun P => ρ P ∉ TQ), D P = 0 := by
      have := h31.trans hG.symm
      change ∑ P ∈ TP', D P + _ = _ at hsplit
      omega
    have hP' : P ∈ TP.filter (fun P => ρ P ∉ TQ) := Finset.mem_filter.mpr ⟨hP, hnot⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg fun P' hP' =>
      hnonneg P' ((hTP P').mp (Finset.mem_filter.mp hP').1).2).mp hzero P hP'
    exact ((hTP P).mp hP).1 this

  have hTeq : T = TP.filter (fun P => ρ P = Q) := by
    ext P; rw [hT, hfib]
  by_cases hQT : Q ∈ TQ
  · rw [hTeq, ← hterm Q hQT, hDbar]
  · have h0 : Dbar Q = 0 := by
      by_contra hne
      exact hQT ((hTQ Q).mpr ⟨hne, hQ⟩)
    have hTempty : T = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun P hP => hQT ?_
      rw [hTeq, Finset.mem_filter] at hP
      exact hP.2 ▸ hall P hP.1
    rw [hTempty, Finset.sum_empty, ← hDbar, h0]

end main

section step0

open scoped IntermediateField.algebraAdjoinAdjoin

private theorem _root_.AlgebraicCurve.RegularProlongation.AJDM.exists_integral_multiple {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (y : F) (hfin : 0 < Module.finrank (IntermediateField.adjoin L ({y} : Set F)) F) (f : F) :
    ∃ p : L[X], p ≠ 0 ∧ IsIntegral (Algebra.adjoin L {y}) (aeval y p * f) := by
  haveI : Module.Finite (IntermediateField.adjoin L ({y} : Set F)) F :=
    Module.finite_of_finrank_pos hfin
  have halg : IsAlgebraic (IntermediateField.adjoin L ({y} : Set F)) f :=
    Algebra.IsAlgebraic.isAlgebraic f
  have halg' : IsAlgebraic (Algebra.adjoin L ({y} : Set F)) f :=
    IsAlgebraic.restrictScalars (S := IntermediateField.adjoin L ({y} : Set F)) (A := F) _ halg
  obtain ⟨z, hz0, hz⟩ := halg'.exists_integral_multiple
  obtain ⟨p, hp⟩ : ∃ p : L[X], aeval y p = (z : F) := Algebra.adjoin_eq_exists_aeval _ y z
  refine ⟨p, ?_, ?_⟩
  · rintro rfl
    apply hz0
    ext
    rw [← hp, map_zero]; rfl
  · rw [Algebra.smul_def] at hz
    change IsIntegral _ ((z : F) * f) at hz
    rwa [← hp] at hz

p2m_export "AlgebraicCurve.RegularProlongation.AJDM" "exists_integral_multiple"

theorem exists_rescale {L : Type*} [Field L] (A : ValuationSubring L) {p : L[X]} (hp : p ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ a : ℕ → A, (∀ i, (a i : L) = c * p.coeff i) ∧ ∃ i₀, a i₀ = 1 := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := p.support.exists_max_image (fun i => A.valuation (p.coeff i))
    (Polynomial.support_nonempty.mpr hp)
  have hc0 : p.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  have hmem : ∀ i, (p.coeff i₀)⁻¹ * p.coeff i ∈ A := by
    intro i
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hi : i ∈ p.support
    · rw [inv_mul_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc0))]
      exact hmax i hi
    · rw [Polynomial.notMem_support_iff.mp hi, map_zero, mul_zero]
      exact zero_le'
  refine ⟨(p.coeff i₀)⁻¹, inv_ne_zero hc0, fun i => ⟨_, hmem i⟩, fun i => rfl, i₀, ?_⟩
  ext
  simp [hc0]

variable {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsAlgClosed L] [IsCurveOver L F] [IsCurveOver (IsLocalRing.ResidueField A) Fbar]

theorem main (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hf : R.residue f ≠ 0)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (T : Finset (Place L F))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧ Dom A (x : F) P ∧ Red A R (x : F) P Q)) :
    ∑ P ∈ T, D P = Q.ord (R.residue f) := by
  classical

  have hfinL : 0 < Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    hdeg ▸ hfin
  obtain ⟨p, hp0, hpf⟩ := exists_integral_multiple (x : F) hfinL (f : F)
  obtain ⟨c, hc0, a, ha, i₀, hi₀⟩ := exists_rescale A hp0

  let cst : A → R.integers := fun b => ⟨algebraMap L F b, (R.algebraMap_mem_iff b).mpr b.2⟩
  let q₀ : R.integers := ∑ i ∈ Finset.range (p.natDegree + 1), cst (a i) * x ^ i
  have hq₀F : (q₀ : F) = algebraMap L F c * aeval (x : F) p := by
    simp only [q₀, cst]
    rw [aeval_eq_sum_range, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i, map_mul, Algebra.smul_def, mul_assoc]

  let pbar : (IsLocalRing.ResidueField A)[X] := ∑ i ∈ Finset.range (p.natDegree + 1),
    Polynomial.monomial i (IsLocalRing.residue A (a i))
  have hres_q₀ : R.residue q₀ = aeval (R.residue x) pbar := by
    simp only [q₀, pbar, map_sum, map_mul, map_pow, aeval_monomial, cst, R.residue_algebraMap]
  have hi₀mem : i₀ ∈ Finset.range (p.natDegree + 1) := by
    refine Finset.mem_range_succ_iff.mpr (Polynomial.le_natDegree_of_ne_zero fun h => ?_)
    have := ha i₀
    rw [hi₀, h, mul_zero] at this
    exact one_ne_zero (by exact_mod_cast this)
  have hpbar : pbar.coeff i₀ = 1 := by
    simp only [pbar, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i₀, if_pos rfl, hi₀, map_one]
    · intro j _ hj; exact if_neg hj
    · intro h; exact absurd hi₀mem h
  have hpbar0 : pbar ≠ 0 := fun h => by simp [h] at hpbar
  have hres_q₀_ne : R.residue q₀ ≠ 0 := by
    rw [hres_q₀]
    exact fun h => hx ⟨pbar, hpbar0, h⟩

  let g : R.integers := q₀ * f
  have hres_g_ne : R.residue g ≠ 0 := by
    simp only [g, map_mul]
    exact mul_ne_zero hres_q₀_ne hf
  have hcmem : algebraMap L F c ∈ Algebra.adjoin L {(x : F)} := Subalgebra.algebraMap_mem _ c
  have hq₀_int : IsIntegral (Algebra.adjoin L {(x : F)}) (q₀ : F) := by
    refine isIntegral_of_mem ?_
    rw [hq₀F]
    exact mul_mem hcmem (Polynomial.aeval_mem_adjoin_singleton L (x : F))
  have hg_int : IsIntegral (Algebra.adjoin L {(x : F)}) (g : F) := by
    have : (g : F) = algebraMap L F c * (aeval (x : F) p * f) := by
      simp only [g]
      push_cast
      rw [hq₀F, mul_assoc]
    rw [this]
    exact (isIntegral_of_mem hcmem).mul hpf
  have hq₀0 : (q₀ : F) ≠ 0 := fun h =>
    hres_q₀_ne (by rw [show q₀ = 0 from Subtype.ext h, map_zero])
  have hg0 : (g : F) ≠ 0 := fun h =>
    hres_g_ne (by rw [show g = 0 from Subtype.ext h, map_zero])

  obtain ⟨Dg, hDg, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (g : F) hg0
  obtain ⟨Dq, hDq, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (q₀ : F) hq₀0
  have hDeq : D = Dg - Dq := by
    ext P
    rw [Finsupp.sub_apply, hD, hDg, hDq]
    have : (f : F) = (g : F) * (q₀ : F)⁻¹ := by
      simp only [g]
      push_cast
      field_simp
    rw [this, P.ord_mul hg0 (inv_ne_zero hq₀0), P.ord_inv]
    ring
  have hres_eq : Q.ord (R.residue f) = Q.ord (R.residue g) - Q.ord (R.residue q₀) := by
    have : R.residue f = R.residue g * (R.residue q₀)⁻¹ := by
      simp only [g, map_mul]
      field_simp
    rw [this, Q.ord_mul hres_g_ne (inv_ne_zero hres_q₀_ne), Q.ord_inv]
    ring
  let c' : Place L F → Prop := fun P => Dom A (x : F) P ∧ Red A R (x : F) P Q
  let Φ : Divisor L F → ℤ := fun E => ∑ P ∈ E.support.filter c', E P
  have hΦ : ∀ E : Divisor L F, Φ E = E.sum fun P n => if c' P then n else 0 := fun E => by
    simp only [Φ, Finsupp.sum, Finset.sum_filter]
  have hΦsub : Φ (Dg - Dq) = Φ Dg - Φ Dq := by
    rw [hΦ, hΦ, hΦ, Finsupp.sum_sub_index]
    intro P b₁ b₂
    split_ifs <;> simp
  have hmemT : ∀ (E : Divisor L F) (P : Place L F), P ∈ E.support.filter c' ↔
      (E P ≠ 0 ∧ Dom A (x : F) P ∧ Red A R (x : F) P Q) := fun E P => by
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, c']
  have hTeq : ∑ P ∈ T, D P = Φ D := by
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext P
    rw [hT, hmemT]
  rw [hTeq, hDeq, hΦsub, hres_eq]
  exact congrArg₂ (· - ·)
    (integral_case R x hx hfin hdeg hchart g hg_int hres_g_ne Q hQ Dg hDg _ (hmemT Dg))
    (integral_case R x hx hfin hdeg hchart q₀ hq₀_int hres_q₀_ne Q hQ Dq hDq _ (hmemT Dq))

end step0

end AlgebraicCurve.RegularProlongation.AJDM

open _root_.AlgebraicCurve.RegularProlongation _root_.P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective.AlgebraicCurve.RegularProlongation in

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
    (f : R.integers) (hf : R.residue f ≠ 0)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (T : Finset (Place L F))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧
      (∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) ∧
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits)) :
    ∑ P ∈ T, D P = Q.ord (R.residue f) :=
  AJDM.main R x hx hfin hdeg hchart f hf Q hQ D hD T hT

end S_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective (solution)
