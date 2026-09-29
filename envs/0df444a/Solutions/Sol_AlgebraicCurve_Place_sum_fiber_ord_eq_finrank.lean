-- Prove2me | solution 1 for AlgebraicCurve.Place.sum_fiber_ord_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e05ad1a9-23d8-56f6-8587-f05381a8c979

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_neg_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_sum_fiber_ord_eq_finrank
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

noncomputable section

namespace FibreOrderCount
open AlgebraicCurve Polynomial

variable {F : Type*} [Field F] [Algebra ℂ F]
variable (x : F)

def fib (b : ℂ) : Set (Place ℂ F) := {w | x ∈ w.toValuationSubring ∧ Place.evalAt w x = b}

def poles : Set (Place ℂ F) := {w | x ∉ w.toValuationSubring}

noncomputable def eFin (w : Place ℂ F) (b : ℂ) : ℕ := (w.ord (x - algebraMap ℂ F b)).toNat

noncomputable def eInf (w : Place ℂ F) : ℕ := (w.ord x⁻¹).toNat

noncomputable abbrev deg : ℕ := Module.finrank (IntermediateField.adjoin ℂ ({x} : Set F)) F

private theorem mem_fib_iff {w : Place ℂ F} {b : ℂ} :
    w ∈ fib x b ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b := Iff.rfl

private theorem mem_poles_iff {w : Place ℂ F} : w ∈ poles x ↔ x ∉ w.toValuationSubring := Iff.rfl

private theorem evalAt_sub_algebraMap (v : Place ℂ F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : ℂ) :
    v.evalAt (f - algebraMap ℂ F c) = v.evalAt f - c := by
  have hcm : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem : f - algebraMap ℂ F c ∈ v.toValuationSubring := sub_mem hf hcm
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hmem, v.algebraMap_evalAt hv hf]
  have hsub : (⟨f - algebraMap ℂ F c, hmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - ⟨algebraMap ℂ F c, hcm⟩ := rfl
  rw [hsub, map_sub]
  congr 1

private theorem evalAt_eq_zero_of_ord_pos (v : Place ℂ F) {g : F} (hg : g ≠ 0)
    (h : 0 < v.ord g) : v.evalAt g = 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg h.le
  have hm : (⟨g, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    omega
  rw [v.evalAt_of_mem hmem]
  have hres0 : IsLocalRing.residue v.toValuationSubring ⟨g, hmem⟩ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [hres0]
  have := v.residueInv_algebraMap 0
  rwa [map_zero] at this

private theorem ord_eq_zero_of_evalAt_ne_zero (v : Place ℂ F) {g : F} (hg : g ≠ 0)
    (hmem : g ∈ v.toValuationSubring) (hne : v.evalAt g ≠ 0) : v.ord g = 0 := by
  have h0 : 0 ≤ v.ord g := (v.mem_iff_ord_nonneg hg).mp hmem
  rcases h0.lt_or_eq with h | h
  · exact absurd (evalAt_eq_zero_of_ord_pos v hg h) hne
  · exact h.symm

private theorem ord_pos_of_evalAt_eq_zero (v : Place ℂ F) (hv : v.IsRational) {g : F} (hg : g ≠ 0)
    (hmem : g ∈ v.toValuationSubring) (hz : v.evalAt g = 0) : 0 < v.ord g := by
  have h0 : 0 ≤ v.ord g := (v.mem_iff_ord_nonneg hg).mp hmem
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd hz (v.evalAt_ne_zero_of_ord_eq_zero hv hg h.symm)

private theorem ord_multiset_prod (v : Place ℂ F) (s : Multiset F) (hs : ∀ y ∈ s, y ≠ 0) :
    v.ord s.prod = (s.map v.ord).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Place.ord_one]
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ y ∈ s, y ≠ 0 := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h0 => hs' 0 h0 rfl)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      v.ord_mul ha hprod, ih hs']

private theorem ord_algebraMap_eq_zero (v : Place ℂ F) {c : ℂ} (hc : c ≠ 0) :
    v.ord (algebraMap ℂ F c) = 0 := by
  have hne : algebraMap ℂ F c ≠ 0 := by
    simpa using (algebraMap ℂ F).injective.ne hc
  have hne' : algebraMap ℂ F c⁻¹ ≠ 0 := by
    simpa using (algebraMap ℂ F).injective.ne (_root_.inv_ne_zero hc)
  have h1 : v.ord (algebraMap ℂ F c * algebraMap ℂ F c⁻¹) = 0 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one, Place.ord_one]
  rw [v.ord_mul hne hne'] at h1
  have h2 : 0 ≤ v.ord (algebraMap ℂ F c) :=
    (v.mem_iff_ord_nonneg hne).mp (v.algebraMap_mem' c)
  have h3 : 0 ≤ v.ord (algebraMap ℂ F c⁻¹) :=
    (v.mem_iff_ord_nonneg hne').mp (v.algebraMap_mem' c⁻¹)
  omega

private theorem sum_map_ite_count (t : ℂ) (e : ℤ) (s : Multiset ℂ) :
    (s.map (fun r => if r = t then e else 0)).sum = (s.count t : ℤ) * e := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
    by_cases h : a = t
    · rw [if_pos h, if_pos h.symm]
      push_cast
      ring
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
      push_cast
      ring

private theorem ord_aeval (v : Place ℂ F) (hv : v.IsRational) {g : F} (htg : Transcendental ℂ g)
    (hmem : g ∈ v.toValuationSubring) {p : ℂ[X]} (hp : p ≠ 0) :
    v.ord (Polynomial.aeval g p)
      = v.ord (g - algebraMap ℂ F (v.evalAt g)) * p.rootMultiplicity (v.evalAt g) := by
  classical
  have hfr : ∀ r : ℂ, g - algebraMap ℂ F r ≠ 0 := fun r h =>
    htg (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap r)
  have hfactor := (IsAlgClosed.splits (k := ℂ) p).eq_prod_roots
  have hmapeq : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).map
        (Polynomial.aeval g)
      = p.roots.map (fun r => g - algebraMap ℂ F r) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro r _
    simp
  have h1 : Polynomial.aeval g p
      = algebraMap ℂ F p.leadingCoeff
          * (p.roots.map (fun r => g - algebraMap ℂ F r)).prod := by
    conv_lhs => rw [hfactor]
    rw [map_mul, map_multiset_prod, hmapeq, Polynomial.aeval_C]
  have hmapne : ∀ y ∈ p.roots.map (fun r => g - algebraMap ℂ F r), y ≠ 0 := by
    intro y hy
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp hy
    exact hr ▸ hfr r
  have hprodne : (p.roots.map (fun r => g - algebraMap ℂ F r)).prod ≠ 0 :=
    Multiset.prod_ne_zero (fun h0 => hmapne 0 h0 rfl)
  have hlc : algebraMap ℂ F p.leadingCoeff ≠ 0 := by
    simpa using (algebraMap ℂ F).injective.ne (Polynomial.leadingCoeff_ne_zero.mpr hp)
  rw [h1, v.ord_mul hlc hprodne,
    ord_algebraMap_eq_zero v (Polynomial.leadingCoeff_ne_zero.mpr hp), zero_add,
    ord_multiset_prod v _ hmapne, Multiset.map_map]
  have hterm : ∀ r ∈ p.roots,
      (v.ord ∘ fun r => g - algebraMap ℂ F r) r
        = if r = v.evalAt g then v.ord (g - algebraMap ℂ F (v.evalAt g)) else 0 := by
    intro r _
    simp only [Function.comp_apply]
    by_cases hr : r = v.evalAt g
    · rw [hr, if_pos rfl]
    · rw [if_neg hr]
      apply ord_eq_zero_of_evalAt_ne_zero v (hfr r) (sub_mem hmem (v.algebraMap_mem' r))
      rw [evalAt_sub_algebraMap v hv hmem r]
      exact _root_.sub_ne_zero.mpr (fun h => hr h.symm)
  rw [Multiset.map_congr rfl hterm, sum_map_ite_count, Polynomial.count_roots]
  ring

private theorem isRational_of_finite {L : Type*} [Field L] [Algebra ℂ L] (v : Place ℂ L)
    (hfin : Module.Finite ℂ v.ResidueField) : v.IsRational := by
  haveI := hfin
  haveI : Algebra.IsIntegral ℂ v.ResidueField := Algebra.IsIntegral.of_finite ℂ v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := v.ResidueField)).2

private theorem nonneg_mul_of_nonneg_mul {e e' d : ℤ} (he : 0 < e) (he' : 0 < e')
    (h : 0 ≤ e * d) : 0 ≤ e' * d := by
  rcases le_total 0 d with hd | hd
  · exact mul_nonneg he'.le hd
  · rcases hd.lt_or_eq with hd' | hd'
    · exact absurd h (not_le.mpr (mul_neg_of_pos_of_neg he hd'))
    · rw [hd']
      simp

private theorem pos_of_mul_pos_of_pos {e k : ℤ} (he : 0 < e) (h : 0 < e * k) : 0 < k := by
  by_contra hk
  have hk' : k ≤ 0 := not_lt.mp hk
  nlinarith

private theorem neg_of_mul_neg_of_pos {e k : ℤ} (he : 0 < e) (h : e * k < 0) : k < 0 := by
  by_contra hk
  have hk' : 0 ≤ k := not_lt.mp hk
  nlinarith

private theorem ne_zero_of_transcendental {g : F} (hg : Transcendental ℂ g) : g ≠ 0 := by
  intro h
  apply hg
  rw [h]
  exact isAlgebraic_zero

private theorem transcendental_inv {g : F} (hg : Transcendental ℂ g) : Transcendental ℂ g⁻¹ :=
  fun h => hg (IsAlgebraic.inv_iff.mp h)

private theorem adjoin_le_adjoin_inv (g : F) :
    IntermediateField.adjoin ℂ ({g} : Set F) ≤ IntermediateField.adjoin ℂ ({g⁻¹} : Set F) := by
  have h := inv_mem (IntermediateField.mem_adjoin_simple_self ℂ g⁻¹)
  rw [inv_inv] at h
  exact IntermediateField.adjoin_simple_le_iff.mpr h

theorem sub_ne_zero (htr : Transcendental ℂ x) (b : ℂ) : x - algebraMap ℂ F b ≠ 0 :=
  fun h => htr (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap b)

private theorem transcendental_sub_algebraMap (htr : Transcendental ℂ x) (c : ℂ) :
    Transcendental ℂ (x - algebraMap ℂ F c) := by
  intro h
  apply htr
  have h2 := h.add (isAlgebraic_algebraMap (R := ℂ) (A := F) c)
  rwa [sub_add_cancel] at h2

private theorem adjoin_inv_sub_eq (c : ℂ) :
    IntermediateField.adjoin ℂ ({(x - algebraMap ℂ F c)⁻¹} : Set F)
      = IntermediateField.adjoin ℂ ({x} : Set F) := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (inv_mem (sub_mem (IntermediateField.mem_adjoin_simple_self ℂ x)
        (IntermediateField.algebraMap_mem _ c)))
  · have h := inv_mem (IntermediateField.mem_adjoin_simple_self ℂ (x - algebraMap ℂ F c)⁻¹)
    rw [inv_inv] at h
    have h2 := add_mem h (IntermediateField.algebraMap_mem
      (IntermediateField.adjoin ℂ ({(x - algebraMap ℂ F c)⁻¹} : Set F)) c)
    rw [sub_add_cancel] at h2
    exact IntermediateField.adjoin_simple_le_iff.mpr h2

theorem sub_mem_of_mem_fib {w : Place ℂ F} {b : ℂ} (hw : w ∈ fib x b) :
    x - algebraMap ℂ F b ∈ w.toValuationSubring :=
  sub_mem ((mem_fib_iff x).mp hw).1 (w.algebraMap_mem' b)

theorem inv_mem_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : x⁻¹ ∈ w.toValuationSubring :=
  (w.toValuationSubring.mem_or_inv_mem x).resolve_left ((mem_poles_iff x).mp hw)

private theorem ne_zero_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : x ≠ 0 := by
  intro h
  apply (mem_poles_iff x).mp hw
  rw [h]
  exact zero_mem _

private theorem ord_neg_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : w.ord x < 0 := by
  have hx0 : x ≠ 0 := ne_zero_of_mem_poles x hw
  by_contra h
  exact (mem_poles_iff x).mp hw ((w.mem_iff_ord_nonneg hx0).mpr (not_lt.mp h))

private theorem ord_inv_pos_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : 0 < w.ord x⁻¹ := by
  rw [w.ord_inv]
  have := ord_neg_of_mem_poles x hw
  omega

theorem evalAt_inv_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : Place.evalAt w x⁻¹ = 0 :=
  evalAt_eq_zero_of_ord_pos w (_root_.inv_ne_zero (ne_zero_of_mem_poles x hw))
    (ord_inv_pos_of_mem_poles x hw)

private theorem exists_mem_poles (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] :
    ∃ w : Place ℂ F, w ∈ poles x := by
  obtain ⟨w, hw⟩ := Place.exists_ord_neg_of_transcendental (K := ℂ) x htr
  refine ⟨w, (mem_poles_iff x).mpr fun hmem => ?_⟩
  have := (w.mem_iff_ord_nonneg (ne_zero_of_transcendental htr)).mp hmem
  omega

private theorem mem_poles_of_restrict_eq
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] {w₀ w : Place ℂ F}
    (hw₀ : w₀ ∈ poles x)
    (hre : w.restrict (IntermediateField.adjoin ℂ ({x} : Set F))
      = w₀.restrict (IntermediateField.adjoin ℂ ({x} : Set F))) : w ∈ poles x := by
  have hx0 : x ≠ 0 := ne_zero_of_mem_poles x hw₀
  have hx₀mem : x ∈ IntermediateField.adjoin ℂ ({x} : Set F) :=
    IntermediateField.mem_adjoin_simple_self ℂ x
  have hcoe : (algebraMap (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F) ⟨x, hx₀mem⟩ = x := rfl
  have h₀ : w₀.ord x < 0 := ord_neg_of_mem_poles x hw₀
  have hr₀ := w₀.ord_restrict (⟨x, hx₀mem⟩ : ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
  rw [hcoe] at hr₀
  have he₀ : (0 : ℤ) < (w₀.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
    exact_mod_cast w₀.ramificationIndex_pos (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
  have hv : (w₀.restrict (IntermediateField.adjoin ℂ ({x} : Set F))).ord ⟨x, hx₀mem⟩ < 0 := by
    rw [hr₀] at h₀
    exact neg_of_mul_neg_of_pos he₀ h₀
  have hrw := w.ord_restrict (⟨x, hx₀mem⟩ : ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
  rw [hcoe, hre] at hrw
  have hwneg : w.ord x < 0 := by
    rw [hrw]
    have he : (0 : ℤ) < (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
      exact_mod_cast w.ramificationIndex_pos (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
    exact mul_neg_of_pos_of_neg he hv
  refine (mem_poles_iff x).mpr fun hmem => ?_
  have := (w.mem_iff_ord_nonneg hx0).mp hmem
  omega

variable [IsCurveOver ℂ F]

private theorem place_isRational (w : Place ℂ F) : w.IsRational :=
  isRational_of_finite w (IsCurveOver.finiteResidue w)

private theorem restrict_isRational
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] (w : Place ℂ F) :
    (w.restrict (IntermediateField.adjoin ℂ ({x} : Set F))).IsRational := by
  have h := w.deg_restrict_mul_inertiaDeg (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed w] at h
  have h1 : Module.finrank ℂ
      (w.restrict (IntermediateField.adjoin ℂ ({x} : Set F))).ResidueField = 1 :=
    Nat.eq_one_of_mul_eq_one_right h
  exact isRational_of_finite _ (Module.finite_of_finrank_eq_succ h1)

theorem evalAt_sub_of_mem_fib {w : Place ℂ F} {b : ℂ} (hw : w ∈ fib x b) :
    Place.evalAt w (x - algebraMap ℂ F b) = 0 := by
  rw [evalAt_sub_algebraMap w (place_isRational w) ((mem_fib_iff x).mp hw).1,
    ((mem_fib_iff x).mp hw).2, sub_self]

private theorem exists_mem_fib (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] (b : ℂ) :
    ∃ w : Place ℂ F, w ∈ fib x b := by
  have hxb : x - algebraMap ℂ F b ≠ 0 := FibreOrderCount.sub_ne_zero x htr b
  have htr' : Transcendental ℂ (x - algebraMap ℂ F b)⁻¹ :=
    transcendental_inv (transcendental_sub_algebraMap x htr b)
  haveI : FiniteDimensional
      (IntermediateField.adjoin ℂ ({(x - algebraMap ℂ F b)⁻¹} : Set F)) F := by
    rw [adjoin_inv_sub_eq x b]
    infer_instance
  obtain ⟨w, hw⟩ := Place.exists_ord_neg_of_transcendental (K := ℂ) _ htr'
  rw [w.ord_inv] at hw
  have hpos : 0 < w.ord (x - algebraMap ℂ F b) := by omega
  have hmem : x - algebraMap ℂ F b ∈ w.toValuationSubring := w.mem_of_ord_nonneg hxb hpos.le
  have hxm : x ∈ w.toValuationSubring := by
    have h := add_mem hmem (w.algebraMap_mem' b)
    rwa [sub_add_cancel] at h
  refine ⟨w, (mem_fib_iff x).mpr ⟨hxm, ?_⟩⟩
  have h0 := evalAt_eq_zero_of_ord_pos w hxb hpos
  rw [evalAt_sub_algebraMap w (place_isRational w) hxm] at h0
  exact sub_eq_zero.mp h0

private theorem exists_ord_coe_eq {g : F} (htg : Transcendental ℂ g)
    (hle : IntermediateField.adjoin ℂ ({x} : Set F) ≤ IntermediateField.adjoin ℂ ({g} : Set F))
    (c : ℂ) (y : ↥(IntermediateField.adjoin ℂ ({x} : Set F))) (hy : y ≠ 0) :
    ∃ k : ℤ, ∀ w : Place ℂ F, g ∈ w.toValuationSubring → w.evalAt g = c →
      w.ord (y : F) = w.ord (g - algebraMap ℂ F c) * k := by
  have hyF : (y : F) ≠ 0 := fun h => hy (by exact_mod_cast h)
  obtain ⟨pn, pd, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ (y : F)).mp (hle y.2)
  have hpd : pd ≠ 0 := by
    rintro rfl
    simp only [map_zero, div_zero] at hpq
    exact hyF hpq
  have hpn : pn ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_div] at hpq
    exact hyF hpq
  refine ⟨(pn.rootMultiplicity c : ℤ) - pd.rootMultiplicity c, ?_⟩
  intro w hgm hgc
  have hdn : Polynomial.aeval g pd ≠ 0 := fun h =>
    hpd (transcendental_iff_injective.mp htg (by simpa using h))
  have hordq : w.ord (y : F)
      = w.ord (Polynomial.aeval g pn) - w.ord (Polynomial.aeval g pd) := by
    have hmul : (y : F) * Polynomial.aeval g pd = Polynomial.aeval g pn := by
      rw [hpq, div_mul_cancel₀ _ hdn]
    have h2 := w.ord_mul hyF hdn
    rw [hmul] at h2
    omega
  rw [hordq, ord_aeval w (place_isRational w) htg hgm hpn,
    ord_aeval w (place_isRational w) htg hgm hpd, hgc]
  ring

private theorem restrict_eq_of_forall
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F]
    {g : F} (htg : Transcendental ℂ g)
    (hle : IntermediateField.adjoin ℂ ({x} : Set F) ≤ IntermediateField.adjoin ℂ ({g} : Set F))
    (c : ℂ) {w w' : Place ℂ F}
    (hw : g ∈ w.toValuationSubring ∧ w.evalAt g = c)
    (hw' : g ∈ w'.toValuationSubring ∧ w'.evalAt g = c) :
    w.restrict (IntermediateField.adjoin ℂ ({x} : Set F))
      = w'.restrict (IntermediateField.adjoin ℂ ({x} : Set F)) := by
  have hgc : g - algebraMap ℂ F c ≠ 0 := fun h =>
    htg (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap c)
  have hew : 0 < w.ord (g - algebraMap ℂ F c) :=
    ord_pos_of_evalAt_eq_zero w (place_isRational w) hgc (sub_mem hw.1 (w.algebraMap_mem' c))
      (by rw [evalAt_sub_algebraMap w (place_isRational w) hw.1, hw.2, sub_self])
  have hew' : 0 < w'.ord (g - algebraMap ℂ F c) :=
    ord_pos_of_evalAt_eq_zero w' (place_isRational w') hgc (sub_mem hw'.1 (w'.algebraMap_mem' c))
      (by rw [evalAt_sub_algebraMap w' (place_isRational w') hw'.1, hw'.2, sub_self])
  apply Place.ext
  apply SetLike.ext
  intro r
  rw [Place.mem_restrict_iff, Place.mem_restrict_iff, IntermediateField.algebraMap_apply]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have hrne : (r : F) ≠ 0 := fun h => hr (by exact_mod_cast h)
    obtain ⟨k, hk⟩ := exists_ord_coe_eq x htg hle c r hr
    rw [w.mem_iff_ord_nonneg hrne, w'.mem_iff_ord_nonneg hrne, hk w hw.1 hw.2, hk w' hw'.1 hw'.2]
    exact ⟨nonneg_mul_of_nonneg_mul hew hew', nonneg_mul_of_nonneg_mul hew' hew⟩

private theorem ramificationIndex_eq_ord
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F]
    {g : F} (htg : Transcendental ℂ g)
    (hle : IntermediateField.adjoin ℂ ({x} : Set F) ≤ IntermediateField.adjoin ℂ ({g} : Set F))
    (hgE : g ∈ IntermediateField.adjoin ℂ ({x} : Set F)) (c : ℂ) (w : Place ℂ F)
    (hgm : g ∈ w.toValuationSubring) (hgc : w.evalAt g = c) :
    (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ)
      = w.ord (g - algebraMap ℂ F c) := by
  have hgc0 : g - algebraMap ℂ F c ≠ 0 := fun h =>
    htg (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap c)
  have hm : 0 < w.ord (g - algebraMap ℂ F c) :=
    ord_pos_of_evalAt_eq_zero w (place_isRational w) hgc0 (sub_mem hgm (w.algebraMap_mem' c))
      (by rw [evalAt_sub_algebraMap w (place_isRational w) hgm, hgc, sub_self])
  have he : (0 : ℤ) < (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
    exact_mod_cast w.ramificationIndex_pos (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
  have hcoe : (algebraMap (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F) ⟨g, hgE⟩ = g := rfl
  have hsubmap : (algebraMap (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F)
      (⟨g, hgE⟩ - algebraMap ℂ _ c) = g - algebraMap ℂ F c := by
    rw [map_sub, hcoe, ← IsScalarTower.algebraMap_apply]
  have hy0 : (⟨g, hgE⟩ : ↥(IntermediateField.adjoin ℂ ({x} : Set F))) - algebraMap ℂ _ c ≠ 0 := by
    intro h
    apply hgc0
    rw [← hsubmap, h, map_zero]
  have h1 : (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ)
      ∣ w.ord (g - algebraMap ℂ F c) := by
    have h := w.ramificationIndex_dvd_ord hy0
    rwa [hsubmap] at h
  have h2 : w.ord (g - algebraMap ℂ F c)
      ∣ (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
    obtain ⟨y, hy, hye⟩ :=
      w.exists_ord_eq_ramificationIndex (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
    obtain ⟨k, hk⟩ := exists_ord_coe_eq x htg hle c y hy
    refine ⟨k, ?_⟩
    exact hye.symm.trans (hk w hgm hgc)
  exact le_antisymm (Int.le_of_dvd hm h1) (Int.le_of_dvd he h2)

private theorem mem_fib_of_restrict_eq (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] {b : ℂ} {w₀ w : Place ℂ F}
    (hw₀ : w₀ ∈ fib x b)
    (hre : w.restrict (IntermediateField.adjoin ℂ ({x} : Set F))
      = w₀.restrict (IntermediateField.adjoin ℂ ({x} : Set F))) : w ∈ fib x b := by
  have hxb : x - algebraMap ℂ F b ≠ 0 := FibreOrderCount.sub_ne_zero x htr b
  have hx₀mem : x ∈ IntermediateField.adjoin ℂ ({x} : Set F) :=
    IntermediateField.mem_adjoin_simple_self ℂ x
  have hcoe : (algebraMap (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F) ⟨x, hx₀mem⟩ = x := rfl
  have hsubmap : (algebraMap (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F)
      (⟨x, hx₀mem⟩ - algebraMap ℂ _ b) = x - algebraMap ℂ F b := by
    rw [map_sub, hcoe, ← IsScalarTower.algebraMap_apply]
  have h₀ : 0 < w₀.ord (x - algebraMap ℂ F b) :=
    ord_pos_of_evalAt_eq_zero w₀ (place_isRational w₀) hxb (sub_mem_of_mem_fib x hw₀)
      (evalAt_sub_of_mem_fib x hw₀)
  have hr₀ := w₀.ord_restrict
    ((⟨x, hx₀mem⟩ : ↥(IntermediateField.adjoin ℂ ({x} : Set F))) - algebraMap ℂ _ b)
  rw [hsubmap] at hr₀
  have he₀ : (0 : ℤ) < (w₀.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
    exact_mod_cast w₀.ramificationIndex_pos (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
  have hv : 0 < (w₀.restrict (IntermediateField.adjoin ℂ ({x} : Set F))).ord
      ((⟨x, hx₀mem⟩ : ↥(IntermediateField.adjoin ℂ ({x} : Set F))) - algebraMap ℂ _ b) := by
    rw [hr₀] at h₀
    exact pos_of_mul_pos_of_pos he₀ h₀
  have hrw := w.ord_restrict
    ((⟨x, hx₀mem⟩ : ↥(IntermediateField.adjoin ℂ ({x} : Set F))) - algebraMap ℂ _ b)
  rw [hsubmap, hre] at hrw
  have hwpos : 0 < w.ord (x - algebraMap ℂ F b) := by
    rw [hrw]
    have he : (0 : ℤ) < (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
      exact_mod_cast w.ramificationIndex_pos (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
    exact mul_pos he hv
  have hmem : x - algebraMap ℂ F b ∈ w.toValuationSubring := w.mem_of_ord_nonneg hxb hwpos.le
  have hxm : x ∈ w.toValuationSubring := by
    have h := add_mem hmem (w.algebraMap_mem' b)
    rwa [sub_add_cancel] at h
  refine (mem_fib_iff x).mpr ⟨hxm, ?_⟩
  have h0 := evalAt_eq_zero_of_ord_pos w hxb hwpos
  rw [evalAt_sub_algebraMap w (place_isRational w) hxm] at h0
  exact sub_eq_zero.mp h0

private theorem fib_iff_restrict_eq (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] {b : ℂ} {w₀ : Place ℂ F}
    (hw₀ : w₀ ∈ fib x b) (w : Place ℂ F) :
    w ∈ fib x b ↔ w.restrict (IntermediateField.adjoin ℂ ({x} : Set F))
      = w₀.restrict (IntermediateField.adjoin ℂ ({x} : Set F)) :=
  ⟨fun hw => restrict_eq_of_forall x htr le_rfl b ((mem_fib_iff x).mp hw) ((mem_fib_iff x).mp hw₀),
    fun h => mem_fib_of_restrict_eq x htr hw₀ h⟩

private theorem poles_iff_restrict_eq (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] {w₀ : Place ℂ F}
    (hw₀ : w₀ ∈ poles x) (w : Place ℂ F) :
    w ∈ poles x ↔ w.restrict (IntermediateField.adjoin ℂ ({x} : Set F))
      = w₀.restrict (IntermediateField.adjoin ℂ ({x} : Set F)) :=
  ⟨fun hw => restrict_eq_of_forall x (transcendental_inv htr) (adjoin_le_adjoin_inv x) 0
      ⟨inv_mem_of_mem_poles x hw, evalAt_inv_of_mem_poles x hw⟩
      ⟨inv_mem_of_mem_poles x hw₀, evalAt_inv_of_mem_poles x hw₀⟩,
    fun h => mem_poles_of_restrict_eq x hw₀ h⟩

private theorem eFin_eq_ramificationIndex (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] {w : Place ℂ F} {b : ℂ}
    (hw : w ∈ fib x b) :
    (eFin x w b : ℤ) = (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
  have h := ramificationIndex_eq_ord x htr le_rfl (IntermediateField.mem_adjoin_simple_self ℂ x) b w
    ((mem_fib_iff x).mp hw).1 ((mem_fib_iff x).mp hw).2
  have hpos : 0 < w.ord (x - algebraMap ℂ F b) := by
    rw [← h]
    exact_mod_cast w.ramificationIndex_pos (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
  show ((w.ord (x - algebraMap ℂ F b)).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg hpos.le]
  exact h.symm

private theorem eInf_eq_ramificationIndex (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] {w : Place ℂ F}
    (hw : w ∈ poles x) :
    (eInf x w : ℤ) = (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
  have hxinv : x⁻¹ ∈ IntermediateField.adjoin ℂ ({x} : Set F) :=
    inv_mem (IntermediateField.mem_adjoin_simple_self ℂ x)
  have h := ramificationIndex_eq_ord x (transcendental_inv htr) (adjoin_le_adjoin_inv x) hxinv 0 w
    (inv_mem_of_mem_poles x hw) (evalAt_inv_of_mem_poles x hw)
  rw [map_zero, sub_zero] at h
  have hpos := ord_inv_pos_of_mem_poles x hw
  show ((w.ord x⁻¹).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg hpos.le]
  exact h.symm

theorem sum_eFin (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] (b : ℂ)
    (s : Finset (Place ℂ F))
    (hs : ∀ w, w ∈ s ↔ w ∈ fib x b) : ∑ w ∈ s, eFin x w b = deg x := by
  classical
  haveI : CharZero (↥(IntermediateField.adjoin ℂ ({x} : Set F))) :=
    charZero_of_injective_algebraMap (algebraMap ℂ _).injective
  haveI : Algebra.IsIntegral (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F :=
    Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F :=
    Algebra.IsSeparable.of_integral _ _
  obtain ⟨w₀, hw₀⟩ := exists_mem_fib x htr b
  have hsum := Place.sum_ramificationIndex_eq_finrank (K := ℂ)
    (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F))) (F' := F)
    (w₀.restrict (IntermediateField.adjoin ℂ ({x} : Set F))) (restrict_isRational x w₀)
    (fun w _ => place_isRational w)
  have hs_eq : s = (w₀.restrict (IntermediateField.adjoin ℂ ({x} : Set F))).fiber F := by
    ext w
    rw [hs w, Place.mem_fiber]
    exact fib_iff_restrict_eq x htr hw₀ w
  have hterm : ∀ w ∈ s, (eFin x w b : ℤ)
      = (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) :=
    fun w hw => eFin_eq_ramificationIndex x htr ((hs w).mp hw)
  have hZ : (∑ w ∈ s, (eFin x w b : ℤ)) = (deg x : ℤ) := by
    rw [Finset.sum_congr rfl hterm, hs_eq]
    exact hsum
  exact_mod_cast hZ

theorem sum_eInf (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] (s : Finset (Place ℂ F))
    (hs : ∀ w, w ∈ s ↔ w ∈ poles x) : ∑ w ∈ s, eInf x w = deg x := by
  classical
  haveI : CharZero (↥(IntermediateField.adjoin ℂ ({x} : Set F))) :=
    charZero_of_injective_algebraMap (algebraMap ℂ _).injective
  haveI : Algebra.IsIntegral (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F :=
    Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F :=
    Algebra.IsSeparable.of_integral _ _
  obtain ⟨w₀, hw₀⟩ := exists_mem_poles x htr
  have hsum := Place.sum_ramificationIndex_eq_finrank (K := ℂ)
    (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F))) (F' := F)
    (w₀.restrict (IntermediateField.adjoin ℂ ({x} : Set F))) (restrict_isRational x w₀)
    (fun w _ => place_isRational w)
  have hs_eq : s = (w₀.restrict (IntermediateField.adjoin ℂ ({x} : Set F))).fiber F := by
    ext w
    rw [hs w, Place.mem_fiber]
    exact poles_iff_restrict_eq x htr hw₀ w
  have hterm : ∀ w ∈ s, (eInf x w : ℤ)
      = (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) :=
    fun w hw => eInf_eq_ramificationIndex x htr ((hs w).mp hw)
  have hZ : (∑ w ∈ s, (eInf x w : ℤ)) = (deg x : ℤ) := by
    rw [Finset.sum_congr rfl hterm, hs_eq]
    exact hsum
  exact_mod_cast hZ

end FibreOrderCount

end

section MainStatement

open AlgebraicCurve IntermediateField

namespace FibreIdentity

theorem sum_fiber_ord_eq_finrank {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    {x : F} (htr : Transcendental ℂ x) [FiniteDimensional (↥(adjoin ℂ ({x} : Set F))) F] :
    (∀ (b : ℂ) (s : Finset (Place ℂ F)),
      (∀ w : Place ℂ F, w ∈ s ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b) →
      ∑ w ∈ s, (w.ord (x - algebraMap ℂ F b)).toNat = Module.finrank (↥(adjoin ℂ ({x} : Set F))) F) ∧
    (∀ s : Finset (Place ℂ F), (∀ w : Place ℂ F, w ∈ s ↔ x ∉ w.toValuationSubring) →
      ∑ w ∈ s, (w.ord x⁻¹).toNat = Module.finrank (↥(adjoin ℂ ({x} : Set F))) F) := by
  exact ⟨fun b s hs => FibreOrderCount.sum_eFin x htr b s hs, fun s hs => FibreOrderCount.sum_eInf x htr s hs⟩

end FibreIdentity

end MainStatement

open AlgebraicCurve IntermediateField

theorem solution {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    {x : F} (htr : Transcendental ℂ x) [FiniteDimensional (↥(adjoin ℂ ({x} : Set F))) F] :
    (∀ (b : ℂ) (s : Finset (Place ℂ F)),
      (∀ w : Place ℂ F, w ∈ s ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b) →
      ∑ w ∈ s, (w.ord (x - algebraMap ℂ F b)).toNat = Module.finrank (↥(adjoin ℂ ({x} : Set F))) F) ∧
    (∀ s : Finset (Place ℂ F), (∀ w : Place ℂ F, w ∈ s ↔ x ∉ w.toValuationSubring) →
      ∑ w ∈ s, (w.ord x⁻¹).toNat = Module.finrank (↥(adjoin ℂ ({x} : Set F))) F) := by
  exact FibreIdentity.sum_fiber_ord_eq_finrank (htr := htr)

end S_AlgebraicCurve_Place_sum_fiber_ord_eq_finrank
end P2MW
export P2MW.S_AlgebraicCurve_Place_sum_fiber_ord_eq_finrank (solution)
