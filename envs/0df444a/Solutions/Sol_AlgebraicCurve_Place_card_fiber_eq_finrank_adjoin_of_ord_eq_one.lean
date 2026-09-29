-- Prove2me | solution 1 for AlgebraicCurve.Place.card_fiber_eq_finrank_adjoin_of_ord_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b7484786-1507-5d17-9599-6bbf8bbe290b

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_eq_finrank
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_card_fiber_eq_finrank_adjoin_of_ord_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open AlgebraicCurve Polynomial

namespace C0RegionD

p2m_open "AlgebraicCurve.Place"

theorem evalAt_sub_algebraMap {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (c : ℂ) :
    v.evalAt (f - algebraMap ℂ F c) = v.evalAt f - c := by
  have hcm : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem : f - algebraMap ℂ F c ∈ v.toValuationSubring := sub_mem hf hcm
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hmem, v.algebraMap_evalAt hv hf]
  have hsub : (⟨f - algebraMap ℂ F c, hmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - ⟨algebraMap ℂ F c, hcm⟩ := rfl
  rw [hsub, map_sub]
  congr 1

theorem evalAt_eq_zero_of_ord_pos {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) {g : F} (hg : g ≠ 0) (h : 0 < v.ord g) : v.evalAt g = 0 := by
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

theorem ord_eq_zero_of_evalAt_ne_zero {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) {g : F} (hg : g ≠ 0) (hmem : g ∈ v.toValuationSubring)
    (hne : v.evalAt g ≠ 0) : v.ord g = 0 := by
  have h0 : 0 ≤ v.ord g := (v.mem_iff_ord_nonneg hg).mp hmem
  rcases h0.lt_or_eq with h | h
  · exact absurd (evalAt_eq_zero_of_ord_pos v hg h) hne
  · exact h.symm

theorem ord_pos_of_evalAt_eq_zero {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) (hv : v.IsRational) {g : F} (hg : g ≠ 0)
    (hmem : g ∈ v.toValuationSubring) (hz : v.evalAt g = 0) : 0 < v.ord g := by
  have h0 : 0 ≤ v.ord g := (v.mem_iff_ord_nonneg hg).mp hmem
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd hz (v.evalAt_ne_zero_of_ord_eq_zero hv hg h.symm)

theorem ord_multiset_prod {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) (s : Multiset F) (hs : ∀ x ∈ s, x ≠ 0) :
    v.ord s.prod = (s.map v.ord).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Place.ord_one]
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ x ∈ s, x ≠ 0 := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h0 => hs' 0 h0 rfl)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      v.ord_mul ha hprod, ih hs']

theorem ord_algebraMap_eq_zero {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) {c : ℂ} (hc : c ≠ 0) : v.ord (algebraMap ℂ F c) = 0 := by
  have hne : algebraMap ℂ F c ≠ 0 := by
    simpa using (algebraMap ℂ F).injective.ne hc
  have hne' : algebraMap ℂ F c⁻¹ ≠ 0 := by
    simpa using (algebraMap ℂ F).injective.ne (inv_ne_zero hc)
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

theorem ord_aeval {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) (hv : v.IsRational) {f : F} (htr : Transcendental ℂ f)
    (hmem : f ∈ v.toValuationSubring) {p : ℂ[X]} (hp : p ≠ 0) :
    v.ord (Polynomial.aeval f p)
      = v.ord (f - algebraMap ℂ F (v.evalAt f)) * p.rootMultiplicity (v.evalAt f) := by
  classical
  have hfr : ∀ r : ℂ, f - algebraMap ℂ F r ≠ 0 := fun r h =>
    htr (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap r)
  have hfactor := (IsAlgClosed.splits (k := ℂ) p).eq_prod_roots
  have hmapeq : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).map
        (Polynomial.aeval f)
      = p.roots.map (fun r => f - algebraMap ℂ F r) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro r _
    simp
  have h1 : Polynomial.aeval f p
      = algebraMap ℂ F p.leadingCoeff
          * (p.roots.map (fun r => f - algebraMap ℂ F r)).prod := by
    conv_lhs => rw [hfactor]
    rw [map_mul, map_multiset_prod, hmapeq, Polynomial.aeval_C]
  have hmapne : ∀ x ∈ p.roots.map (fun r => f - algebraMap ℂ F r), x ≠ 0 := by
    intro x hx
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp hx
    exact hr ▸ hfr r
  have hprodne : (p.roots.map (fun r => f - algebraMap ℂ F r)).prod ≠ 0 :=
    Multiset.prod_ne_zero (fun h0 => hmapne 0 h0 rfl)
  have hlc : algebraMap ℂ F p.leadingCoeff ≠ 0 := by
    simpa using (algebraMap ℂ F).injective.ne (Polynomial.leadingCoeff_ne_zero.mpr hp)
  rw [h1, v.ord_mul hlc hprodne,
    ord_algebraMap_eq_zero v (Polynomial.leadingCoeff_ne_zero.mpr hp), zero_add,
    ord_multiset_prod v _ hmapne, Multiset.map_map]
  have hterm : ∀ r ∈ p.roots,
      (v.ord ∘ fun r => f - algebraMap ℂ F r) r
        = if r = v.evalAt f then v.ord (f - algebraMap ℂ F (v.evalAt f)) else 0 := by
    intro r _
    simp only [Function.comp_apply]
    by_cases hr : r = v.evalAt f
    · rw [hr, if_pos rfl]
    · rw [if_neg hr]
      apply ord_eq_zero_of_evalAt_ne_zero v (hfr r) (sub_mem hmem (v.algebraMap_mem' r))
      rw [evalAt_sub_algebraMap v hv hmem r]
      exact sub_ne_zero.mpr (fun h => hr h.symm)
  rw [Multiset.map_congr rfl hterm, sum_map_ite_count, Polynomial.count_roots]
  ring

theorem restrict_eq_restrict {F : Type*} [Field F] [Algebra ℂ F]
    (w w' : Place ℂ F) (hw : w.IsRational) (hw' : w'.IsRational) {f : F}
    (htr : Transcendental ℂ f) (hwm : f ∈ w.toValuationSubring)
    (hw'm : f ∈ w'.toValuationSubring) (hval : w.evalAt f = w'.evalAt f)
    [FiniteDimensional (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F] :
    w.restrict (IntermediateField.adjoin ℂ ({f} : Set F))
      = w'.restrict (IntermediateField.adjoin ℂ ({f} : Set F)) := by
  haveI : Algebra.IsIntegral (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F :=
    Algebra.IsIntegral.of_finite _ _
  have hfr : ∀ r : ℂ, f - algebraMap ℂ F r ≠ 0 := fun r h =>
    htr (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap r)
  have key : ∀ (u : Place ℂ F), u.IsRational → f ∈ u.toValuationSubring →
      u.evalAt f = w.evalAt f →
      ∀ (x : F), x ≠ 0 → ∀ (pn pd : ℂ[X]), pn ≠ 0 → pd ≠ 0 →
      x = Polynomial.aeval f pn / Polynomial.aeval f pd →
      u.ord x = u.ord (f - algebraMap ℂ F (w.evalAt f))
        * ((pn.rootMultiplicity (w.evalAt f) : ℤ) - pd.rootMultiplicity (w.evalAt f)) := by
    intro u hu hum huval x hx pn pd hpn hpd hx_eq
    have hdn : Polynomial.aeval f pd ≠ 0 := fun h =>
      hpd (transcendental_iff_injective.mp htr (by simpa using h))
    have hordq : u.ord x
        = u.ord (Polynomial.aeval f pn) - u.ord (Polynomial.aeval f pd) := by
      have hmul : x * Polynomial.aeval f pd = Polynomial.aeval f pn := by
        rw [hx_eq, div_mul_cancel₀ _ hdn]
      have h2 := u.ord_mul hx hdn
      rw [hmul] at h2
      omega
    rw [hordq, ord_aeval u hu htr hum hpn, ord_aeval u hu htr hum hpd, huval]
    ring
  have key2 : ∀ {e e' d : ℤ}, 0 < e → 0 < e' → 0 ≤ e * d → 0 ≤ e' * d := by
    intro e e' d he he' h
    rcases le_total 0 d with hd | hd
    · exact mul_nonneg he'.le hd
    · rcases hd.lt_or_eq with hd' | hd'
      · exact absurd h (not_le.mpr (mul_neg_of_pos_of_neg he hd'))
      · rw [hd']
        simp
  have hew : 0 < w.ord (f - algebraMap ℂ F (w.evalAt f)) :=
    ord_pos_of_evalAt_eq_zero w hw (hfr _) (sub_mem hwm (w.algebraMap_mem' _))
      (by rw [evalAt_sub_algebraMap w hw hwm, sub_self])
  have hew' : 0 < w'.ord (f - algebraMap ℂ F (w.evalAt f)) :=
    ord_pos_of_evalAt_eq_zero w' hw' (hfr _) (sub_mem hw'm (w'.algebraMap_mem' _))
      (by rw [evalAt_sub_algebraMap w' hw' hw'm, ← hval, sub_self])
  apply Place.ext
  apply SetLike.ext
  intro r
  rw [Place.mem_restrict_iff, Place.mem_restrict_iff,
    IntermediateField.algebraMap_apply]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have hrne : (r : F) ≠ 0 := fun h => hr (by exact_mod_cast h)
    obtain ⟨pn, pd, hpq⟩ :=
      (IntermediateField.mem_adjoin_simple_iff ℂ (r : F)).mp r.2
    have hpd : pd ≠ 0 := by
      rintro rfl
      simp only [map_zero, div_zero] at hpq
      exact hrne hpq
    have hpn : pn ≠ 0 := by
      rintro rfl
      simp only [map_zero, zero_div] at hpq
      exact hrne hpq
    have h1 := key w hw hwm rfl _ hrne pn pd hpn hpd hpq
    have h2 := key w' hw' hw'm hval.symm _ hrne pn pd hpn hpd hpq
    rw [w.mem_iff_ord_nonneg hrne, w'.mem_iff_ord_nonneg hrne, h1, h2]
    exact ⟨key2 hew hew', key2 hew' hew⟩

theorem card_fiber_eq_finrank {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    {f : F} (htr : Transcendental ℂ f)
    [FiniteDimensional (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F]
    (hrat : ∀ w : Place ℂ F, w.IsRational)
    (hratE : ∀ u : Place ℂ (↥(IntermediateField.adjoin ℂ ({f} : Set F))), u.IsRational)
    (t : ℂ) (w₀ : Place ℂ F) (h₀m : f ∈ w₀.toValuationSubring) (h₀v : w₀.evalAt f = t)
    (hunram : ∀ w : Place ℂ F, f ∈ w.toValuationSubring → w.evalAt f = t →
      w.ord (f - algebraMap ℂ F t) = 1) :
    Nat.card {P : Place ℂ F // f ∈ P.toValuationSubring ∧ P.evalAt f = t}
      = Module.finrank (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F := by
  classical
  haveI : CharZero (↥(IntermediateField.adjoin ℂ ({f} : Set F))) :=
    charZero_of_injective_algebraMap (algebraMap ℂ _).injective
  haveI : Algebra.IsIntegral (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F :=
    Algebra.IsIntegral.of_finite _ _
  have hfr : ∀ r : ℂ, f - algebraMap ℂ F r ≠ 0 := fun r h =>
    htr (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap r)
  have hx₀mem : f ∈ IntermediateField.adjoin ℂ ({f} : Set F) :=
    IntermediateField.mem_adjoin_simple_self ℂ f
  have hcoe : (algebraMap (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F)
      ⟨f, hx₀mem⟩ = f := rfl
  have hx₀v : (⟨f, hx₀mem⟩ : ↥(IntermediateField.adjoin ℂ ({f} : Set F)))
      ∈ (w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).toValuationSubring := by
    rw [Place.mem_restrict_iff, hcoe]
    exact h₀m
  have hvx₀ : (w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).evalAt
      ⟨f, hx₀mem⟩ = t := by
    have h := Place.evalAt_algebraMap_eq_evalAt_restrict w₀ (hratE _) hx₀v
    rw [hcoe] at h
    rw [← h, h₀v]
  have hset : {P : Place ℂ F | f ∈ P.toValuationSubring ∧ P.evalAt f = t}
      = ↑((w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).fiber F) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Place.mem_fiber]
    constructor
    · rintro ⟨hm, hv⟩
      exact restrict_eq_restrict w w₀ (hrat w) (hrat w₀) htr hm h₀m (hv.trans h₀v.symm)
    · intro hre
      have hx₀w : (⟨f, hx₀mem⟩ : ↥(IntermediateField.adjoin ℂ ({f} : Set F)))
          ∈ (w.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).toValuationSubring := by
        rw [hre]
        exact hx₀v
      have hfm : f ∈ w.toValuationSubring := by
        rw [Place.mem_restrict_iff, hcoe] at hx₀w
        exact hx₀w
      refine ⟨hfm, ?_⟩
      have h1 := Place.evalAt_algebraMap_eq_evalAt_restrict w (hratE _) hx₀w
      rw [hcoe] at h1
      rw [h1, hre, hvx₀]
  have hsum := Place.sum_ramificationIndex_eq_finrank (K := ℂ)
    (F := ↥(IntermediateField.adjoin ℂ ({f} : Set F))) (F' := F)
    (w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))) (hratE _)
    (fun w _ => hrat w)
  have hone : ∀ w ∈ (w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).fiber F,
      ((w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({f} : Set F)))) : ℤ) = 1 := by
    intro w hwf
    have hw' : w ∈ {P : Place ℂ F | f ∈ P.toValuationSubring ∧ P.evalAt f = t} := by
      rw [hset]
      exact hwf
    obtain ⟨hm, hv⟩ := hw'
    have he := hunram w hm hv
    have hre : w.restrict (IntermediateField.adjoin ℂ ({f} : Set F))
        = w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F)) :=
      Place.mem_fiber.mp hwf
    have hsubmap : (algebraMap (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F)
        (⟨f, hx₀mem⟩ - algebraMap ℂ _ t) = f - algebraMap ℂ F t := by
      rw [map_sub, hcoe, ← IsScalarTower.algebraMap_apply]
    have hor := w.ord_restrict
      ((⟨f, hx₀mem⟩ : ↥(IntermediateField.adjoin ℂ ({f} : Set F))) - algebraMap ℂ _ t)
    rw [hsubmap, he] at hor
    have hx₀t : (⟨f, hx₀mem⟩ : ↥(IntermediateField.adjoin ℂ ({f} : Set F)))
        - algebraMap ℂ _ t ≠ 0 := by
      intro h
      apply hfr t
      rw [← hsubmap, h, map_zero]
    have hx₀vmem : (⟨f, hx₀mem⟩ : ↥(IntermediateField.adjoin ℂ ({f} : Set F)))
        - algebraMap ℂ _ t
        ∈ (w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).toValuationSubring :=
      sub_mem hx₀v ((w₀.restrict _).algebraMap_mem' t)
    have hkpos : 0 < (w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).ord
        (⟨f, hx₀mem⟩ - algebraMap ℂ _ t) :=
      ord_pos_of_evalAt_eq_zero _ (hratE _) hx₀t hx₀vmem
        (by rw [evalAt_sub_algebraMap _ (hratE _) hx₀v, hvx₀, sub_self])
    rw [hre] at hor
    have hepos := w.ramificationIndex_pos
      (F := ↥(IntermediateField.adjoin ℂ ({f} : Set F)))
    set e := w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({f} : Set F))) with he_def
    set k := (w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).ord
      (⟨f, hx₀mem⟩ - algebraMap ℂ _ t) with hk_def
    have hbound : (e : ℤ) * 1 ≤ (e : ℤ) * k := by
      apply mul_le_mul_of_nonneg_left hkpos (by positivity)
    omega
  have hcardsum : ((((w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).fiber F).card : ℤ))
      = (Module.finrank (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F : ℤ) := by
    rw [← hsum, Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : Nat.card {P : Place ℂ F // f ∈ P.toValuationSubring ∧ P.evalAt f = t}
      = ((w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).fiber F).card := by
    have he : {P : Place ℂ F // f ∈ P.toValuationSubring ∧ P.evalAt f = t}
        ≃ {P : Place ℂ F //
            P ∈ (w₀.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).fiber F} :=
      Equiv.subtypeEquivRight (fun P => by
        have := Set.ext_iff.mp hset P
        simpa using this)
    rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_coe]
  omega

theorem transcendental_adjoin_self {F : Type*} [Field F] [Algebra ℂ F] {f : F}
    (htr : Transcendental ℂ f) :
    Transcendental ℂ (⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
      ↥(IntermediateField.adjoin ℂ ({f} : Set F))) := by
  intro halg
  apply htr
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  have h2 := Polynomial.aeval_algHom_apply
    (IntermediateField.val (IntermediateField.adjoin ℂ ({f} : Set F)))
    ⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ p
  rw [hp, map_zero] at h2
  simpa using h2

theorem ord_sub_evalAt_eq_one_of_generator {E : Type*} [Field E] [Algebra ℂ E]
    {x₀ : E} (htr : Transcendental ℂ x₀)
    (hgen : ∀ y : E, ∃ pn pd : ℂ[X],
      y = Polynomial.aeval x₀ pn / Polynomial.aeval x₀ pd)
    (v : Place ℂ E) (hvr : v.IsRational) (hvm : x₀ ∈ v.toValuationSubring) :
    v.ord (x₀ - algebraMap ℂ E (v.evalAt x₀)) = 1 := by
  have hfr : ∀ c : ℂ, x₀ - algebraMap ℂ E c ≠ 0 := fun c h =>
    htr (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap c)
  have hkpos : 0 < v.ord (x₀ - algebraMap ℂ E (v.evalAt x₀)) :=
    ord_pos_of_evalAt_eq_zero v hvr (hfr _) (sub_mem hvm (v.algebraMap_mem' _))
      (by rw [evalAt_sub_algebraMap v hvr hvm, sub_self])
  have hdvd : ∀ y : E, y ≠ 0 →
      v.ord (x₀ - algebraMap ℂ E (v.evalAt x₀)) ∣ v.ord y := by
    intro y hy
    obtain ⟨pn, pd, hrep⟩ := hgen y
    have hdn : Polynomial.aeval x₀ pd ≠ 0 := by
      intro h
      apply hy
      rw [hrep, h, div_zero]
    have hnn : Polynomial.aeval x₀ pn ≠ 0 := by
      intro h
      apply hy
      rw [hrep, h, zero_div]
    have hpd : pd ≠ 0 := by rintro rfl; exact hdn (map_zero _)
    have hpn : pn ≠ 0 := by rintro rfl; exact hnn (map_zero _)
    have hdiv : v.ord y
        = v.ord (Polynomial.aeval x₀ pn) - v.ord (Polynomial.aeval x₀ pd) := by
      have hmul : y * Polynomial.aeval x₀ pd = Polynomial.aeval x₀ pn := by
        rw [hrep, div_mul_cancel₀ _ hdn]
      have h2 := v.ord_mul hy hdn
      rw [hmul] at h2
      omega
    rw [hdiv, ord_aeval v hvr htr hvm hpn, ord_aeval v hvr htr hvm hpd]
    exact ⟨(pn.rootMultiplicity (v.evalAt x₀) : ℤ)
      - (pd.rootMultiplicity (v.evalAt x₀) : ℤ), by ring⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπne : (π : E) ≠ 0 := fun h => hπ.ne_zero (ZeroMemClass.coe_eq_zero.mp h)
  have hd1 := hdvd (π : E) hπne
  rw [v.ord_coe_irreducible hπ] at hd1
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hd1) with h1 | h1
  · exact h1
  · omega

theorem generator_adjoin {F : Type*} [Field F] [Algebra ℂ F] (f : F) :
    ∀ y : ↥(IntermediateField.adjoin ℂ ({f} : Set F)), ∃ pn pd : ℂ[X],
      y = Polynomial.aeval
          (⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
            ↥(IntermediateField.adjoin ℂ ({f} : Set F))) pn
        / Polynomial.aeval
          (⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
            ↥(IntermediateField.adjoin ℂ ({f} : Set F))) pd := by
  intro y
  obtain ⟨pn, pd, h⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ (y : F)).mp y.2
  refine ⟨pn, pd, ?_⟩
  have hc : ∀ p : ℂ[X],
      ((Polynomial.aeval
        (⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
          ↥(IntermediateField.adjoin ℂ ({f} : Set F))) p : _) : F)
      = Polynomial.aeval f p := by
    intro p
    exact (Polynomial.aeval_algHom_apply
      (IntermediateField.val (IntermediateField.adjoin ℂ ({f} : Set F)))
      ⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ p).symm
  apply Subtype.coe_injective
  push_cast [hc]
  exact h

theorem ord_sub_eq_one_of_ramificationIndex_eq_one {F : Type*} [Field F] [Algebra ℂ F]
    {f : F} (htr : Transcendental ℂ f)
    [FiniteDimensional (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F]
    (w : Place ℂ F)
    (hvr : (w.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).IsRational)
    (hwm : f ∈ w.toValuationSubring) {t : ℂ} (hwt : w.evalAt f = t)
    (hre : w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({f} : Set F))) = 1) :
    w.ord (f - algebraMap ℂ F t) = 1 := by
  haveI : Algebra.IsIntegral (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F :=
    Algebra.IsIntegral.of_finite _ _
  have hcoe : (algebraMap (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F)
      ⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ = f := rfl
  have hvm : (⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
      ↥(IntermediateField.adjoin ℂ ({f} : Set F)))
      ∈ (w.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).toValuationSubring := by
    rw [Place.mem_restrict_iff, hcoe]
    exact hwm
  have hvt : (w.restrict (IntermediateField.adjoin ℂ ({f} : Set F))).evalAt
      ⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ = t := by
    have h := Place.evalAt_algebraMap_eq_evalAt_restrict w hvr hvm
    rw [hcoe] at h
    rw [← h, hwt]
  have hsubmap : (algebraMap (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F)
      ((⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
        ↥(IntermediateField.adjoin ℂ ({f} : Set F))) - algebraMap ℂ _ t)
      = f - algebraMap ℂ F t := by
    rw [map_sub, hcoe, ← IsScalarTower.algebraMap_apply]
  have hor := w.ord_restrict
    ((⟨f, IntermediateField.mem_adjoin_simple_self ℂ f⟩ :
      ↥(IntermediateField.adjoin ℂ ({f} : Set F))) - algebraMap ℂ _ t)
  rw [hsubmap, hre] at hor
  have hk := ord_sub_evalAt_eq_one_of_generator (transcendental_adjoin_self htr)
    (generator_adjoin f) (w.restrict (IntermediateField.adjoin ℂ ({f} : Set F))) hvr hvm
  rw [hvt] at hk
  rw [hor, hk]
  ring

end C0RegionD

open AlgebraicCurve in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    {f : F} (htr : Transcendental ℂ f)
    [FiniteDimensional (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F]
    (hrat : ∀ w : Place ℂ F, w.IsRational)
    (hratE : ∀ u : Place ℂ (↥(IntermediateField.adjoin ℂ ({f} : Set F))), u.IsRational)
    (t : ℂ) (w₀ : Place ℂ F) (h₀m : f ∈ w₀.toValuationSubring) (h₀v : w₀.evalAt f = t)
    (hunram : ∀ w : Place ℂ F, f ∈ w.toValuationSubring → w.evalAt f = t →
      w.ord (f - algebraMap ℂ F t) = 1) :
    Nat.card {P : Place ℂ F // f ∈ P.toValuationSubring ∧ P.evalAt f = t}
      = Module.finrank (↥(IntermediateField.adjoin ℂ ({f} : Set F))) F :=
  C0RegionD.card_fiber_eq_finrank htr hrat hratE t w₀ h₀m h₀v hunram

end S_AlgebraicCurve_Place_card_fiber_eq_finrank_adjoin_of_ord_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_card_fiber_eq_finrank_adjoin_of_ord_eq_one (solution)
