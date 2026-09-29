-- Prove2me | solution 1 for AlgebraicCurve.exists_place_over_of_simple_root_along
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f1e01a73-132c-56db-b803-2b48cda3998d

import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_place_over_of_simple_root_along
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve Polynomial

namespace S09SR

theorem eq_singleton_of_sum_eq_one {ι : Type*} (S : Finset ι) (g : ι → ℕ) (hg : ∀ x ∈ S, 1 ≤ g x)
    (h : ∑ x ∈ S, g x = 1) : ∃ a, S = {a} ∧ g a = 1 := by
  have hcard : S.card ≤ 1 :=
    calc S.card = ∑ x ∈ S, 1 := Finset.card_eq_sum_ones S
      _ ≤ ∑ x ∈ S, g x := Finset.sum_le_sum hg
      _ = 1 := h
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at h
  have hc1 : S.card = 1 := le_antisymm hcard (Finset.card_pos.mpr hne)
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
  exact ⟨a, rfl, by simpa using h⟩

section OnePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_coe_eq_zero_of_isUnit (v : Place K F) {u : v.toValuationSubring} (hu : IsUnit u) :
    ((u : F) ≠ 0) ∧ v.ord (u : F) = 0 := by
  have hu0 : (u : F) ≠ 0 := by
    intro h
    have : u = 0 := Subtype.ext h
    rw [this] at hu
    exact not_isUnit_zero hu
  refine ⟨hu0, ?_⟩
  have hnonneg : 0 ≤ v.ord (u : F) := (v.mem_iff_ord_nonneg hu0).mp u.2
  have hnotmax : u ∉ IsLocalRing.maximalIdeal v.toValuationSubring := fun h => h hu
  have : ¬ 0 < v.ord (u : F) := by
    intro hpos
    exact hnotmax ((v.mem_maximalIdeal_iff_ord_pos hu0 u.2).mpr hpos)
  omega

theorem ord_add_eq_zero (w : Place K F) {u z : F} (hu0 : u ≠ 0) (hu : w.ord u = 0)
    (humem : u ∈ w.toValuationSubring) (hz : z ∈ w.toValuationSubring) (hzpos : z = 0 ∨ 0 < w.ord z) :
    u + z ≠ 0 ∧ w.ord (u + z) = 0 := by
  rcases hzpos with rfl | hzpos
  · simpa using ⟨hu0, hu⟩
  have hz0 : z ≠ 0 := by rintro rfl; simp at hzpos
  have hzmax : (⟨z, hz⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    (w.mem_maximalIdeal_iff_ord_pos hz0 hz).mpr hzpos
  have humax : (⟨u, humem⟩ : w.toValuationSubring) ∉ IsLocalRing.maximalIdeal w.toValuationSubring := by
    rw [w.mem_maximalIdeal_iff_ord_pos hu0 humem]; omega
  have hsmem : u + z ∈ w.toValuationSubring := add_mem humem hz
  have hne : u + z ≠ 0 := by
    intro h
    apply humax
    have : (⟨u, humem⟩ : w.toValuationSubring) = -⟨z, hz⟩ :=
      Subtype.ext (eq_neg_of_add_eq_zero_left h)
    rw [this]; exact neg_mem hzmax
  refine ⟨hne, ?_⟩
  have hnonneg : 0 ≤ w.ord (u + z) := (w.mem_iff_ord_nonneg hne).mp hsmem
  by_contra hcon
  have hpos : 0 < w.ord (u + z) := lt_of_le_of_ne hnonneg (Ne.symm hcon)
  have hsmax : (⟨u + z, hsmem⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    (w.mem_maximalIdeal_iff_ord_pos hne hsmem).mpr hpos
  apply humax
  have : (⟨u, humem⟩ : w.toValuationSubring) = ⟨u + z, hsmem⟩ - ⟨z, hz⟩ := Subtype.ext (by simp)
  rw [this]; exact sub_mem hsmax hzmax

theorem exists_taylor (v : Place K F) (Q : Polynomial v.toValuationSubring) (b : v.toValuationSubring) :
    ∃ S : Polynomial v.toValuationSubring,
      Q - C (Q.eval b) = (X - C b) * S ∧ S.eval b = Q.derivative.eval b := by
  have h : (X - C b) * ((Q - C (Q.eval b)) /ₘ (X - C b)) = Q - C (Q.eval b) := by
    rw [mul_divByMonic_eq_iff_isRoot]; simp [IsRoot]
  refine ⟨(Q - C (Q.eval b)) /ₘ (X - C b), h.symm, ?_⟩
  have hd := congrArg Polynomial.derivative h
  simp only [derivative_mul, derivative_sub, derivative_C, derivative_X, sub_zero, one_mul] at hd
  have he := congrArg (Polynomial.eval b) hd
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at he
  exact he

end OnePlace

section Engine

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F']

omit [Algebra K F'] [IsScalarTower K F F'] in

theorem aeval_taylor (v : Place K F) {Q S : Polynomial v.toValuationSubring} {b : v.toValuationSubring}
    (hS : Q - C (Q.eval b) = (X - C b) * S) (x : F') :
    aeval x (Q.map (algebraMap v.toValuationSubring F)) - algebraMap F F' ((Q.eval b : v.toValuationSubring) : F)
      = (x - algebraMap F F' (b : F)) * aeval x (S.map (algebraMap v.toValuationSubring F)) := by
  have h := congrArg (fun P : Polynomial v.toValuationSubring => aeval x (P.map (algebraMap v.toValuationSubring F))) hS
  simpa [Polynomial.map_sub, Polynomial.map_mul, aeval_C, aeval_X, ← IsScalarTower.algebraMap_apply] using h

variable [Algebra.IsIntegral F F']

theorem algebraMap_mem_of_restrict_eq {w : Place K F'} {v : Place K F} (hw : w.restrict F = v)
    (r : v.toValuationSubring) : algebraMap F F' (r : F) ∈ w.toValuationSubring := by
  have : (r : F) ∈ (w.restrict F).toValuationSubring := by rw [hw]; exact r.2
  exact (Place.mem_restrict_iff w).mp this

theorem aeval_mem_of_restrict_eq {w : Place K F'} {v : Place K F} (hw : w.restrict F = v)
    (S : Polynomial v.toValuationSubring) {x : F'} (hxmem : x ∈ w.toValuationSubring) :
    aeval x (S.map (algebraMap v.toValuationSubring F)) ∈ w.toValuationSubring := by
  rw [aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [coeff_map, Algebra.smul_def]
  exact mul_mem (algebraMap_mem_of_restrict_eq hw _) (pow_mem hxmem i)

theorem root_mem_of_restrict_eq {w : Place K F'} {v : Place K F} (hw : w.restrict F = v)
    {Q : Polynomial v.toValuationSubring} (hQ : Q.Monic) {x : F'}
    (hx : aeval x (Q.map (algebraMap v.toValuationSubring F)) = 0) : x ∈ w.toValuationSubring := by
  have hmonic : ((Q.map (algebraMap v.toValuationSubring F)).map (algebraMap F F')).Monic := (hQ.map _).map _
  refine w.mem_of_eval_monic_eq_zero hmonic ?_ (x := x) ?_
  · intro i
    rw [coeff_map, coeff_map]
    exact algebraMap_mem_of_restrict_eq hw _
  · rwa [eval_map, ← aeval_def]

theorem ord_sub_eq_ramificationIndex_mul (v : Place K F) (Q : Polynomial v.toValuationSubring)
    {x : F'} (hx : aeval x (Q.map (algebraMap v.toValuationSubring F)) = 0)
    (b : v.toValuationSubring) (hsimple : IsUnit (Q.derivative.eval b))
    {w : Place K F'} (hw : w.restrict F = v) (hxb : 0 < w.ord (x - algebraMap F F' (b : F))) :
    w.ord (x - algebraMap F F' (b : F))
      = Place.ramificationIndex (F := F) w * v.ord ((Q.eval b : v.toValuationSubring) : F) := by
  obtain ⟨S, hS, hSb⟩ := exists_taylor v Q b
  obtain ⟨T, hT, -⟩ := exists_taylor v S b
  set y := x - algebraMap F F' (b : F) with hy
  have hy0 : y ≠ 0 := by
    intro h; rw [h] at hxb; simp at hxb
  have hymem : y ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg hy0).mpr hxb.le
  have hxmem : x ∈ w.toValuationSubring := by
    have : x = y + algebraMap F F' (b : F) := by rw [hy]; ring
    rw [this]; exact add_mem hymem (algebraMap_mem_of_restrict_eq hw b)

  obtain ⟨hu0, hu⟩ := ord_coe_eq_zero_of_isUnit v hsimple
  set u : F' := algebraMap F F' ((Q.derivative.eval b : v.toValuationSubring) : F) with hu_def
  have hu0' : u ≠ 0 := (map_ne_zero_iff _ (algebraMap F F').injective).mpr hu0
  have huord : w.ord u = 0 := by
    rw [hu_def, w.ord_restrict (F := F), hw, hu, mul_zero]
  have humem : u ∈ w.toValuationSubring := algebraMap_mem_of_restrict_eq hw _
  set t := aeval x (T.map (algebraMap v.toValuationSubring F)) with ht
  have htmem : t ∈ w.toValuationSubring := aeval_mem_of_restrict_eq hw T hxmem
  have hSx : aeval x (S.map (algebraMap v.toValuationSubring F)) = u + y * t := by
    have h := aeval_taylor v hT x
    rw [hSb] at h
    rw [← ht, ← hy] at h
    rw [← hu_def] at h
    linear_combination h
  have hyt : y * t = 0 ∨ 0 < w.ord (y * t) := by
    rcases eq_or_ne t 0 with ht0 | ht0
    · left; rw [ht0, mul_zero]
    · right
      rw [w.ord_mul hy0 ht0]
      have : 0 ≤ w.ord t := (w.mem_iff_ord_nonneg ht0).mp htmem
      omega
  obtain ⟨hs0, hsord⟩ := ord_add_eq_zero w hu0' huord humem (mul_mem hymem htmem) hyt

  have hmain : y * (u + y * t) = -algebraMap F F' ((Q.eval b : v.toValuationSubring) : F) := by
    have h := aeval_taylor v hS x
    rw [hx, hSx, ← hy] at h
    linear_combination -h
  have hQb0 : algebraMap F F' ((Q.eval b : v.toValuationSubring) : F) ≠ 0 := by
    intro h
    rw [h, neg_zero] at hmain
    exact (mul_ne_zero hy0 hs0) hmain
  have h1 : w.ord (y * (u + y * t)) = w.ord y := by rw [w.ord_mul hy0 hs0, hsord, add_zero]
  rw [hmain, Place.ord_neg, w.ord_restrict (F := F), hw] at h1
  exact h1.symm

variable [Module.Finite F F'] [HasPrincipalDivisors K F']

theorem exists_place_of_simple_root (H : Divisor.PushforwardNormFormula K F F') (v : Place K F)
    {Q : Polynomial v.toValuationSubring} (hQ : Q.Monic) {x : F'}
    (hx : aeval x (Q.map (algebraMap v.toValuationSubring F)) = 0)
    (b : v.toValuationSubring) (hroot : 0 < v.ord ((Q.eval b : v.toValuationSubring) : F))
    (hsimple : IsUnit (Q.derivative.eval b))
    (hnorm : v.ord (Algebra.norm F (x - algebraMap F F' (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F)) :
    ∃ w₀ : Place K F', w₀.restrict F = v ∧ 0 < w₀.ord (x - algebraMap F F' (b : F)) ∧
      Place.ramificationIndex (F := F) w₀ = 1 ∧ w₀.inertiaDeg F = 1 ∧
      ∀ w : Place K F', w.restrict F = v → 0 < w.ord (x - algebraMap F F' (b : F)) → w = w₀ := by
  classical
  have hQb0 : ((Q.eval b : v.toValuationSubring) : F) ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hroot; exact lt_irrefl _ hroot
  set y := x - algebraMap F F' (b : F) with hy
  have hy0 : y ≠ 0 := by
    intro h0
    obtain ⟨S, hS, -⟩ := exists_taylor v Q b
    have h := aeval_taylor v hS x
    rw [hx, ← hy, h0, zero_mul, zero_sub, neg_eq_zero] at h
    exact hQb0 ((map_eq_zero_iff _ (algebraMap F F').injective).mp h)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) y hy0
  have hpush := H y hy0 D hD v
  rw [hnorm, Divisor.pushforward_apply, ← Finset.sum_filter] at hpush
  set T : Finset (Place K F') := D.support.filter (fun w => w.restrict F = v) with hT
  have hmemT : ∀ w, w ∈ T ↔ w.restrict F = v ∧ 0 < w.ord y := by
    intro w
    rw [hT, Finset.mem_filter, Finsupp.mem_support_iff, hD w]
    constructor
    · rintro ⟨hne, hw⟩
      have hymem : y ∈ w.toValuationSubring :=
        sub_mem (root_mem_of_restrict_eq hw hQ hx) (algebraMap_mem_of_restrict_eq hw b)
      exact ⟨hw, lt_of_le_of_ne ((w.mem_iff_ord_nonneg hy0).mp hymem) (Ne.symm hne)⟩
    · rintro ⟨hw, hpos⟩
      exact ⟨by omega, hw⟩

  have hterm : ∀ w ∈ T, D w * (w.inertiaDeg F : ℤ)
      = v.ord ((Q.eval b : v.toValuationSubring) : F) * ((Place.ramificationIndex (F := F) w * w.inertiaDeg F : ℕ) : ℤ) := by
    intro w hwT
    obtain ⟨hw, hpos⟩ := (hmemT w).mp hwT
    rw [hD w, ord_sub_eq_ramificationIndex_mul v Q hx b hsimple hw hpos]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hpush

  have hm0 : v.ord ((Q.eval b : v.toValuationSubring) : F) ≠ 0 := by omega
  have hsum1 : ∑ w ∈ T, (Place.ramificationIndex (F := F) w * w.inertiaDeg F) = 1 := by
    have h := hpush
    have h2 : v.ord ((Q.eval b : v.toValuationSubring) : F)
        * ((∑ w ∈ T, (Place.ramificationIndex (F := F) w * w.inertiaDeg F : ℕ) : ℤ) - 1) = 0 := by
      push_cast at h ⊢
      linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hm0
    · exact_mod_cast sub_eq_zero.mp h3
  obtain ⟨w₀, hT0, hw₀⟩ := eq_singleton_of_sum_eq_one T _ (fun w _ =>
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (w.ramificationIndex_pos (F := F)).ne'
      (w.inertiaDeg_pos_of_finiteDimensional (F := F)).ne')) hsum1
  have hw₀T : w₀ ∈ T := by rw [hT0]; exact Finset.mem_singleton_self _
  obtain ⟨hres, hpos⟩ := (hmemT w₀).mp hw₀T
  refine ⟨w₀, hres, hpos, Nat.eq_one_of_mul_eq_one_right hw₀, Nat.eq_one_of_mul_eq_one_left hw₀, ?_⟩
  intro w hw hwpos
  have : w ∈ T := (hmemT w).mpr ⟨hw, hwpos⟩
  rw [hT0] at this
  exact Finset.mem_singleton.mp this

end Engine

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [CharZero F]
  [HasPrincipalDivisors K F']

theorem exists_place_of_simple_root_along (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (v : Place K F) {Q : Polynomial v.toValuationSubring} (hQ : Q.Monic) {x : F'}
    (hx : (Q.map (algebraMap v.toValuationSubring F)).eval₂ φ.toRingHom x = 0)
    (b : v.toValuationSubring) (hroot : 0 < v.ord ((Q.eval b : v.toValuationSubring) : F))
    (hsimple : IsUnit (Q.derivative.eval b))
    (hnorm : letI := algebraAlong φ; v.ord (Algebra.norm F (x - φ (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F)) :
    ∃ w₀ : Place K F', w₀.restrictAlong φ hφ = v ∧ 0 < w₀.ord (x - φ (b : F)) ∧
      w₀.ramificationIndexAlong φ = 1 ∧ w₀.inertiaDegAlong φ hφ = 1 ∧
      ∀ w : Place K F', w.restrictAlong φ hφ = v → 0 < w.ord (x - φ (b : F)) → w = w₀ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  have H : Divisor.PushforwardNormFormula K F F' := normFormulaAlong φ hfin (separableAlong_of_charZero φ hφ)
  have hx' : aeval x (Q.map (algebraMap v.toValuationSubring F)) = 0 := by
    rw [aeval_def]; exact hx
  exact exists_place_of_simple_root H v hQ hx' b hroot hsimple hnorm

end Along

end S09SR

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [CharZero F] [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (v : Place K F) {Q : Polynomial v.toValuationSubring} (hQ : Q.Monic) {x : F'} (hx : (Q.map (algebraMap v.toValuationSubring F)).eval₂ φ.toRingHom x = 0) (b : v.toValuationSubring) (hroot : 0 < v.ord ((Q.eval b : v.toValuationSubring) : F)) (hsimple : IsUnit ((Polynomial.derivative Q).eval b)) (hnorm : letI := algebraAlong φ; v.ord (Algebra.norm F (x - φ (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F)) : ∃ w₀ : Place K F', w₀.restrictAlong φ hφ = v ∧ 0 < w₀.ord (x - φ (b : F)) ∧ w₀.ramificationIndexAlong φ = 1 ∧ w₀.inertiaDegAlong φ hφ = 1 ∧ ∀ w : Place K F', w.restrictAlong φ hφ = v → 0 < w.ord (x - φ (b : F)) → w = w₀ := by
  exact S09SR.exists_place_of_simple_root_along φ hφ hfin v hQ hx b hroot hsimple hnorm

end S_AlgebraicCurve_exists_place_over_of_simple_root_along
end P2MW
export P2MW.S_AlgebraicCurve_exists_place_over_of_simple_root_along (solution)
