-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.ell_sub_ell_eq_genus_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/25ad3494-97bf-5071-8a86-e82b9c36d884

import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ell_sub_ell_eq_genus_zero
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

open Polynomial IsDedekindDomain WithZero AlgebraicCurve AlgebraicCurve.RationalFunctionField

universe u v

namespace RRSol

section principal

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.ord_nonneg_iff_mem (v : Place K F) {f : F} (hf : f ≠ 0) :
    0 ≤ v.ord f ↔ f ∈ v.toValuationSubring := by
  rw [v.mem_iff_adicValuation_le_one,
    show v.adicValuation f = exp (-v.ord f) by
      rw [Place.ord, neg_neg, exp_log (v.adicValuation_ne_zero hf)],
    ← exp_zero, exp_le_exp, neg_nonpos]

theorem lSpace_add_map_mulLeft {D P : Divisor K F} {f : F} (hf : f ≠ 0)
    (hP : ∀ v : Place K F, P v = v.ord f) :
    (LSpace (D + P)).map (LinearMap.mulLeft K f) = LSpace D := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    replace hg : g ∈ LSpace (D + P) := hg
    rw [LinearMap.mulLeft_apply]
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [mul_zero]; exact (LSpace D).zero_mem
    · rw [mem_lSpace_iff_ord] at hg ⊢
      refine Or.inr fun v => ?_
      rcases hg with h | h
      · exact absurd h hg0
      · have := h v
        rw [v.ord_mul hf hg0, ← hP v]
        simp only [Finsupp.coe_add, Pi.add_apply, neg_add] at this
        linarith
  · intro g hg
    refine ⟨f⁻¹ * g, ?_, by rw [LinearMap.mulLeft_apply, ← mul_assoc, mul_inv_cancel₀ hf, one_mul]⟩
    show f⁻¹ * g ∈ LSpace (D + P)
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [mul_zero]; exact (LSpace (D + P)).zero_mem
    · rw [mem_lSpace_iff_ord] at hg ⊢
      refine Or.inr fun v => ?_
      rcases hg with h | h
      · exact absurd h hg0
      · have := h v
        rw [v.ord_mul (inv_ne_zero hf) hg0, v.ord_inv, ← hP v]
        simp only [Finsupp.coe_add, Pi.add_apply, neg_add]
        linarith

theorem ell_add_of_forall_eq_ord {D P : Divisor K F} {f : F} (hf : f ≠ 0)
    (hP : ∀ v : Place K F, P v = v.ord f) : ell (D + P) = ell D := by
  have e := Submodule.equivMapOfInjective (LinearMap.mulLeft K f)
    (mul_right_injective₀ hf) (LSpace (D + P))
  rw [lSpace_add_map_mulLeft hf hP] at e
  exact e.finrank_eq

end principal

namespace RationalFunctionField

variable (K : Type u) [Field K]

noncomputable def polyIncl : K[X] →ₗ[K] RatFunc K :=
  (IsScalarTower.toAlgHom K K[X] (RatFunc K)).toLinearMap

@[scoped simp] theorem polyIncl_apply (q : K[X]) : polyIncl K q = algebraMap K[X] (RatFunc K) q := rfl

theorem polyIncl_injective : Function.Injective (polyIncl K) :=
  fun _ _ h => RatFunc.algebraMap_injective K h

variable [DecidableEq (RatFunc K)]

theorem placeInfty_ne_ofHeightOneSpectrum' (w : HeightOneSpectrum K[X]) :
    placeInfty K ≠ Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w := by
  intro h
  have hX : algebraMap K[X] (RatFunc K) X ∈ (placeInfty K).toValuationSubring := by
    rw [h]; exact algebraMap_mem_ofHeightOneSpectrum K w X
  rw [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff, RatFunc.algebraMap_X,
    RatFunc.inftyValuation.X, ← exp_zero, exp_le_exp] at hX
  exact absurd hX (by norm_num)

theorem smul_single_placeInfty_apply_ofHeightOneSpectrum (n : ℤ) (w : HeightOneSpectrum K[X]) :
    (n • Finsupp.single (placeInfty K) (1 : ℤ)) (Place.ofHeightOneSpectrum w) = 0 := by
  classical
  rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (placeInfty_ne_ofHeightOneSpectrum' K w),
    smul_zero]

@[scoped simp] theorem smul_single_placeInfty_apply_placeInfty (n : ℤ) :
    (n • Finsupp.single (placeInfty K) (1 : ℤ)) (placeInfty K) = n := by
  rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem algebraMap_mem_lSpace_smul_single_placeInfty_iff (n : ℤ) {q : K[X]} (hq : q ≠ 0) :
    algebraMap K[X] (RatFunc K) q ∈ LSpace (n • Finsupp.single (placeInfty K) (1 : ℤ)) ↔
      (q.natDegree : ℤ) ≤ n := by
  have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  rw [mem_lSpace_iff_ord, or_iff_right hq']
  constructor
  · intro h
    have := h (placeInfty K)
    rw [smul_single_placeInfty_apply_placeInfty, ord_placeInfty_algebraMap hq] at this
    linarith
  · intro hn v
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    · rw [smul_single_placeInfty_apply_ofHeightOneSpectrum, neg_zero]
      exact (Place.ord_nonneg_iff_mem _ hq').mpr (algebraMap_mem_ofHeightOneSpectrum K w q)
    · rw [smul_single_placeInfty_apply_placeInfty, ord_placeInfty_algebraMap hq]
      linarith

omit [DecidableEq (RatFunc K)] in

theorem exists_eq_algebraMap_of_forall_ord_nonneg {g : RatFunc K} (hg : g ≠ 0)
    (h : ∀ w : HeightOneSpectrum K[X], 0 ≤ (Place.ofHeightOneSpectrum (K := K) w).ord g) :
    ∃ q : K[X], algebraMap K[X] (RatFunc K) q = g := by
  have := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := K[X]) (RatFunc K) g fun w =>
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := RatFunc K) w).le_one_iff_le_one.mpr
      ((Place.mem_iff_adicValuation_le_one _).mp ((Place.ord_nonneg_iff_mem _ hg).mp (h w)))
  exact this

theorem lSpace_smul_single_placeInfty (n : ℤ) :
    LSpace (n • Finsupp.single (placeInfty K) (1 : ℤ)) =
      (Polynomial.degreeLT K (n + 1).toNat).map (polyIncl K) := by
  ext g
  rw [Submodule.mem_map]
  constructor
  · intro hg
    rcases eq_or_ne g 0 with rfl | hg0
    · exact ⟨0, Submodule.zero_mem _, map_zero _⟩
    · have hord : ∀ v, -(n • Finsupp.single (placeInfty K) (1 : ℤ)) v ≤ v.ord g :=
        ((mem_lSpace_iff_ord).mp hg).resolve_left hg0
      obtain ⟨q, rfl⟩ := exists_eq_algebraMap_of_forall_ord_nonneg K hg0 fun w => by
        simpa only [smul_single_placeInfty_apply_ofHeightOneSpectrum, neg_zero] using
          hord (Place.ofHeightOneSpectrum w)
      have hq : q ≠ 0 := by rintro rfl; exact hg0 (map_zero _)
      have hdeg : (q.natDegree : ℤ) ≤ n :=
        (algebraMap_mem_lSpace_smul_single_placeInfty_iff K n hq).mp hg
      refine ⟨q, ?_, rfl⟩
      rw [Polynomial.mem_degreeLT]
      exact (Polynomial.natDegree_lt_iff_degree_lt hq).mp (Int.lt_toNat.mpr (by omega))
  · rintro ⟨q, hq, rfl⟩
    rcases eq_or_ne q 0 with rfl | hq0
    · rw [map_zero]; exact Submodule.zero_mem _
    · rw [polyIncl_apply, algebraMap_mem_lSpace_smul_single_placeInfty_iff K n hq0]
      rw [Polynomial.mem_degreeLT] at hq
      have := Int.lt_toNat.mp ((Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hq)
      omega

theorem ell_smul_single_placeInfty (n : ℤ) :
    ell (n • Finsupp.single (placeInfty K) (1 : ℤ)) = (n + 1).toNat := by
  have e := Submodule.equivMapOfInjective (polyIncl K) (polyIncl_injective K)
    (Polynomial.degreeLT K (n + 1).toNat)
  rw [← lSpace_smul_single_placeInfty] at e
  rw [ell, ← e.finrank_eq, (Polynomial.degreeLTEquiv K _).finrank_eq, Module.finrank_fin_fun]

theorem ell_eq_max (D : Divisor K (RatFunc K)) :
    (ell D : ℤ) = max (Divisor.degree D + 1) 0 := by
  set d := Divisor.degree D with hd
  have hdeg0 : Divisor.degree (D - d • Finsupp.single (placeInfty K) (1 : ℤ)) = 0 := by
    rw [map_sub, map_zsmul, Divisor.degree_single, deg_placeInfty]; simp [hd]
  obtain ⟨f, hf, hDf⟩ := isPrincipal_of_degree_eq_zero _ hdeg0
  have hsplit : D = d • Finsupp.single (placeInfty K) (1 : ℤ) +
      (D - d • Finsupp.single (placeInfty K) (1 : ℤ)) := by abel
  rw [hsplit, ell_add_of_forall_eq_ord hf hDf, ell_smul_single_placeInfty, Int.toNat_eq_max]

theorem ell_sub_ell_eq_genus_zero (D : Divisor K (RatFunc K)) :
    (ell D : ℤ) - ell ((-2 : ℤ) • Finsupp.single (placeInfty K) (1 : ℤ) - D) =
      Divisor.degree D + 1 - ((0 : ℕ) : ℤ) := by
  rw [ell_eq_max, ell_eq_max, map_sub, map_zsmul, Divisor.degree_single, deg_placeInfty]
  simp only [Nat.cast_one, mul_one, smul_eq_mul, Nat.cast_zero, sub_zero]
  rcases le_or_gt (-1) (Divisor.degree D) with h | h
  · rw [max_eq_left (by omega), max_eq_right (by omega)]; ring
  · rw [max_eq_right (by omega), max_eq_left (by omega)]; ring

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_ell_sub_ell_eq_genus_zero.RRSol.RationalFunctionField"

end RRSol
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_ell_sub_ell_eq_genus_zero.RRSol.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_ell_sub_ell_eq_genus_zero.RRSol"

theorem solution
    (K : Type u) [Field K] [DecidableEq (RatFunc K)] (D : Divisor K (RatFunc K)) :
    (ell D : ℤ) - ell ((-2 : ℤ) • Finsupp.single (placeInfty K) (1 : ℤ) - D) =
      Divisor.degree D + 1 - ((0 : ℕ) : ℤ) :=
  RRSol.RationalFunctionField.ell_sub_ell_eq_genus_zero K D

end S_AlgebraicCurve_RationalFunctionField_ell_sub_ell_eq_genus_zero
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_ell_sub_ell_eq_genus_zero (solution)
