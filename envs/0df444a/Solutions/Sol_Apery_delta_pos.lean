-- Prove2me | solution 1 for Apery.delta_pos
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-11T23:27:33.377715+00:00
-- url     : https://prove2.me/submissions/06a81fa0-792b-4a6e-85b0-39cc63340f71

/-
# Irrationality of $\\zeta(5)$ via normalized Hankel determinants
# Proposition 2.2 (strict determinant positivity) — reduction to `Apery.moment_rep`

This file proves the platform theorem `Apery.delta_pos`,

  `0 < aeval zeta5 (Δ n)`  for `n > 0`,

from the already-proved platform theorem `Apery.moment_rep` (the positive-weight
moment representation). The argument is the second half of
`Apery/Positivity.lean` of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0: the matrix `G n` evaluated
at `ζ(5)` is the Gram matrix of the positive weight `ν(y) = D_N(y²)^6 / D_K(y²) · w(y)`
on `(0,∞)`, hence its determinant is strictly positive.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_MomentWeight
import Theorems.Thm_Apery_moment_rep

set_option autoImplicit false

open Polynomial MeasureTheory Set Finset
open scoped Matrix

namespace Apery

lemma summable_w_term {y : ℝ} (hy : 0 < y) :
    Summable fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 4 (r := 2 * Real.pi * y) (by positivity)
  have h2 := (summable_nat_add_iff 1).mpr h
  refine h2.congr fun ℓ => ?_
  push_cast
  ring_nf

lemma wS_pos {y : ℝ} (hy : 0 < y) : 0 < wS y :=
  (summable_w_term hy).tsum_pos (fun ℓ => by positivity) 0 (by positivity)

lemma w_pos {y : ℝ} (hy : 0 < y) : 0 < w y := by
  unfold w; have := wS_pos hy; positivity

lemma aeval_D_pos (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 < aeval t (D m) := by
  simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]
  refine Finset.prod_pos fun j hj => ?_
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  positivity

/-- The positive weight `ν(y) = D_N(y²)^6 / D_K(y²) · w(y)`. -/
noncomputable def ν (n : ℕ) (y : ℝ) : ℝ :=
  aeval (y ^ 2) (D (3 * n)) ^ 6 / aeval (y ^ 2) (D (40 * n)) * w y

lemma ν_pos (n : ℕ) {y : ℝ} (hy : 0 < y) : 0 < ν n y := by
  unfold ν
  have h1 := aeval_D_pos (3 * n) (t := y ^ 2) (by positivity)
  have h2 := aeval_D_pos (40 * n) (t := y ^ 2) (by positivity)
  have h3 := w_pos hy
  positivity

lemma integrand_eq (n : ℕ) (i j : ℕ) (y : ℝ) :
    integrand (40 * n) (D (3 * n) ^ 6 * X ^ (i + j)) y =
      (y ^ 2) ^ i * (y ^ 2) ^ j * ν n y := by
  simp only [integrand, ν, map_mul, map_pow, aeval_X]
  rw [pow_add]; ring

/-- **Positivity**: `Δ_K(ζ(5)) > 0`, from the moment representation. -/
theorem delta_pos_aux (n : ℕ) (_hn : 0 < n) : 0 < aeval zeta5 (Δ n) := by
  have hdet : aeval zeta5 (Δ n) = ((G n).map (aeval zeta5)).det := by
    have := RingHom.map_det (aeval zeta5 : ℚ[X] →ₐ[ℚ] ℝ).toRingHom (G n)
    simpa [Δ, RingHom.mapMatrix_apply] using this
  rw [hdet]
  set M : Matrix (Fin (37 * n)) (Fin (37 * n)) ℝ := (G n).map (aeval zeta5) with hM
  have hentry : ∀ i j : Fin (37 * n), M i j =
      ∫ y in Ioi 0, integrand (40 * n) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ))) y :=
    fun i j => (moment_rep _ _).2
  have hint : ∀ i j : Fin (37 * n),
      IntegrableOn (integrand (40 * n) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ)))) (Ioi 0) :=
    fun i j => (moment_rep _ _).1
  apply Matrix.PosDef.det_pos
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [star_trivial, hM, Matrix.map_apply, G]
    rw [Nat.add_comm (j : ℕ) i]
  · intro x hx
    set f : Fin (37 * n) → Fin (37 * n) → ℝ → ℝ := fun i j y =>
      x i * x j * integrand (40 * n) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ))) y with hf
    have hfint : ∀ i j, IntegrableOn (f i j) (Ioi 0) := fun i j => (hint i j).const_mul _
    have hpt : ∀ y, ∑ i, ∑ j, f i j y = (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y := by
      intro y
      simp only [hf, integrand_eq]
      rw [sq (∑ i, x i * (y ^ 2) ^ (i : ℕ)), Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hq : star x ⬝ᵥ (M *ᵥ x) = ∫ y in Ioi 0, (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y := by
      have h1 : star x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, ∫ y in Set.Ioi 0, f i j y := by
        simp only [dotProduct, Matrix.mulVec, star_trivial, hentry, hf, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]; ring
      rw [h1]
      have h2 : ∀ i, ∑ j, ∫ y in Set.Ioi 0, f i j y = ∫ y in Set.Ioi 0, ∑ j, f i j y :=
        fun i => (integral_finsetSum _ (fun j _ => hfint i j)).symm
      simp_rw [h2]
      rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hfint i j))]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => hpt y)
    rw [hq]
    have hsq : IntegrableOn (fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y) (Ioi 0) := by
      have : (fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y) = fun y => ∑ i, ∑ j, f i j y :=
        funext fun y => (hpt y).symm
      rw [this]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hfint i j
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
        fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y := by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
      exact mul_nonneg (sq_nonneg _) (ν_pos n hy).le
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hsq]
    set q : ℝ[X] := ∑ i : Fin (37 * n), C (x i) * X ^ (i : ℕ) with hqdef
    have hqeval : ∀ y : ℝ, q.eval (y ^ 2) = ∑ i, x i * (y ^ 2) ^ (i : ℕ) := by
      intro y; simp [hqdef, eval_finsetSum]
    have hq0 : q ≠ 0 := by
      intro h0
      apply hx
      funext i
      have hc : q.coeff (i : ℕ) = x i := by
        simp only [hqdef, finsetSum_coeff, coeff_C_mul_X_pow]
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h.symm)
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [← hc, h0, coeff_zero]; rfl
    have hroots : Set.Finite {t : ℝ | IsRoot q t} := Polynomial.finite_setOfPred_isRoot hq0
    have hB : Set.Finite {y : ℝ | IsRoot q (y ^ 2)} := by
      refine (hroots.image Real.sqrt |>.union (hroots.image fun t => -Real.sqrt t)).subset ?_
      intro y hy
      simp only [Set.mem_ofPred_eq] at hy
      rcases le_or_gt 0 y with h | h
      · exact Or.inl ⟨y ^ 2, hy, Real.sqrt_sq h⟩
      · exact Or.inr ⟨y ^ 2, hy, by
          show -Real.sqrt (y ^ 2) = y
          rw [Real.sqrt_sq_eq_abs, abs_of_neg h, neg_neg]⟩
    have hsub : Set.Ioi 0 \ {y : ℝ | IsRoot q (y ^ 2)} ⊆
        Function.support (fun y => (∑ i, x i * (y ^ 2) ^ (i : ℕ)) ^ 2 * ν n y) ∩ Set.Ioi 0 := by
      intro y hy
      obtain ⟨hy0, hyB⟩ := hy
      refine ⟨?_, hy0⟩
      simp only [Function.mem_support]
      have hqy : q.eval (y ^ 2) ≠ 0 := fun h => hyB h
      rw [hqeval] at hqy
      exact mul_ne_zero (pow_ne_zero _ hqy) (ν_pos n hy0).ne'
    calc (0 : ENNReal) < ⊤ := ENNReal.zero_lt_top
      _ = volume (Set.Ioi (0 : ℝ) \ {y : ℝ | IsRoot q (y ^ 2)}) := by
        rw [measure_sdiff_null (hB.measure_zero volume), Real.volume_Ioi]
      _ ≤ _ := measure_mono hsub

end Apery

open MeasureTheory Polynomial in
/-- The platform target `Apery.delta_pos`, restated at top level as `solution`. -/
theorem solution (n : ℕ) (hn : 0 < n) : 0 < aeval Apery.zeta5 (Apery.Δ n) :=
  Apery.delta_pos_aux n hn
