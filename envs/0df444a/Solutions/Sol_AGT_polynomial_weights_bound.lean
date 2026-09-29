-- Prove2me | solution 1 for AGT.polynomial_weights_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-12T17:57:14.81757+00:00
-- url     : https://prove2.me/submissions/d8d30f22-7455-425d-a605-f31b7753346f

import Definitions.Def_agt_regret
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic

namespace AGTpw

open Finset AGT

variable {n : ℕ}

/-- `exp (-(x + x²)) ≤ 1 - x` on `[0, 1/2]`: the lower-bound counterpart of
`1 - x ≤ exp (-x)`, and the only analytic input of Theorem 4.6 beyond the
standard exponential bound.  It comes from the quadratic lower bound
`1 + z + z²/2 ≤ exp z` at `z = x + x²`, which reduces the claim to the
polynomial inequality `x² (1 - x - x² - x³) ≥ 0`. -/
theorem exp_neg_add_sq_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-(x + x ^ 2)) ≤ 1 - x := by
  have hz0 : 0 ≤ x + x ^ 2 := by positivity
  have hq : 1 + (x + x ^ 2) + (x + x ^ 2) ^ 2 / 2 ≤ Real.exp (x + x ^ 2) :=
    Real.quadratic_le_exp_of_nonneg hz0
  have hkey : 1 ≤ (1 - x) * (1 + (x + x ^ 2) + (x + x ^ 2) ^ 2 / 2) := by
    nlinarith [sq_nonneg x, pow_nonneg hx0 3, pow_nonneg hx0 4, pow_nonneg hx0 5,
      mul_nonneg hx0 hx0, sq_nonneg (x * x)]
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  refine hkey.trans (mul_le_mul_of_nonneg_left hq (by linarith))

/-- The Polynomial Weights potential `W_t = ∑_i w_t(i)`. -/
def pot (η : ℝ) (ℓ : ℕ → Fin (n + 1) → ℝ) (t : ℕ) : ℝ :=
  ∑ j, pwWeights η ℓ t j

/-- The expected loss the algorithm actually suffers at time `t`. -/
noncomputable def eLoss (η : ℝ) (ℓ : ℕ → Fin (n + 1) → ℝ) (t : ℕ) : ℝ :=
  ∑ i, pwProb η ℓ t i * ℓ t i

end AGTpw

open AGT AGTpw Finset in
theorem solution {n : ℕ} (η : ℝ) (hη0 : 0 < η)
    (hη : η ≤ 1 / 2) (ℓ : ℕ → Fin (n + 1) → ℝ)
    (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (k : Fin (n + 1)) :
    ∑ t ∈ Finset.range T, ∑ i, pwProb η ℓ t i * ℓ t i ≤
      actionLoss ℓ k T + η * ∑ t ∈ Finset.range T, (ℓ t k) ^ 2 +
        Real.log (n + 1) / η := by
  classical
  have hℓ0 : ∀ t i, 0 ≤ ℓ t i := fun t i => (hℓ t i).1
  have hℓ1 : ∀ t i, ℓ t i ≤ 1 := fun t i => (hℓ t i).2
  have hsmall : ∀ t i, η * ℓ t i ≤ 1 / 2 := fun t i => by
    nlinarith [hℓ1 t i, hℓ0 t i]
  have hsmall0 : ∀ t i, 0 ≤ η * ℓ t i := fun t i => mul_nonneg hη0.le (hℓ0 t i)
  -- Every weight stays positive, hence so does the potential.
  have hwpos : ∀ t i, 0 < pwWeights η ℓ t i := by
    intro t
    induction t with
    | zero => intro i; simp [pwWeights]
    | succ t ih =>
        intro i
        have h : (0 : ℝ) < 1 - η * ℓ t i := by linarith [hsmall t i]
        exact mul_pos (ih i) h
  have hpotpos : ∀ t, 0 < pot η ℓ t := fun t =>
    Finset.sum_pos (fun i _ => hwpos t i) ⟨k, Finset.mem_univ k⟩
  -- The played expected loss as a weighted average.
  have hEeq : ∀ t, eLoss η ℓ t = (∑ i, pwWeights η ℓ t i * ℓ t i) / pot η ℓ t := by
    intro t
    simp only [eLoss, pwProb, pot, div_mul_eq_mul_div, ← Finset.sum_div]
  have hE0 : ∀ t, 0 ≤ eLoss η ℓ t := by
    intro t
    rw [hEeq t]
    exact div_nonneg (Finset.sum_nonneg fun i _ =>
      mul_nonneg (hwpos t i).le (hℓ0 t i)) (hpotpos t).le
  have hE1 : ∀ t, eLoss η ℓ t ≤ 1 := by
    intro t
    rw [hEeq t, div_le_one (hpotpos t)]
    exact Finset.sum_le_sum fun i _ => by nlinarith [hwpos t i, hℓ1 t i, hℓ0 t i]
  have hEsmall : ∀ t, η * eLoss η ℓ t ≤ 1 / 2 := fun t => by
    nlinarith [hE1 t, hE0 t]
  -- One step of the potential: `W_{t+1} = W_t (1 - η F_t)`.
  have hpotsucc : ∀ t, pot η ℓ (t + 1) = pot η ℓ t * (1 - η * eLoss η ℓ t) := by
    intro t
    have h1 : pot η ℓ (t + 1)
        = pot η ℓ t - η * ∑ i, pwWeights η ℓ t i * ℓ t i := by
      simp only [pot, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        show pwWeights η ℓ t i * (1 - η * ℓ t i) = _
        ring
    have h2 : pot η ℓ t * eLoss η ℓ t = ∑ i, pwWeights η ℓ t i * ℓ t i := by
      rw [hEeq t, mul_div_cancel₀ _ (hpotpos t).ne']
    rw [h1, show pot η ℓ t * (1 - η * eLoss η ℓ t)
      = pot η ℓ t - η * (pot η ℓ t * eLoss η ℓ t) from by ring, h2]
  have hpotprod : ∀ t, pot η ℓ t
      = (n + 1 : ℝ) * ∏ u ∈ range t, (1 - η * eLoss η ℓ u) := by
    intro t
    induction t with
    | zero => simp [pot, pwWeights, Finset.card_univ]
    | succ t ih => rw [hpotsucc t, ih, Finset.prod_range_succ]; ring
  have hwk : ∀ t, pwWeights η ℓ t k = ∏ u ∈ range t, (1 - η * ℓ u k) := by
    intro t
    induction t with
    | zero => simp [pwWeights]
    | succ t ih => rw [Finset.prod_range_succ, ← ih]; rfl
  -- Upper bound on the potential, from `1 - y ≤ exp (-y)`.
  have hUpper : pot η ℓ T
      ≤ (n + 1 : ℝ) * Real.exp (-(η * ∑ t ∈ range T, eLoss η ℓ t)) := by
    rw [hpotprod T]
    have hprod : ∏ u ∈ range T, (1 - η * eLoss η ℓ u)
        ≤ ∏ u ∈ range T, Real.exp (-(η * eLoss η ℓ u)) := by
      refine Finset.prod_le_prod (fun u _ => by linarith [hEsmall u]) (fun u _ => ?_)
      linarith [Real.add_one_le_exp (-(η * eLoss η ℓ u))]
    have hexp : ∏ u ∈ range T, Real.exp (-(η * eLoss η ℓ u))
        = Real.exp (-(η * ∑ t ∈ range T, eLoss η ℓ t)) := by
      rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [hexp] at hprod
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  -- Lower bound on the potential, from the single action `k`.
  have hLower : Real.exp
      (-(η * actionLoss ℓ k T + η ^ 2 * ∑ t ∈ range T, (ℓ t k) ^ 2)) ≤ pot η ℓ T := by
    have hstep : ∏ u ∈ range T, Real.exp (-(η * ℓ u k + (η * ℓ u k) ^ 2))
        ≤ ∏ u ∈ range T, (1 - η * ℓ u k) :=
      Finset.prod_le_prod (fun u _ => (Real.exp_pos _).le)
        (fun u _ => exp_neg_add_sq_le (hsmall0 u k) (hsmall u k))
    have hexp : ∏ u ∈ range T, Real.exp (-(η * ℓ u k + (η * ℓ u k) ^ 2))
        = Real.exp (-(η * actionLoss ℓ k T + η ^ 2 * ∑ t ∈ range T, (ℓ t k) ^ 2)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [actionLoss, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [hexp] at hstep
    refine hstep.trans ?_
    rw [← hwk T]
    exact Finset.single_le_sum (fun i _ => (hwpos T i).le) (Finset.mem_univ k)
  -- Compare the two bounds and take logarithms.
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hchain : Real.exp
        (-(η * actionLoss ℓ k T + η ^ 2 * ∑ t ∈ range T, (ℓ t k) ^ 2))
      ≤ Real.exp (Real.log ((n : ℝ) + 1) + -(η * ∑ t ∈ range T, eLoss η ℓ t)) := by
    refine hLower.trans (hUpper.trans ?_)
    rw [Real.exp_add, Real.exp_log hNpos]
  have hlog := Real.exp_le_exp.mp hchain
  -- `η L_PW ≤ η L_k + η² Q_k + log N`; divide by `η > 0`.
  have hexpand : η * (actionLoss ℓ k T + η * (∑ t ∈ range T, (ℓ t k) ^ 2)
        + Real.log ((n : ℝ) + 1) / η)
      = η * actionLoss ℓ k T + η ^ 2 * (∑ t ∈ range T, (ℓ t k) ^ 2)
        + Real.log ((n : ℝ) + 1) := by
    field_simp
  have hfin : η * (∑ t ∈ range T, eLoss η ℓ t)
      ≤ η * (actionLoss ℓ k T + η * (∑ t ∈ range T, (ℓ t k) ^ 2)
        + Real.log ((n : ℝ) + 1) / η) := by
    rw [hexpand]
    linarith [hlog]
  exact le_of_mul_le_mul_left hfin hη0
