-- Prove2me | Definitions.Def_ray_multibrot_potential
-- name    : ray_multibrot_potential
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T21:14:12.649059+00:00
-- url     : https://prove2.me/theorems/8e959d49-4448-4c6a-bdd0-8a3c22f50e12
-- title:
--   ray (11/12): potential estimates for the Multibrot family
-- statement:
--   Quantitative estimates for the Multibrot family $z^d + c$. They cover iterates and their growth, the relation between the dynamical potential and $\log|z|$, lower bounds for the potential away from $M_d$, and explicit real bounds. The main consequence is that for every $c \notin M_d$ the point $(c, c)$ lies in the postcritical region, so the diagonal $\Phi(c) = b_c(c)$ of the continued Böttcher map is defined and analytic on $\widehat{\mathbb{C}} \setminus M_d$.
--
--   This file is part 11 of 12 of a verbatim flattening of Geoffrey Irving's Lean 4 formalization *ray* (https://github.com/girving/ray, Apache License 2.0). Together the 12 files prove that the Mandelbrot set is connected. Each original ray module is wrapped in its own `section`, and module-system keywords are removed. A few mechanical edits avoid clashes with the full Mathlib import and avoid syntax extensions: a duplicated private definition is dropped, `ContinuousOn.partialSups` is renamed to `ContinuousOn.rayPartialSups`, `Finset.antidiagonal` is written as `Finset.HasAntidiagonal.antidiagonal`, the `bound_destruct` attribute macro is inlined, and the notation `𝕊` is replaced by `(OnePoint ℂ)`. The files are split only because of the compile-time limit. Declaration names are ray's own.
-- source:
--   Geoffrey Irving, ray: The Mandelbrot set is connected (Lean 4 formalization), https://github.com/girving/ray (Apache License 2.0), commit of 2026-08-16; module list in the file header. Mathematical background: A. Douady and J. H. Hubbard, Itération des polynômes quadratiques complexes, C. R. Acad. Sci. Paris 294 (1982); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Section 9 and Appendix; Carleson–Gamelin, Complex Dynamics, Ch. VIII.

import Definitions.Def_ray_riemann_sphere_multibrot

/-!
# ray (11/12): potential estimates for the Multibrot family

Part 11 of 12 of a flattened copy of Geoffrey Irving's Lean 4 formalization *ray*
(https://github.com/girving/ray, Apache License 2.0, Copyright Geoffrey Irving), which proves that
the Mandelbrot set is connected. Each original module is wrapped in its own `section`;
module-system keywords are removed, and a few names are adjusted to avoid clashes with Mathlib.

Original modules in this file:
* `Ray.Multibrot.Specific`
* `Ray.Multibrot.Log1p`
* `Ray.Multibrot.Iterates`
* `Ray.Multibrot.Potential`
* `Ray.Multibrot.PotentialLower`
* `Ray.Multibrot.Rinv`
* `Ray.Multibrot.Postcritical`
* `Ray.Multibrot.RealBounds`
-/

-- ===== Ray.Multibrot.Specific =====
section Ray_Ray_Multibrot_Specific
/-!
## Bounds about `exp`, `log` at specific values or bounds
-/

open Real (exp log)
open Set
noncomputable section

-- We do big `norm_num` calculations in this file
set_option exponentiation.threshold 2000

/-- `exp a < b` in terms `norm_num` can handle `-/
lemma exp_ofNat_lt {a : ℕ} {b : ℝ} (a0 : a ≠ 0 := by norm_num)
    (h0 : 2.7182818286 ^ a < b := by norm_num) : exp a < b := by
  rw [←Real.exp_one_pow a]
  exact _root_.trans (pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_nonneg _) a0) h0

/-- `exp (-a) < b` in terms `norm_num` can handle `-/
lemma exp_neg_ofNat_lt {a : ℕ} {b : ℝ} (a0 : a ≠ 0 := by norm_num)
    (b0 : 0 < b := by norm_num) (h0 : b⁻¹ < 2.7182818283 ^ a := by norm_num) : exp (-a) < b := by
  rw [Real.exp_neg, inv_lt_comm₀, ←Real.exp_one_pow a]
  · exact _root_.trans h0 (pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) a0)
  · exact Real.exp_pos _
  · exact b0

/-- `b < exp a` in terms `norm_num` can handle `-/
lemma lt_exp_ofNat {a : ℕ} {b : ℝ} (a0 : a ≠ 0 := by norm_num)
    (h0 : b < 2.7182818283 ^ a := by norm_num) : b < exp a := by
  rw [←Real.exp_one_pow a]
  exact _root_.trans h0 (pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) a0)

/-- `c < exp (a/b)` in terms `norm_num` can handle `-/
lemma lt_exp_div {a b : ℕ} {c : ℝ} (a0 : a ≠ 0 := by norm_num) (b0 : b ≠ 0 := by norm_num)
    (c0 : 0 < c := by norm_num) (h0 : c ^ b < 2.7182818283 ^ a := by norm_num) :
    c < exp (a / b) := by
  have e : exp (a/b : ℝ) = exp 1 ^ (a / b : ℝ) := by rw [Real.exp_one_rpow]
  rw [e, div_eq_mul_inv, Real.rpow_mul (Real.exp_nonneg _), Real.lt_rpow_inv_iff_of_pos,
    Real.rpow_natCast, Real.rpow_natCast]
  · exact _root_.trans h0 (pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) a0)
  · exact c0.le
  · apply Real.rpow_nonneg (Real.exp_nonneg _)
  · simp only [Nat.cast_pos, Nat.pos_iff_ne_zero]; exact b0

/-- `exp (a/b) < c` in terms `norm_num` can handle `-/
lemma exp_div_lt {a b : ℕ} {c : ℝ} (a0 : a ≠ 0 := by norm_num) (b0 : b ≠ 0 := by norm_num)
    (c0 : 0 < c := by norm_num) (h0 : 2.7182818286 ^ a < c ^ b := by norm_num) :
    exp (a / b) < c := by
  have e : exp (a/b : ℝ) = exp 1 ^ (a / b : ℝ) := by rw [Real.exp_one_rpow]
  rw [e, div_eq_mul_inv, Real.rpow_mul (Real.exp_nonneg _), Real.rpow_inv_lt_iff_of_pos,
    Real.rpow_natCast, Real.rpow_natCast]
  · exact _root_.trans (pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_nonneg _) a0) h0
  · apply Real.rpow_nonneg (Real.exp_nonneg _)
  · exact c0.le
  · simp only [Nat.cast_pos, Nat.pos_iff_ne_zero]; exact b0

/-- `exp (-(a/b)) < c` in terms `norm_num` can handle `-/
lemma exp_neg_div_lt {a b : ℕ} {c : ℝ} (a0 : a ≠ 0 := by norm_num)
    (b0 : b ≠ 0 := by norm_num) (c0 : 0 < c := by norm_num)
    (h0 : c⁻¹ ^ b < 2.7182818283 ^ a := by norm_num) :
    exp (-(a / b : ℝ)) < c := by
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) c0]
  exact lt_exp_div a0 b0 (inv_pos.mpr c0) h0

/-- `c < exp (-(a/b))` in terms `norm_num` can handle `-/
lemma lt_exp_neg_div {a b : ℕ} {c : ℝ} (a0 : a ≠ 0 := by norm_num)
    (b0 : b ≠ 0 := by norm_num) (c0 : 0 < c := by norm_num)
    (h0 : 2.7182818286 ^ a < c⁻¹ ^ b := by norm_num) :
    c < exp (-(a / b : ℝ)) := by
  rw [Real.exp_neg, lt_inv_comm₀ c0 (Real.exp_pos _)]
  exact exp_div_lt a0 b0 (inv_pos.mpr c0) h0

-- Specific values of `exp`
lemma exp_two_thirds_lt : exp (2/3) < 1.95 := exp_div_lt
lemma le_exp_9 : 1000 ≤ exp 9 := (lt_exp_ofNat).le

-- Specific values of `log`
lemma lt_log_2 : 0.693 < log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  norm_num; exact exp_div_lt
lemma lt_log_3 : 1.098 < log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  norm_num; exact exp_div_lt
lemma log_3_lt : log 3 < 1.099 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  norm_num; exact lt_exp_div
lemma lt_log_4 : 1.386 < log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  norm_num; exact exp_div_lt
lemma log_4_lt : log 4 < 1.387 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  norm_num; exact lt_exp_div

/-- `-log (1 - 1/x) < 0.41` if `3 ≤ x` -/
lemma neg_log_one_sub_lt {x : ℝ} (x3 : 3 ≤ x) : -log (1 - 1/x) < 0.41 := by
  have le : 2/3 ≤ 1 - 1 / x := by
    rw [le_tsub_iff_le_tsub (by norm_num), one_div, inv_le_comm₀ (by positivity)]
    · exact le_trans (by norm_num) x3
    · norm_num
    · rw [one_div, inv_le_one_iff₀]; right; exact le_trans (by norm_num) x3
  rw [neg_lt, Real.lt_log_iff_exp_lt (lt_of_lt_of_le (by norm_num) le)]
  refine lt_of_lt_of_le ?_ le
  norm_num; exact exp_neg_div_lt

end
end Ray_Ray_Multibrot_Specific

-- ===== Ray.Multibrot.Log1p =====
section Ray_Ray_Multibrot_Log1p
/-!
## `Complex.log (1 + z) ≤ -Real.log (1 - abs z)` for `abs z < 1`
-/

open Set

/-- Bound `Complex.log (1 + z)` in terms of `Real.log`.

    It feels like this lemma should have an algebraic proof, but I don't see it:
      https://math.stackexchange.com/questions/4844828 -/
lemma Complex.norm_log_one_add_le' {z : ℂ} (z1 : ‖z‖ < 1) :
    ‖Complex.log (1 + z)‖ ≤ -Real.log (1 - ‖z‖) := by
  have m1 : ∀ t : ℝ, t ≤ 1 → t * ‖z‖ < 1 :=
    fun t m ↦ (mul_le_of_le_one_left (norm_nonneg _) m).trans_lt z1
  have dc : ∀ t : ℝ, t ∈ uIcc 0 1 →
      HasDerivAt (fun t : ℝ ↦ Complex.log (1 + t*z)) (z / (1 + t*z)) t := by
    intro t m
    apply HasDerivAt.clog_real
    · exact ((hasDerivAt_mul_const _).const_add _).comp_ofReal
    · apply Complex.mem_slitPlane_of_norm_lt_one
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp only [zero_le_one, uIcc_of_le, mem_Icc] at m
      apply m1
      simp only [abs_le]
      exact ⟨by linarith, m.2⟩
  have dr : ∀ t : ℝ, t ∈ uIcc 0 1 →
      HasDerivAt (fun t : ℝ ↦ -Real.log (1 - t * ‖z‖)) (- (-‖z‖ / (1 - t * ‖z‖))) t := by
    intro t m
    simp only [zero_le_one, uIcc_of_le, mem_Icc] at m
    exact (((hasDerivAt_mul_const (x := t) ‖z‖).const_sub 1).log
      ((sub_pos.mpr (m1 _ m.2)).ne')).neg
  have ic : IntervalIntegrable (fun t ↦ z / (1 + t*z)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    apply continuousOn_const.div (Continuous.continuousOn (by continuity))
    intro t ⟨t0,t1⟩
    rw [← norm_ne_zero_iff]
    apply ne_of_gt
    calc ‖1 + t*z‖
      _ ≥ ‖(1 : ℂ)‖ - ‖t*z‖ := by bound
      _ = 1 - |t| * ‖z‖ := by simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ > 0 := by refine sub_pos.mpr (m1 _ (abs_le.mpr ⟨by linarith, t1⟩))
  simp only [neg_div, neg_neg] at dr
  have ir : IntervalIntegrable (fun t ↦ ‖z‖ / (1 - t * ‖z‖)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    apply continuousOn_const.div (Continuous.continuousOn (by continuity))
    intro t ⟨_,t1⟩; exact ne_of_gt (sub_pos.mpr (m1 _ t1))
  have fc := intervalIntegral.integral_eq_sub_of_hasDerivAt dc ic
  have fr := intervalIntegral.integral_eq_sub_of_hasDerivAt dr ir
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero, Complex.log_one,
    sub_zero, Real.log_one, neg_zero] at fc fr
  rw [←fc, ←fr]
  clear dc dr fc fr
  apply le_trans (intervalIntegral.norm_integral_le_integral_norm zero_le_one) ?_
  apply intervalIntegral.integral_mono_on zero_le_one ic.norm ir
  intro t ⟨t0,t1⟩
  simp only [norm_div]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr (m1 _ t1)) ?_
  calc ‖1 + t * z‖
    _ ≥ ‖(1 : ℂ)‖ - ‖t * z‖ := by bound
    _ = 1 - t * ‖z‖ := by
      simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, _root_.abs_of_nonneg t0]

/-- The real version is simpler, but we'll use the complex version anyways -/
lemma Real.abs_log_one_add_le {x : ℝ} (x1 : |x| < 1) :
    |Real.log (1 + x)| ≤ -Real.log (1 - |x|) := by
  have h := Complex.norm_log_one_add_le' (z := x) ?_
  · rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_log] at h
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using h
    · simp only [abs_lt] at x1; linarith
  · simpa only [Complex.norm_real]

/-- Our bound is monotonic -/
lemma Real.neg_log_one_sub_mono {x y : ℝ} (xy : x ≤ y) (y1 : y < 1) :
    -Real.log (1 - x) ≤ -Real.log (1 - y) :=
  neg_le_neg (Real.log_le_log (by linarith) (by linarith))

/-- Our bound is `≤ 2` for `x ≤ 1/2` -/
lemma neg_log_one_sub_le_two {x : ℝ} (x2 : x ≤ 1/2) : -Real.log (1 - x) ≤ 2 := by
  apply le_trans (Real.neg_log_one_sub_mono x2 (by linarith)) ?_
  rw [neg_le, Real.le_log_iff_exp_le]
  · exact (exp_neg_ofNat_lt).le
  · norm_num

/-- Variable linear bound on `-log (1 - x)`.
    This is intended to be used with a concrete value for `c`, so that `norm_num` can work.  -/
lemma neg_log_one_sub_le_linear {x c : ℝ} (x0 : 0 ≤ x) (c1 : 1 < c)
    (xc : x ≤ min 1 (((c - 1) * 2)⁻¹ + 1)⁻¹) : -Real.log (1 - x) ≤ c * x := by
  rcases le_min_iff.mp xc with ⟨x1,xc⟩
  by_cases xz : x = 0
  · simp only [xz, sub_zero, Real.log_one, neg_zero, mul_zero, le_refl]
  by_cases xe : x = 1
  · simp only [xe, sub_self, Real.log_zero, neg_zero, mul_one]; linarith
  replace x1 := Ne.lt_of_le xe x1
  have x0' : 0 < x := (Ne.symm xz).lt_of_le x0
  have c1p : 0 < (c - 1) * 2 := mul_pos (sub_pos.mpr c1) (by norm_num)
  have x1p : 0 < 1 - x := by linarith
  have h := Complex.norm_log_one_add_sub_self_le (z := -x)
    (by simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg x0]; exact x1)
  simp only [Complex.norm_real, Real.norm_eq_abs, ←Complex.ofReal_one, ←Complex.ofReal_add,
    ←Complex.ofReal_log x1p.le, ←Complex.ofReal_sub, abs_le, abs_of_nonneg x0, ←Complex.ofReal_neg,
    ←sub_eq_add_neg, abs_neg] at h
  simp only [sub_neg_eq_add] at h
  replace h : -Real.log (1 - x) ≤ x + x^2 * (1 - x)⁻¹ / 2 := by linarith
  apply le_trans h
  rw [pow_two, mul_assoc, mul_div_assoc, ←mul_one_add, mul_comm x _]
  apply mul_le_mul_of_nonneg_right _ x0
  nth_rw 1 [←inv_inv x]
  rw [←mul_inv, mul_sub, mul_one, inv_mul_cancel₀ xz]
  rw [add_comm, ←le_sub_iff_add_le, div_le_iff₀ (by norm_num)]
  apply inv_le_of_inv_le₀ c1p
  rw [le_sub_iff_add_le, le_inv_comm₀ (add_pos (inv_pos.mpr c1p) (by norm_num)) x0']
  exact xc

end Ray_Ray_Multibrot_Log1p

-- ===== Ray.Multibrot.Iterates =====
section Ray_Ray_Multibrot_Iterates
/-!
## Effective bounds on Multibrot iterates

We derive effective bounds and estimates for the growth rate of the Multibrot iteration
`z ← z^d + c`, for downstream use in theoretical results and numerical calculation.  Theoretical
results such as Multibrot connectness need only weak bounds, but numerical want them to be as tight
as possible, so we put significant effort towards tightening.  However, we strive for tightness only
when `d = 2`.  Effective bounds are continued in
`Ray.Multibrot.{Potential,Postcritical,Bottcher.lean`.

Our main result in this file is `iter_approx`, which shows that iterates grow as
`z^d^(n + o(1))` for large `z`.  Concretely, if if `3 ≤ b` and `max b (abs c) ≤ abs z`, then

  `|log (log (abs ((f' d c)^[n] z))) - log (log (abs z)) - n * log d| ≤` `k / (abs z * log (abs z))`

where `k` varies depending on `b` (see `iter_error_le_of_z3` and `iter_error_le_of_z4`).
-/

open Bornology (cobounded)
open Filter (Tendsto atTop)
open Real (exp log)
open Set
open scoped Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

-- We use large `norm_num`s in this file. Let them all through.
set_option exponentiation.threshold 10000

/-!
## Warmup bounds on iterates

Our iterations increase way faster than exponentially, but exponentials are nice for geometric
series bounds.
-/

/-- A warmup exponential lower bound on iterates, `3 ≤ abs z` version -/
lemma iter_large_z3 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    2^n * ‖z‖ ≤ ‖((f' d c)^[n] z)‖ := by
  rw [(by norm_num : (2:ℝ) = 3-1)]
  exact iter_large d 3 (by norm_num) z3 cz n

/-- A warmup exponential lower bound on iterates, `4 ≤ abs z` version -/
lemma iter_large_z4 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    3^n * ‖z‖ ≤ ‖((f' d c)^[n] z)‖ := by
  rw [(by norm_num : (3:ℝ) = 4-1)]
  exact iter_large d 4 (by norm_num) z4 cz n

/-- Iteration increases `abs z` -/
lemma le_self_iter (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    ‖z‖ ≤ ‖((f' d c)^[n] z)‖ := by
  refine le_trans ?_ (iter_large_z3 d z3 cz n)
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num))

/-- Iterates tend to infinity for large `z` -/
theorem tendsto_iter_cobounded (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) : Tendsto (fun n ↦ (f' d c)^[n] z) atTop (cobounded ℂ) := by
  simp only [tendsto_cobounded_iff_norm_tendsto_atTop]
  refine Filter.tendsto_atTop_mono (iter_large_z3 d z3 cz) ?_
  exact Filter.Tendsto.atTop_mul_const (by linarith) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Large iterates are `≠ 0` -/
lemma f_ne_zero {c z : ℂ} (cz : ‖c‖ ≤ ‖z‖) (z3 : 3 ≤ ‖z‖) : z^d + c ≠ 0 := by
  rw [← norm_ne_zero_iff]; apply ne_of_gt
  have z1 : 1 ≤ ‖z‖ := le_trans (by norm_num) z3
  calc ‖z ^ d + c‖
    _ ≥ ‖z ^ d‖ - ‖c‖ := by bound
    _ = ‖z‖ ^ d - ‖c‖ := by rw [norm_pow]
    _ ≥ ‖z‖ ^ 2 - ‖z‖ := by bound
    _ = ‖z‖ * (‖z‖ - 1) := by ring
    _ ≥ 3 * (3 - 1) := by bound
    _ > 0 := by norm_num

/-!
## Error bound functions

In the desire to be reasonably tight, our bounds are quite complicated.  We record them as functions
so that we can state the bounds simply.
-/

/-- Bounds on `log (abs z)` -/
lemma le_log_abs_z {z : ℂ} (z3 : 3 ≤ ‖z‖) : 1.0986 ≤ log (‖z‖) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  refine le_trans ?_ z3
  norm_num
  exact (exp_div_lt).le

/-- The inside of `f_error` is nonnegative -/
lemma f_error_inner_nonneg (d : ℕ) {z : ℂ} (z3 : 3 ≤ ‖z‖) :
    0 ≤ -log (1 - 1 / ‖z‖) / (d * log (‖z‖)) := by
  have z0 : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) z3
  have z0' : z ≠ 0 := by exact nnnorm_pos.mp z0
  have i1 : 1 / ‖z‖ ≤ 1 := by rw [one_div_le z0]; exact le_trans (by norm_num) z3; norm_num
  have s1 : 1 - 1 / ‖z‖ < 1 := by rw [tsub_lt_iff_tsub_lt]; norm_num; exact z0'; exact i1; rfl
  have l1 := le_log_abs_z z3
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (sub_nonneg.mpr i1) s1.le)) (by positivity)

/-- `0 ≤ f_error` for `3 ≤ abs z` -/
lemma f_error_nonneg {d : ℕ} [Fact (2 ≤ d)] {z : ℂ} (z3 : 3 ≤ ‖z‖) : 0 ≤ f_error d z := by
  rw [f_error, le_neg, neg_zero]
  have d0 : 0 < d := d_pos d
  have  l1 : 1 ≤ log ‖z‖ := le_trans (by norm_num) (le_log_abs_z z3)
  apply Real.log_nonpos
  · simp only [one_div, neg_div, sub_nonneg, neg_le]
    rw [le_div_iff₀ (by positivity), neg_one_mul, neg_le]
    trans 2
    · refine le_trans (neg_log_one_sub_le_linear (c := 2) (by positivity) (by norm_num) ?_) ?_
      · exact le_trans (inv_anti₀ (by positivity) z3) (by norm_num)
      · simp only [zero_lt_two, mul_le_iff_le_one_right]; apply inv_le_one_of_one_le₀; linarith
    · exact le_trans (by norm_num) (mul_le_mul (two_le_cast_d d) l1 zero_le_one (by positivity))
  · linarith [f_error_inner_nonneg d z3]

/-- `f_error` bound if `b ≤ abs z`, with tunable parameters to adjust for each `b`.
    To use, pick `b`, choose `l` accordingly, then `tune `s, t, c, g` in order to be small.  -/
lemma f_error_le_generic (d : ℕ) [Fact (2 ≤ d)] (b l s t c g : ℝ) {z : ℂ} (bz : b ≤ ‖z‖)
    (lb : exp l ≤ b)
    (b3 : 3 ≤ b := by norm_num)
    (st : s / b / (2 * l) ≤ t := by norm_num)
    (tc : t ≤ min 1 (((c - 1) * 2)⁻¹ + 1)⁻¹ := by norm_num)
    (bs : b⁻¹ ≤ min 1 (((s - 1) * 2)⁻¹ + 1)⁻¹ := by norm_num)
    (csg : 1 / 2 * c * s ≤ g := by norm_num)
    (l0 : 0 < l := by norm_num) (c1 : 1 < c := by norm_num) (s1 : 1 < s := by norm_num) :
     f_error d z ≤ g / (‖z‖ * log (‖z‖)) := by
  have z3 := le_trans b3 bz
  replace lb := (Real.le_log_iff_exp_le (by positivity)).mpr (le_trans lb bz)
  have l0' : 0 < log ‖z‖ := trans l0 lb
  have inner_le : -log (1 - 1 / ‖z‖) ≤ s / ‖z‖ := by
    rw [one_div, div_eq_mul_inv]
    apply neg_log_one_sub_le_linear (by positivity) s1
    exact le_trans (inv_anti₀ (by positivity) bz) bs
  have dm : 2 * log ‖z‖ ≤ d * log ‖z‖ := by bound
  have div_le : -log (1 - 1 / ‖z‖) / (d * log ‖z‖) ≤ t := by
    have sz : s / ‖z‖ ≤ s / b := div_le_div_of_nonneg_left (by positivity) (by positivity) bz
    exact le_trans (div_le_div₀ (by positivity) (le_trans inner_le sz) (by positivity)
      (le_trans (mul_le_mul_of_nonneg_left lb (by norm_num)) dm)) st
  refine le_trans (neg_log_one_sub_le_linear (f_error_inner_nonneg d z3) c1 ?_) ?_
  · exact le_trans div_le tc
  · refine le_trans (mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) inner_le
      (by positivity) dm) (by positivity)) ?_
    simp only [div_eq_mul_inv, ←mul_assoc, mul_inv, mul_comm _ (2⁻¹ : ℝ)]
    norm_num
    simp only [mul_assoc _ (‖z‖)⁻¹ _]
    exact mul_le_mul_of_nonneg_right csg (by positivity)

/-- `f_error` bound if `3 ≤ abs z` -/
lemma f_error_le_of_z3 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z3 : 3 ≤ ‖z‖) :
    f_error d z ≤ 0.699 / (‖z‖ * log (‖z‖)) := by
  refine f_error_le_generic d 3 1.0986 (s := 1.25) (t := 0.1897) (c := 1.1171) _ z3 ?_
  norm_num; exact (exp_div_lt).le

/-- `f_error` bound if `4 ≤ abs z` -/
lemma f_error_le_of_z4 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z4 : 4 ≤ ‖z‖) :
    f_error d z ≤ 0.619 / (‖z‖ * log ‖z‖) := by
  refine f_error_le_generic d (b := 4) (l := 1.3862) (s := 1.167) (t := 0.106) (c := 1.06)
    (g := _) z4 (lb := ?_) (b3 := by norm_num) (st := by norm_num) (tc := by norm_num)
    (bs := by norm_num) (csg := by norm_num) (l0 := by norm_num) (c1 := by norm_num)
  norm_num; exact (exp_div_lt).le

/-- `f_error` bound if `6 ≤ abs z` -/
lemma f_error_le_of_z6 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z6 : 6 ≤ ‖z‖) :
    f_error d z ≤ 0.565 / (‖z‖ * log ‖z‖) := by
  refine f_error_le_generic d (b := 6) (l := 1.791) (s := 1.1) (t := 0.0512) (c := 1.027)
    (g := _) z6 (lb := ?_) (b3 := by norm_num) (st := by norm_num) (tc := by norm_num)
    (bs := by norm_num) (csg := by norm_num) (l0 := by norm_num) (c1 := by norm_num)
  norm_num; exact (exp_div_lt).le

/-- `f_error` bound if `12 ≤ abs z` -/
lemma f_error_le_of_z12 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z12 : 12 ≤ ‖z‖) :
    f_error d z ≤ 0.528 / (‖z‖ * log ‖z‖) := by
  refine f_error_le_generic d (b := 12) (l := 2.48) (s := 1.046) (t := 0.0176) (c := 1.009)
    (g := _) z12 (lb := ?_) (b3 := by norm_num) (st := by norm_num) (tc := by norm_num)
    (bs := by norm_num) (csg := by norm_num) (l0 := by norm_num) (c1 := by norm_num)
  norm_num; exact (exp_div_lt).le

/-- `f_error` bound if `33 ≤ abs z` -/
lemma f_error_le_of_z33 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z33 : 33 ≤ ‖z‖) :
    f_error d z ≤ 0.512 / (‖z‖ * log ‖z‖) := by
  refine f_error_le_generic d (b := 33) (l := 3.49) (s := 1.02) (t := 0.0045) (c := 1.003)
    (g := _) z33 (lb := ?_) (b3 := by norm_num) (st := by norm_num) (tc := by norm_num)
    (bs := by norm_num) (csg := by norm_num) (l0 := by norm_num) (c1 := by norm_num)
  norm_num; exact (exp_div_lt).le

/-- `f_error` bound if `140 ≤ abs z` -/
lemma f_error_le_of_z140 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z140 : 140 ≤ ‖z‖) :
    f_error d z ≤ 0.5023 / (‖z‖ * log ‖z‖) := by
  refine f_error_le_generic d (b := 140) (l := 4.94) (s := 1.004) (t := 0.00073) (c := 1.0004)
    (g := _) z140 (lb := ?_) (b3 := by norm_num) (st := by norm_num) (tc := by norm_num)
    (bs := by norm_num) (csg := by norm_num) (l0 := by norm_num) (c1 := by norm_num)
  norm_num; exact (exp_div_lt).le

/-- Finite sums of `f_error` -/
def iter_error_sum (d : ℕ) (c z : ℂ) (N : Finset ℕ) :=
  N.sum (fun k ↦ f_error d ((f' d c)^[k] z))

/-- `0 ≤ iter_error` -/
lemma iter_error_nonneg (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    0 ≤ iter_error d c z :=
  tsum_nonneg (fun n ↦ f_error_nonneg (le_trans z3 (le_self_iter d z3 cz n)))

/-- Weak `iter_error_sum` bound based on geometric series -/
lemma iter_error_sum_weak (d : ℕ) [Fact (2 ≤ d)] {b s : ℝ} {c : ℂ} (b3 : 3 ≤ b) (s0 : 0 ≤ s)
    (bs : ∀ {w : ℂ}, b ≤ ‖w‖ → f_error d w ≤ s / (‖w‖ * log (‖w‖)))
    {z : ℂ} (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) {N : Finset ℕ} :
    iter_error_sum d c z N ≤ s / (1 - (b-1)⁻¹) / (‖z‖ * log (‖z‖)) := by
  have mf : ∀ k (w : ℂ), b ≤ ‖w‖ → ‖c‖ ≤ ‖w‖ → (b-1)^k * ‖w‖ ≤ ‖((f' d c)^[k] w)‖ :=
    fun k w bw cw ↦ iter_large d b (by linarith) bw cw k
  have z3 : 3 ≤ ‖z‖ := by linarith
  have l0 : 0 < log ‖z‖ := lt_of_lt_of_le (by norm_num) (le_log_abs_z z3)
  have b1 : 1 < b - 1 := by linarith
  have fb : ∀ k, f_error d ((f' d c)^[k] z) ≤ s / ((b-1)^k * ‖z‖ * log (‖z‖)) := by
    intro k
    have mk := mf k z bz cz
    have mk' : ‖z‖ ≤ ‖((f' d c)^[k] z)‖ :=
      le_trans (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ b1.le)) mk
    refine le_trans (bs (le_trans bz mk')) ?_
    refine div_le_div_of_nonneg_left s0 (by positivity) ?_
    exact mul_le_mul mk (Real.log_le_log (by positivity) mk') l0.le (by positivity)
  simp only [div_eq_mul_inv, ←mul_assoc, mul_inv, mul_comm _ ((b-1)^_)⁻¹,
    mul_comm _ (1-(b-1)⁻¹)⁻¹] at fb ⊢
  simp only [mul_assoc] at fb ⊢
  generalize ht : s * ((‖z‖)⁻¹ * (log (‖z‖))⁻¹) = t at fb
  have t0 : 0 ≤ t := by rw [←ht]; positivity
  apply le_trans (Finset.sum_le_sum (fun k _ ↦ fb k))
  simp only [mul_comm _ t, ←Finset.mul_sum, ←inv_pow] at fb ⊢
  exact mul_le_mul_of_nonneg_left (partial_geometric_bound _ (by positivity)
    (inv_lt_one_of_one_lt₀ b1)) t0

/-- `iter_error` converges -/
lemma iter_error_summable (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) : Summable (fun n ↦ f_error d ((f' d c)^[n] z)) := by
  apply summable_of_sum_le
  · intro n; exact f_error_nonneg (le_trans z3 (le_self_iter d z3 cz n))
  · intro N; exact iter_error_sum_weak d (le_refl _) (by norm_num) (f_error_le_of_z3 d) z3 cz

/-- Peel off the first step of the `iter_error` sum -/
lemma iter_error_peel {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖):
    iter_error d c z = f_error d z + iter_error d c (f' d c z) := by
  have h0 := sum_drop (iter_error_summable d z3 cz).hasSum
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq] at h0
  simp only [iter_error, h0.tsum_eq]; abel

/-- Weak `iter_error` bound based on geometric series -/
lemma iter_error_weak (d : ℕ) [Fact (2 ≤ d)] {b s : ℝ} {c : ℂ} (b3 : 3 ≤ b) (s0 : 0 ≤ s)
    (bs : ∀ {w : ℂ}, b ≤ ‖w‖ → f_error d w ≤ s / (‖w‖ * log (‖w‖)))
    {z : ℂ} (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    iter_error d c z ≤ s / (1 - (b-1)⁻¹) / (‖z‖ * log (‖z‖)) := by
  have z3 : 3 ≤ ‖z‖ := by linarith
  have l0 : 0 < log ‖z‖ := lt_of_lt_of_le (by norm_num) (le_log_abs_z z3)
  have b1 : 1 < b - 1 := by linarith
  have b0 : 0 ≤ 1 - (b - 1)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ b1.le)
  refine tsum_le_of_sum_le' ?_ ?_
  · positivity
  · intro N; exact iter_error_sum_weak d b3 s0 bs bz cz

/-- `iter_error_weak` for `33 ≤ abs z` (what you get from `3 ≤ abs z` after 2 iterations) -/
lemma iter_error_weak_of_z33 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z33 : 33 ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) : iter_error d c z ≤ 0.529 / (‖z‖ * log (‖z‖)) := by
  refine le_trans (iter_error_weak d (b := 33) (by norm_num) (by norm_num)
    (fun {_} bz ↦ f_error_le_of_z33 d bz) z33 cz) ?_
  have l0 : 0 < log ‖z‖ :=
    lt_of_lt_of_le (by norm_num) (le_log_abs_z (le_trans (by norm_num) z33))
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- Stronger `iter_error` bound based on expanding the first two terms -/
lemma iter_error_le (i : ℝ) {b s0 s1 s2 : ℝ} {c : ℂ} (b3 : 3 ≤ b)
    (s1p : 0 ≤ s1) (s2p : 0 ≤ s2)
    (bs0 : ∀ {w : ℂ}, b ≤ ‖w‖ → f_error d w ≤ s0 / (‖w‖ * log (‖w‖)))
    (bs1 : ∀ {w : ℂ}, (b^(d-1)-1)*b ≤ ‖w‖ → f_error d w ≤ s1 / (‖w‖ * log (‖w‖)))
    (bs2 : ∀ {w : ℂ}, ((b^(d-1)-1)^d * b^(d-1) - 1)*b ≤ ‖w‖ →
      f_error d w ≤ s2 / (‖w‖ * log (‖w‖)))
    (b11 : 11 ≤ (b^(d-1) - 1) ^ d * b^(d-1) - 1)
    (bb3 : 3 ≤ ((b^(d-1) - 1) ^ d * b^(d-1) - 1) * b)
    (b0' : 0 < b^(d-1) - 1)
    (b0'' : 0 < 1 - (((b^(d-1)-1)^d * b^(d-1) - 1) * b - 1)⁻¹)
    (si : s0 + s1 / (b ^ (d - 1) - 1) + s2 /
      ((1 - (((b^(d-1)-1)^d * b^(d-1) - 1) * b - 1)⁻¹) * ((b^(d-1)-1)^d * b^(d-1) - 1)) ≤ i)
    {z : ℂ} (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    iter_error d c z ≤ i / (‖z‖ * log (‖z‖)) := by
  have b0 : 0 < b := lt_of_lt_of_le (by norm_num) b3
  have z0 : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) (le_trans b3 bz)
  have z3 : 3 ≤ ‖z‖ := le_trans (by norm_num) (le_trans b3 bz)
  have l0 : 1 < log ‖z‖ := lt_of_lt_of_le (by norm_num) (le_log_abs_z z3)
  generalize hbb : (b^(d-1)-1)^d * b^(d-1) - 1 = bb at b11 bb3 bs2 b0'' si
  have fz : ‖z‖^d - ‖c‖ ≤ ‖f' d c z‖ := by
    calc ‖z^d + c‖
      _ ≥ ‖z^d‖ - ‖c‖ := by bound
      _ = ‖z‖^d - ‖c‖ := by rw [norm_pow]
  have fz' : (b^(d-1)-1) * ‖z‖ ≤ ‖f' d c z‖ := by
    calc ‖f' d c z‖
      _ ≥ ‖z‖^d - ‖c‖ := fz
      _ ≥ ‖z‖^d - ‖z‖ := by bound
      _ = ‖z‖^(d-1) * ‖z‖ - ‖z‖ := by rw [←pow_succ, Nat.sub_add_cancel (d_ge_one d)]
      _ = (‖z‖^(d-1) - 1) * ‖z‖ := by rw [sub_one_mul]
      _ ≥ (b^(d-1)-1) * ‖z‖ := by bound
  have zfz : ‖z‖ ≤ ‖f' d c z‖ := le_self_iter d z3 cz 1
  have zffz : ‖z‖ ≤ ‖f' d c (f' d c z)‖ := le_self_iter d z3 cz 2
  have bfz : b ≤ ‖f' d c z‖ := le_trans bz zfz
  have ffz : bb * ‖z‖ ≤ ‖f' d c (f' d c z)‖ := by
    calc ‖((f' d c z)^d + c)‖
      _ ≥ ‖(f' d c z)^d‖ - ‖c‖ := by bound
      _ = ‖f' d c z‖^d - ‖c‖ := by rw [norm_pow]
      _ ≥ ((b^(d-1)-1) * ‖z‖)^d - ‖z‖ := by bound
      _ = (b^(d-1)-1)^d * ‖z‖^(d-1) * ‖z‖ - ‖z‖ := by
          rw [mul_assoc, ←pow_succ, mul_pow, Nat.sub_add_cancel (d_ge_one d)]
      _ ≥ (b^(d-1)-1)^d * b^(d-1) * ‖z‖ - ‖z‖ := by bound
      _ = bb * ‖z‖ := by rw [←hbb, sub_one_mul]
  have e0 : f_error d z ≤ s0 / (‖z‖ * log (‖z‖)) := bs0 bz
  have e1 : f_error d (f' d c z) ≤ s1 / (b^(d-1)-1) / (‖z‖ * log (‖z‖)) := by
    refine le_trans (bs1 ?_) ?_
    · exact le_trans (mul_le_mul_of_nonneg_left bz b0'.le) fz'
    · simp only [div_eq_mul_inv, mul_inv, ←mul_assoc _ (‖z‖)⁻¹, mul_assoc s1 _ (‖z‖)⁻¹]
      simp only [←mul_inv, mul_assoc s1]
      refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) s1p
      exact mul_le_mul fz' (Real.log_le_log (by positivity) zfz) (by positivity)
        (le_trans b0.le bfz)
  have e2 : iter_error d c (f' d c (f' d c z)) ≤
      s2 / ((1 - (bb*b-1)⁻¹) * bb) / (‖z‖ * log (‖z‖)) := by
    refine le_trans (iter_error_weak d bb3 s2p bs2 ?_ (le_trans cz zffz)) ?_
    · exact le_trans (mul_le_mul_of_nonneg_left bz (by positivity)) ffz
    · simp only [div_eq_mul_inv, mul_assoc s2]
      refine mul_le_mul_of_nonneg_left ?_ s2p
      simp only [←mul_inv, ←mul_assoc]
      refine inv_anti₀ (by positivity) ?_
      refine mul_le_mul ?_ (Real.log_le_log z0 zffz) (by positivity) (by positivity)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ffz (by positivity)
  rw [iter_error_peel z3 cz, iter_error_peel (le_trans b3 bfz) (le_trans cz zfz), ←add_assoc]
  refine le_trans (add_le_add (add_le_add e0 e1) e2) ?_
  simp only [← add_div]
  exact div_le_div_of_nonneg_right si (by positivity)

/-- `iter_error_string` for `3 ≤ abs z` -/
lemma iter_error_le_of_z3 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    iter_error d c z ≤ 1.03 / (‖z‖ * log (‖z‖)) := by
  have b3 : (3:ℝ) ≤ 3^(d-1) := by
    calc (3:ℝ)^(d-1)
      _ ≥ 3^(2-1) := by bound
      _ = 3 := by norm_num
  generalize hb3 : (3:ℝ)^(d-1) = t3 at b3
  have b2 : (2:ℝ) ≤ t3 - 1 := by linarith
  generalize hb2 : t3 - 1 = t2 at b2
  have t2p : 0 ≤ t2 := by positivity
  have b6 : (6:ℝ) ≤ t2 * 3 := by linarith
  have b11 : (11:ℝ) ≤ t2^d * t3 - 1 := by
    calc t2^d * t3 - 1
      _ ≥ 2^d * 3 - 1 := by bound
      _ ≥ 2^2 * 3 - 1 := by bound
      _ = 11 := by norm_num
  generalize hb11 : t2^d * t3 - 1 = t11 at b11
  have b33 : (33:ℝ) ≤ t11 * 3 := by linarith
  generalize hb33 : t11 * 3 = t33 at b33
  have b10 : 10.65 ≤ (1 - (t33 - 1)⁻¹) * t11 := by
    have h : 1 ≤ t33 - 1 := by linarith
    calc (1 - (t33 - 1)⁻¹) * t11
      _ ≥ (1 - (33 - 1)⁻¹) * 11 := by bound
      _ ≥ 10.65 := by norm_num
  simp only [←hb2, ←hb3, ←hb11, ←hb33] at b2 b6 b11 b33
  refine iter_error_le _ (by norm_num) (by norm_num) (by norm_num)
    (bs0 := f_error_le_of_z3 d)
    (bs1 := fun {_} bz ↦ f_error_le_of_z6 d (le_trans b6 bz))
    (bs2 := fun {_} bz ↦ f_error_le_of_z33 d (le_trans b33 bz))
    b11 (le_trans (by norm_num) b33) (by positivity) ?_ ?_ z3 cz
  · exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
  · simp only [hb2, hb3, hb11, hb33] at b2 b3 b6 b11 b33 ⊢
    exact le_trans (add_le_add (add_le_add_right
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) b2) _)
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) b10)) (by norm_num)

/-- `iter_error_string` for `4 ≤ abs z` -/
lemma iter_error_le_of_z4 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    iter_error d c z ≤ 0.8095 / (‖z‖ * log (‖z‖)) := by
  have b3 : (4:ℝ) ≤ 4^(d-1) := by
    calc (4:ℝ)^(d-1)
      _ ≥ 4^(2-1) := by bound
      _ = 4 := by norm_num
  generalize hb3 : (4:ℝ)^(d-1) = t3 at b3
  have b2 : (3:ℝ) ≤ t3 - 1 := by linarith
  generalize hb2 : t3 - 1 = t2 at b2
  have t2p : 0 ≤ t2 := by positivity
  have b6 : (12:ℝ) ≤ t2 * 4 := by linarith
  have b11 : (35:ℝ) ≤ t2^d * t3 - 1 := by
    calc t2^d * t3 - 1
      _ ≥ 3^d * 4 - 1 := by bound
      _ ≥ 3^2 * 4 - 1 := by bound
      _ = 35 := by norm_num
  generalize hb11 : t2^d * t3 - 1 = t11 at b11
  have b33 : (140:ℝ) ≤ t11 * 4 := by linarith
  generalize hb33 : t11 * 4 = t33 at b33
  have b10 : 34.748 ≤ (1 - (t33 - 1)⁻¹) * t11 := by
    have h : 1 ≤ t33 - 1 := by linarith
    calc (1 - (t33 - 1)⁻¹) * t11
      _ ≥ (1 - (140 - 1)⁻¹) * 35 := by bound
      _ ≥ 34.748 := by norm_num
  simp only [←hb2, ←hb3, ←hb11, ←hb33] at b2 b6 b11 b33
  refine iter_error_le _ (by norm_num) (by norm_num) (by norm_num)
    (bs0 := f_error_le_of_z4 d)
    (bs1 := fun {_} bz ↦ f_error_le_of_z12 d (le_trans b6 bz))
    (bs2 := fun {_} bz ↦ f_error_le_of_z140 d (le_trans b33 bz))
    (le_trans (by norm_num) b11) (le_trans (by norm_num) b33) (by positivity) ?_ ?_ z4 cz
  · exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
  · simp only [hb2, hb3, hb11, hb33] at b2 b3 b6 b11 b33 ⊢
    exact le_trans (add_le_add (add_le_add_right
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) b2) _)
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) b10)) (by norm_num)

/-!
## Effective bounds on iterates
-/

/-- The approximate change of `log (log (abs z))` across one iterate -/
theorem f_approx {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    |log (log (‖z ^ d + c‖)) - log (log (‖z‖)) - log d| ≤ f_error d z := by
  have dp : 0 < d := d_pos d
  have d2 : 2 ≤ (d : ℝ) := two_le_cast_d d
  have z1' : 1 < ‖z‖ := lt_of_lt_of_le (by norm_num) z3
  have z0' : 0 < ‖z‖ := by positivity
  have iz1 : 1 / ‖z‖ < 1 := (div_lt_one z0').mpr z1'
  have z0 : z ≠ 0 := norm_ne_zero_iff.mp (by positivity)
  have cz_le : ‖c / z^d‖ ≤ 1 / ‖z‖ := by
    have d1 : z^d = z^(d - 1 + 1) := by rw [Nat.sub_add_cancel (d_ge_one d)]
    simp only [d1, norm_div, norm_pow, pow_succ', div_mul_eq_div_div]
    bound
  have l0s : 1 ≤ log ‖z‖ := by
    rw [Real.le_log_iff_exp_le z0']; exact le_trans Real.exp_one_lt_3.le z3
  have l0 : 0 < log ‖z‖ := by positivity
  have l1 : 0 < ↑d * log ‖z‖ := by positivity
  have l1' : 1 < log ‖z‖ := by
    rw [Real.lt_log_iff_exp_lt z0']; exact lt_of_lt_of_le Real.exp_one_lt_3 z3
  have l2 : |log (‖1 + c / z ^ d‖)| ≤ -log (1 - 1 / ‖z‖) := by
    nth_rw 1 [← Complex.log_re]
    apply le_trans (Complex.abs_re_le_norm _)
    apply le_trans (Complex.norm_log_one_add_le' (trans cz_le iz1))
    exact Real.neg_log_one_sub_mono cz_le iz1
  have dl2 : 2 < d * log ‖z‖ := by
    calc ↑d * log ‖z‖
      _ ≥ 2 * log ‖z‖ := by gcongr
      _ > 2 * 1 := by gcongr
      _ = 2 := by norm_num
  have l3 : 0 < ↑d * log ‖z‖ + log ‖1 + c / z ^ d‖ := by
    have i2 : 1/‖z‖ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    suffices h : -log ‖1 + c / z ^ d‖ < ↑d * log ‖z‖ by linarith
    apply lt_of_le_of_lt (neg_le_neg_iff.mpr (abs_le.mp l2).1); simp only [neg_neg]
    exact lt_of_le_of_lt (neg_log_one_sub_le_two i2) dl2
  rw [log_abs_add (z ^ d) c (pow_ne_zero _ z0) (f_ne_zero cz z3), norm_pow, Real.log_pow,
    log_add _ _ l1 l3, Real.log_mul (Nat.cast_ne_zero.mpr (d_ne_zero d)) l0.ne']
  generalize hu : log (‖1 + c / z ^ d‖) / (d * log ‖z‖) = u
  ring_nf
  have inner : |u| ≤ -log (1 - 1/‖z‖) / (d * log ‖z‖) := by
    simp only [← hu, abs_div, abs_of_pos l1, div_le_iff₀ l1]
    apply le_trans l2; apply le_of_eq; field_simp
  have weak : -log (1 - 1/‖z‖) / (d * log ‖z‖) < 1 := by
    rw [div_lt_one l1]
    refine lt_of_le_of_lt (neg_log_one_sub_le_two ?_) dl2
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  apply le_trans (Real.abs_log_one_add_le (trans inner weak))
  apply le_trans (Real.neg_log_one_sub_mono inner weak)
  rw [f_error]

/-- Absolute values of iterates grow roughly as `z^d^n` for large `z` -/
theorem iter_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖)
    (n : ℕ) : |log (log (‖(f' d c)^[n] z‖)) - log (log (‖z‖)) - n * log d| ≤ iter_error d c z := by
  induction' n with n h generalizing z
  · simp only [Function.iterate_zero, id_eq, sub_self, CharP.cast_eq_zero, zero_mul, abs_zero,
    iter_error_nonneg d z3 cz]
  · simp only [Function.iterate_succ_apply, Nat.cast_add_one]
    have e : log (log (‖(f' d c)^[n] (f' d c z)‖)) - log (log (‖z‖)) - (n+1) * log d =
        (log (log (‖f' d c z‖)) - log (log (‖z‖)) - log d) +
        (log (log (‖(f' d c)^[n] (f' d c z)‖)) - log (log (‖f' d c z‖)) - n * log d) := by
      ring
    rw [e, iter_error_peel z3 cz]
    have le : ‖z‖ ≤ ‖f' d c z‖ := le_self_iter d z3 cz 1
    exact le_trans (abs_add_le _ _) (add_le_add (f_approx z3 cz)
      (h (le_trans z3 le) (le_trans cz le)))

end
end Ray_Ray_Multibrot_Iterates

-- ===== Ray.Multibrot.Potential =====
section Ray_Ray_Multibrot_Potential
/-!
## Effective bounds on the Multibrot `potential` function

We derive effective estimates for `log (-log potential)` and `potential`, building only
the iterate growth rate estimates in `Iterates.lean`:

1. `log (-log (s.potential c z)) = log (log (abs z)) + O(1) / (abs z * log (abs z))`
2. `s.potential c z = 1/abs z + O(1) / abs z ^ k`, where `k = 1.864` if `4 ≤ abs z` and
   `k = 1.927` if `6 ≤ abs z`.
-/

open Filter (Tendsto atTop)
open Metric (ball mem_ball_self mem_ball)
open Real (exp log)
open Set
open scoped Topology
noncomputable section

variable {c z : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

-- We use large `norm_num`s in this file. Let them all through.
set_option exponentiation.threshold 10000

/-!
## `potential` is the limit of roots of iterates
-/

/-- `potential` is the limit of roots of iterates -/
lemma tendsto_potential (d : ℕ) [Fact (2 ≤ d)] (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    Tendsto (fun n ↦ ‖(f' d c)^[n] z‖ ^ (-((d ^ n : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 ((superF d).potential c z)) := by
  set s := superF d
  suffices h : Tendsto (fun n ↦ (‖(f' d c)^[n] z‖ *
      s.potential c ↑((f' d c)^[n] z)) ^ (-((d ^ n : ℕ) : ℝ)⁻¹))
      atTop (𝓝 1) by
    replace h := h.mul_const (s.potential c z)
    simp only [div_mul_cancel₀ _ potential_pos.ne', one_mul, ← f_f'_iter, s.potential_eqn_iter,
      Real.mul_rpow (norm_nonneg _) (pow_nonneg s.potential_nonneg _),
      Real.pow_rpow_inv_natCast s.potential_nonneg (pow_ne_zero _ (d_ne_zero d)),
      Real.rpow_neg (pow_nonneg s.potential_nonneg _), ← div_eq_mul_inv] at h
    exact h
  simp only [← s.norm_bottcher, ← norm_mul, mul_comm _ (s.bottcher _ _)]
  rw [Metric.tendsto_atTop]; intro r rp
  rcases Metric.tendsto_atTop.mp ((bottcher_large_approx d c).comp (tendsto_iter_cobounded d z3 cz))
      (min (1 / 2) (r / 4)) (by bound) with ⟨n, h⟩
  use n; intro k nk; specialize h k nk
  generalize hw : (f' d c)^[k] z = w; generalize hp : s.bottcher c w * w = p
  simp only [hw, hp, Function.comp, Complex.dist_eq, Real.dist_eq] at h ⊢
  clear hp w hw nk n s cz z3
  generalize ha : ‖p‖ = a
  generalize hb : ((d ^ k : ℕ) : ℝ)⁻¹ = b
  have a1 : |a - 1| < min (1 / 2) (r / 4) := by
    rw [← ha]; refine lt_of_le_of_lt ?_ h
    rw [← norm_one (α := ℂ)]
    apply abs_norm_sub_norm_le
  have am : a ∈ ball (1 : ℝ) (1 / 2) := by
    simp only [mem_ball, Real.dist_eq]; exact (lt_min_iff.mp a1).1
  have b0 : 0 ≤ b := by rw [← hb]; bound
  have b1 : b ≤ 1 := by rw [← hb]; bound
  have hd : ∀ x, x ∈ ball (1 : ℝ) (1 / 2) →
      HasDerivAt (fun x ↦ x ^ (-b)) (1 * -b * x ^ (-b - 1) + 0 * x ^ (-b) * log x) x := by
    intro x m; apply HasDerivAt.rpow (hasDerivAt_id _) (hasDerivAt_const _ _)
    simp only [mem_ball, Real.dist_eq, id] at m ⊢; linarith [abs_lt.mp m]
  simp only [MulZeroClass.zero_mul, add_zero, one_mul] at hd
  have bound : ∀ x, x ∈ ball (1 : ℝ) (1 / 2) → ‖deriv (fun x ↦ x ^ (-b)) x‖ ≤ 4 := by
    intro x m
    simp only [(hd x m).deriv, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg b0]
    simp only [mem_ball, Real.dist_eq, abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add] at m
    norm_num at m
    have x0 : 0 < x := by linarith
    calc b * |x ^ (-b - 1)|
      _ ≤ 1 * |x| ^ (-b - 1) := by bound
      _ = (x ^ (b + 1))⁻¹ := by rw [← Real.rpow_neg x0.le, neg_add', one_mul, abs_of_pos x0]
      _ ≤ ((1 / 2 : ℝ) ^ (b + 1))⁻¹ := by bound
      _ = 2 ^ (b + 1) := by rw [one_div, Real.inv_rpow zero_le_two, inv_inv]
      _ ≤ 2 ^ (1 + 1 : ℝ) := by bound
      _ ≤ 4 := by norm_num
  have le := Convex.norm_image_sub_le_of_norm_deriv_le (fun x m ↦ (hd x m).differentiableAt) bound
      (convex_ball _ _) (mem_ball_self (by norm_num)) am
  simp only [Real.norm_eq_abs, Real.one_rpow] at le
  calc |a ^ (-b) - 1|
    _ ≤ 4 * |a - 1| := le
    _ < 4 * (r / 4) := by linarith [(lt_min_iff.mp a1).2]
    _ = r := by ring

/-- `log (-log potential)` is the limit of roots of iterates -/
lemma tendsto_log_neg_log_potential (d : ℕ) [Fact (2 ≤ d)] (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    Tendsto (fun n ↦ log (log (‖(f' d c)^[n] z‖)) - n * log d) atTop
      (𝓝 (log (-log ((superF d).potential c z)))) := by
  set s := superF d
  have zn1 : ∀ {n}, 1 < ‖(f' d c)^[n] z‖ := by
    intro n; exact lt_of_lt_of_le (by norm_num) (le_trans z3 (le_self_iter d z3 cz _))
  have zn0 : ∀ {n}, 0 < ‖(f' d c)^[n] z‖ := fun {_} ↦ lt_trans zero_lt_one zn1
  have ln0 : ∀ {n}, 0 < log (‖(f' d c)^[n] z‖) := fun {_} ↦ Real.log_pos zn1
  have dn0 : ∀ {n}, (d:ℝ)^n ≠ 0 := fun {_} ↦ pow_ne_zero _ (Nat.cast_ne_zero.mpr (d_ne_zero d))
  have p0 : 0 < s.potential c z := potential_pos
  have p1 : s.potential c z < 1 := potential_lt_one_of_two_lt (by linarith) cz
  set f := fun x ↦ log (log x⁻¹)
  have fc : ContinuousAt f ((superF d).potential c z) := by
    refine ((NormedField.continuousAt_inv.mpr p0.ne').log (inv_ne_zero p0.ne')).log ?_
    exact Real.log_ne_zero_of_pos_of_ne_one (inv_pos.mpr p0) (inv_ne_one.mpr p1.ne)
  have t := Tendsto.comp fc (tendsto_potential d z3 cz)
  simpa only [Real.log_inv, Real.log_neg_eq_log, Nat.cast_pow, Function.comp_def, Real.log_rpow zn0,
    neg_mul, ← div_eq_inv_mul, Real.log_div ln0.ne' dn0, Real.log_pow, f] using t

/-- `log (-log potential)` inherits the `iter_approx` bound by taking limits -/
lemma log_neg_log_potential_approx (d : ℕ) [Fact (2 ≤ d)] (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    |log (-log ((superF d).potential c z)) - log (log (‖z‖))| ≤ iter_error d c z := by
  apply le_of_forall_pos_lt_add; intro e ep
  rcases (Metric.tendsto_nhds.mp (tendsto_log_neg_log_potential d z3 cz) e ep).exists with ⟨n,t⟩
  have ie := iter_approx d z3 cz n
  generalize log (-log ((superF d).potential c z)) = p at ie t
  generalize log (log ‖(f' d c)^[n] z‖) = x at ie t
  generalize log (log ‖z‖) = y at ie t
  rw [Real.dist_eq, abs_sub_comm] at t
  rw [add_comm]
  calc |p - y|
      _ = |(p - (x - n * log d)) + (x - y - n * log d)| := by ring_nf
      _ ≤ |p - (x - n * log d)| + |x - y - n * log d| := abs_add_le _ _
      _ < e + _ := add_lt_add_of_lt_of_le t ie

/-!
### We use `ene x = exp (-exp x)` below for Lipschitz bounds

This undoes the `log (log (abs z))` from `iter_approx`.
-/

/-- `d ene / dx = dene` -/
lemma hasDerivAt_ene (x : ℝ) : HasDerivAt ene (-dene x) x := by
  have h : HasDerivAt (fun x ↦ exp (-exp x)) (exp (-exp x) * -exp x) x :=
    HasDerivAt.exp (Real.hasDerivAt_exp x).neg
  simp only [mul_neg, ← Real.exp_add, neg_add_eq_sub] at h; exact h

/-- `d ene / dx = dene` -/
lemma deriv_ene (x : ℝ) : deriv ene x = -dene x := (hasDerivAt_ene x).deriv

/-- `0 ≤ dene x` -/
lemma dene_nonneg {x : ℝ} : 0 ≤ dene x := Real.exp_nonneg _

/-- `dene x` is decreasing for positive `x` -/
lemma dene_anti {x y : ℝ} (x0 : 0 ≤ x) (xy : x ≤ y) : dene x ≥ dene y := by
  refine Real.exp_le_exp.mpr ?_
  have a : AntitoneOn (fun x ↦ x - exp x) (Ici 0) := by
    have hd : ∀ x, HasDerivAt (fun x ↦ x - exp x) (1 - exp x) x :=
      fun x ↦ (hasDerivAt_id x).sub (Real.hasDerivAt_exp x)
    have d : Differentiable ℝ (fun x ↦ x - exp x) := fun x ↦ (hd x).differentiableAt
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact d.continuous.continuousOn
    · exact d.differentiableOn
    · intro x m; simp only [nonempty_Iio, interior_Ici', mem_Ioi] at m
      simp only [(hd x).deriv, sub_nonpos, Real.one_le_exp m.le]
  exact a x0 (le_trans x0 xy) xy

/-- Below we evaluate `dene x = -exp (-exp x)` at a point of the form `log (log (abs z)) - k`.
    The derivative simplifies in this case. -/
lemma dene_eq {z : ℝ} (z1 : 1 < z) (k : ℝ) :
    dene (log (log z) - k) = exp (-k) * log z * z ^ (-exp (-k)) := by
  have l0 : 0 < log z := Real.log_pos z1
  simp only [dene, sub_eq_add_neg, Real.exp_add, Real.exp_log l0, mul_comm _ (exp (-k)), ←neg_mul]
  apply congr_arg₂ _ rfl
  rw [mul_comm, Real.exp_mul, Real.exp_log (by positivity)]

/-!
## Effective bounds on `potential`
-/

/-- Generic `potential_error` bound for any `b ≤ abs z` lower bound -/
lemma potential_error_le (d : ℕ) [Fact (2 ≤ d)] {b : ℝ} {c z : ℂ}
    (b4 : 4 ≤ b) (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    potential_error d c z ≤ 0.8095 / ‖z‖ ^ (1 + exp (-0.8095 / (‖z‖ * log (‖z‖)))) := by
  have z1 : 1 < ‖z‖ := by linarith
  have z4 : 4 ≤ ‖z‖ := by linarith
  have l1 : 1.386 < log ‖z‖ := lt_of_lt_of_le lt_log_4 (Real.log_le_log (by linarith) z4)
  have l0 : 0 < log ‖z‖ := lt_trans (by norm_num) l1
  simp only [potential_error, dene_eq z1]
  have ie := iter_error_le_of_z4 d z4 cz
  have ie0 := iter_error_nonneg d (by linarith) cz
  generalize hk : (0.8095 : ℝ) = k at ie
  have k0 : 0 < k := by rw [← hk]; norm_num
  generalize hx : ‖z‖ = x at ie z1 l0 l1 z4
  generalize iter_error d c z = i at ie ie0
  have x0 : 0 < x := by rw [←hx]; linarith
  refine le_trans (mul_le_mul_of_nonneg_left ie (by positivity)) ?_
  simp only [←mul_assoc, div_eq_inv_mul, mul_inv, mul_comm _ (log x)]
  simp only [←mul_assoc, mul_comm _ (log x)⁻¹, inv_mul_cancel₀ l0.ne', one_mul]
  simp only [mul_assoc]
  refine le_trans (mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr (by linarith))) ?_
  simp only [←mul_assoc, ←Real.rpow_neg_one x, ←Real.rpow_add (lt_trans zero_lt_one z1),
    ←Real.rpow_neg x0.le]
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le z1.le ?_) k0.le
  simp only [Real.rpow_neg_one, mul_neg, neg_add_rev, le_add_neg_iff_add_le, neg_add_cancel_right,
    neg_le_neg_iff, Real.exp_le_exp, ←mul_inv, ←div_eq_inv_mul k, mul_comm _ x, ie]

/-- Helper for specifix `b` `potential_error` bounds.  Python formulas are:
      `i = 1 + np.exp(-0.8095 / (b * np.log(b)))  -- round down`
      `j = 0.8095 / (b * np.log(b))  -- round up` -/
lemma potential_error_le' (d : ℕ) [Fact (2 ≤ d)] (i j b : ℝ) {c z : ℂ}
    (b4 : 4 ≤ b) (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖)
    (j0 : 0 < j) (ij : i - 1 ≤ exp (-j)) (bj : exp (0.8095 / b / j) ≤ b) :
    potential_error d c z ≤ 0.8095 / ‖z‖ ^ i := by
  have z0 : 0 < ‖z‖ := by linarith
  have l1 : 1.386 < log ‖z‖ :=
    lt_of_lt_of_le lt_log_4 (Real.log_le_log (by linarith) (by linarith))
  have l0 : 0 < log ‖z‖ := lt_trans (by norm_num) l1
  refine le_trans (potential_error_le d b4 bz cz) (div_le_div_of_nonneg_left (by norm_num)
    (by positivity) ?_)
  refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
  simp only [add_comm (1:ℝ), ←sub_le_iff_le_add]
  refine le_trans ij (Real.exp_le_exp.mpr ?_)
  simp only [neg_div, neg_le_neg_iff, div_mul_eq_div_div]
  rw [div_le_iff₀ l0, mul_comm j, ←div_le_iff₀ j0]
  trans 0.8095 / b / j
  · gcongr
  · rw [Real.le_log_iff_exp_le z0]
    exact le_trans bj bz

/-- `potential_error` bound for `4 ≤ abs z` -/
lemma potential_error_le_of_z4 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ}
    (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    potential_error d c z ≤ 0.8095 / ‖z‖ ^ (1.864 : ℝ) := by
  apply potential_error_le' d _ (j := 0.146) (b := 4) (by norm_num) z4 cz (by norm_num)
  · norm_num; exact (lt_exp_neg_div).le
  · norm_num; exact (exp_div_lt).le

/-- `potential_error` bound for `6 ≤ abs z` -/
lemma potential_error_le_of_z6 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ}
    (z6 : 6 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    potential_error d c z ≤ 0.8095 / ‖z‖ ^ (1.927 : ℝ) := by
  apply potential_error_le' d _ (j := 0.0753) (b := 6) (by norm_num) z6 cz (by norm_num)
  · norm_num; exact (lt_exp_neg_div).le
  · norm_num; exact (exp_div_lt).le

/-- We need `iter_error d c z ≤ log (log (abs z))` below to make `dene` monotonic -/
lemma iter_error_le_log_log_abs (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z4 : 4 ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) : iter_error d c z ≤ log (log ‖z‖) := by
  have hl : 1.38 ≤ log ‖z‖ := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    norm_num
    exact le_trans (exp_div_lt).le z4
  have hll : 0.32 ≤ log (log ‖z‖) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    norm_num
    exact le_trans (exp_div_lt).le hl
  refine le_trans ?_ hll
  apply le_trans (iter_error_le_of_z4 d z4 cz)
  rw [div_le_iff₀' (by positivity), ←div_le_iff₀ (by norm_num)]
  refine le_trans (by norm_num) (mul_le_mul z4 hl (by positivity) (by positivity))

/-- `s.potential ≈ ‖z‖⁻¹` -/
theorem potential_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    |(superF d).potential c z - 1 / ‖z‖| ≤ potential_error d c z := by
  set s := superF d
  have z3 : 3 ≤ ‖z‖ := le_trans (by norm_num) z4
  have z0 : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) z3
  have l2 : 0 < log ‖z‖ := Real.log_pos (by linarith)
  have h := log_neg_log_potential_approx d z3 cz
  have p0 : 0 < s.potential c z := potential_pos
  have lp0 : 0 < -log (s.potential c z) :=
    neg_pos.mpr (Real.log_neg p0 (potential_lt_one_of_two_lt (by linarith) cz))
  generalize s.potential c z = p at h p0 lp0
  generalize hr : iter_error d c z = r at h
  have r0 : 0 ≤ r := le_trans (abs_nonneg _) h
  set t := Ici (log (log ‖z‖) - r)
  have yt : log (-log p) ∈ t := by
    simp only [abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right, add_comm r] at h
    simp only [mem_Ici, tsub_le_iff_right, h, t]
  have lt : log (log ‖z‖) ∈ t := by
    simp only [mem_Ici, tsub_le_iff_right, le_add_iff_nonneg_right, r0, t]
  generalize hb : dene (log (log ‖z‖) - r) = b
  have b0 : 0 ≤ b := by rw [←hb]; exact dene_nonneg
  have bound : ∀ x, x ∈ t → ‖deriv ene x‖ ≤ b := by
    intro x m
    simp only [mem_Ici, ← hr, t] at m
    simp only [deriv_ene, norm_neg, Real.norm_of_nonneg dene_nonneg, ←hb, ←hr]
    apply dene_anti (sub_nonneg.mpr (iter_error_le_log_log_abs d z4 cz)) m
  have m := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ ↦ (hasDerivAt_ene x).differentiableAt) bound (convex_Ici _) lt yt
  simp only [Real.norm_eq_abs] at m
  replace m := le_trans m (mul_le_mul_of_nonneg_left h (by bound))
  simp only [ene, Real.exp_log lp0, neg_neg, Real.exp_log p0, Real.exp_log l2, Real.exp_neg,
    Real.exp_log z0, inv_eq_one_div] at m
  refine le_trans m (le_of_eq ?_)
  simp only [←hr, ←hb, potential_error]

end
end Ray_Ray_Multibrot_Potential

-- ===== Ray.Multibrot.PotentialLower =====
section Ray_Ray_Multibrot_PotentialLower
/-!
## A lower bounds `potential c z` for small `z`

`potential_approx` in `Dynamics.Multibrot.Potential` gives an effective estimate on
`s.potential c z` for `max 4 ‖c‖ ≤ ‖z‖`.  However, for rendering we also need an effective
lower bound for small `z`, in order to show that iterations which stay bounded have potential
near `1`.  We do this by noting that if `‖c‖, ‖z‖ ≤ 4`, then iteration must eventually pass
through the interval `‖w‖ ∈ [4,4^d+4]`.  On this interval, we have the estimate

  `potential c w ≥ 1/‖w‖ - 0.8095 / ‖w‖ ^ 1.864 ≥ 0.0469`
  `potential c z ≥ potential c w ^ d⁻¹ ≥ 0.216`

Note that if `z` is the result of at least 10 iterations, we then know that the potential of the
intial `z` is at least `1 - 1/512`.
-/

open Classical
open Real (log)
open Set

variable {c z : ℂ}
variable {d : ℕ} [Fact (2 ≤ d)]

/-- Small iterates eventually pass through `‖z‖ ∈ (4, 4 ^ d + 4]` -/
lemma pass_through (c4 : ‖c‖ ≤ 4) (z4 : ‖z‖ ≤ 4) (m : (c,↑z) ∈ (superF d).basin) :
    ∃ n, ‖(f' d c)^[n+1] z‖ ∈ Ioc 4 (4 ^ d + 4) := by
  set s := superF d
  simp only [s.basin_iff_attracts, Attracts, RiemannSphere.tendsto_inf_iff_tendsto_cobounded,
    f_f'_iter, tendsto_cobounded_iff_norm_tendsto_atTop] at m
  rcases Filter.tendsto_atTop_atTop.mp m 5 with ⟨n,h⟩
  generalize hp : (fun n ↦ 4 < ‖(f' d c)^[n] z‖) = p
  replace h : p n := by rw [←hp]; linarith [h n (by linarith)]
  generalize hk : Nat.find (p := p) ⟨_,h⟩ = k
  have k4 : p k := by rw [←hk]; exact Nat.find_spec (p := p) ⟨_,h⟩
  have k0 : k ≠ 0 := by
    contrapose k4
    simp only [k4, ← hp, not_lt, Function.iterate_zero_apply, z4]
  have k1 : 1 ≤ k := Nat.pos_iff_ne_zero.mpr k0
  use k-1
  have lt : ¬p (k-1) := by apply Nat.find_min; rw [hk]; omega
  simp only [Nat.sub_add_cancel k1, ←hp, not_lt] at k4 k1 lt ⊢
  use k4
  have fs := iter_small d c ((f' d c)^[k-1] z)
  simp only [← Function.iterate_succ_apply', Nat.succ_eq_add_one, Nat.sub_add_cancel k1] at fs
  exact le_trans fs (by bound)

/-- Our lower bound is decreasing in `‖z‖` -/
lemma lower_anti (k p : ℝ) (kp : k * p ≤ 2 := by norm_num) (hp : 3/2 ≤ p := by norm_num) :
    AntitoneOn (fun x : ℝ ↦ 1 / x - k / x^p) (Ici 4) := by
  have hd : ∀ x, 4 ≤ x → HasDerivAt (fun x : ℝ ↦ 1 / x - k / x^p)
      (-(x^2)⁻¹ - k * (-(p * x^(p-1)) / (x^p)^2)) x := by
    intro x x2
    simp only [div_eq_mul_inv, one_mul]
    refine (hasDerivAt_inv (by positivity)).sub (HasDerivAt.const_mul _ ?_)
    exact (Real.hasDerivAt_rpow_const (Or.inl (by positivity))).inv (by positivity)
  have d : DifferentiableOn ℝ (fun x ↦ 1 / x - k / x^p) (Ici 4) :=
    fun x m ↦ (hd x m).differentiableAt.differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact d.continuousOn
  · exact d.mono interior_subset
  · intro x x4
    simp only [nonempty_Iio, interior_Ici', mem_Ioi] at x4
    have x0 : 0 < x := by linarith
    simp only [(hd x x4.le).deriv]
    simp only [← Real.rpow_mul x0.le, neg_div, mul_div_assoc p, ← Real.rpow_sub x0, mul_neg, ←
      mul_assoc k p, sub_neg_eq_add, neg_add_le_iff_le_add, add_zero, ← Real.rpow_two, ←
      Real.rpow_neg x0.le]
    ring_nf
    simp only [←neg_add', Real.rpow_neg x0.le (1 + p)]
    rw [mul_inv_le_iff₀ (by positivity), ← Real.rpow_add x0]
    ring_nf
    have p1' : 1/2 ≤ -1 + p := by linarith
    refine le_trans kp (le_trans ?_ (Real.rpow_le_rpow_of_exponent_le (by linarith) p1'))
    rw [one_div, Real.le_rpow_inv_iff_of_pos (by norm_num) x0.le (by norm_num)]
    norm_num; exact x4.le

/-- A bound we need below -/
lemma le_of_d3 {d : ℕ} (d3 : 3 ≤ d) :
    (0.216 : ℝ) ^ d ≤ (4 ^ d + 4)⁻¹ - 0.8095 / (4 ^ d + 4) ^ (1.864 : ℝ) := by
  have e : (0.216 * 4 : ℝ) = 0.864 := by norm_num
  rw [le_sub_iff_add_le, ← one_div, le_div_iff₀ (by apply add_pos <;> bound), add_mul, mul_add,
    ← mul_pow, e, mul_comm _ (4 : ℝ), div_mul, ← Real.rpow_sub_one (by positivity)]
  have le : 38 ≤ (68 : ℝ) ^ (108 / 125 : ℝ) := by
    rw [div_eq_mul_inv, Real.rpow_mul (by positivity), Real.le_rpow_inv_iff_of_pos (by norm_num)
      (by positivity) (by positivity)]
    norm_num
  trans 0.864 ^ 3 + 4 * 0.216 ^ 3 + 0.8095 / (4 ^ 3 + 4) ^ (1.864 - 1 : ℝ)
  · bound
  · norm_num
    grw [← le]
    norm_num

/-- If `‖c‖, ‖z‖ ≤ 4`, `0.216 ≤ s.potential c z` -/
@[bound] lemma le_potential (c4 : ‖c‖ ≤ 4) (z4 : ‖z‖ ≤ 4) :
    0.216 ≤ (superF d).potential c z := by
  set s := superF d
  by_cases m : (c,↑z) ∉ s.basin
  · rw [s.potential_eq_one m]
    norm_num
  simp only [not_not] at m
  obtain ⟨n,w4,w20⟩ := pass_through c4 z4 m
  generalize hw : (f' d c)^[n+1] z = w at w4 w20
  have cw : ‖c‖ ≤ ‖w‖ := by linarith
  have pw : 1 / (4 ^ d + 4) - 0.8095 / (4 ^ d + 4) ^ (1.864 : ℝ) ≤ s.potential c w := by
    have pw := (abs_le.mp (le_trans (potential_approx d w4.le cw)
      (potential_error_le_of_z4 d w4.le cw))).1
    rw [le_sub_iff_add_le, neg_add_eq_sub] at pw
    have anti := lower_anti 0.8095 1.864 (by norm_num) (by norm_num)
      (a := ‖w‖) (b := 4 ^ d + 4) w4.le (by norm_num) w20
    simp only at anti
    exact le_trans anti pw
  have pwz : s.potential c w ^ (d⁻¹ : ℝ) ≤ s.potential c z := by
    have pwz : s.potential c w = s.potential c z ^ d ^ (n+1) := by
      simp only [←hw, ←f_f'_iter, s.potential_eqn_iter]
    rw [← Real.rpow_natCast] at pwz
    have dn0 : ((d ^ (n + 1) : ℕ) : ℝ) ≠ 0 := by simp [s.d0]
    rw [← Real.rpow_inv_eq s.potential_nonneg s.potential_nonneg dn0] at pwz
    rw [← pwz]
    apply Real.rpow_le_rpow_of_exponent_ge (by bound) (by bound)
    simp only [Nat.cast_pow]
    bound
  refine le_trans ?_ pwz
  rw [Real.le_rpow_inv_iff_of_pos (by norm_num) (by bound) (by bound)]
  refine le_trans ?_ pw
  simp only [Real.rpow_natCast, one_div]
  -- Handle `d = 2` explicitly since it's tight, and be more relaxed for `2 < d`
  by_cases d2 : d = 2
  · simp only [d2]
    have le : (266 : ℝ) ≤ 20 ^ (233 / 125 : ℝ) := by
      rw [div_eq_mul_inv, Real.rpow_mul (by positivity), Real.le_rpow_inv_iff_of_pos (by norm_num)
        (by positivity) (by positivity)]
      norm_num
    norm_num
    grw [← le]
    norm_num
  · have d3 : 3 ≤ d := by have : 2 ≤ d := s.d2; omega
    exact le_of_d3 d3

end Ray_Ray_Multibrot_PotentialLower

-- ===== Ray.Multibrot.Rinv =====
section Ray_Ray_Multibrot_Rinv
/-!
## Properties of `rinv`
-/

open Complex
open Metric (ball closedBall mem_closedBall)
open RiemannSphere
open OneDimension
open Set
open scoped OneDimension OnePoint Real RiemannSphere Topology
noncomputable section

variable {c z : ℂ} {r x : ℝ}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

@[simp, bound] lemma rinv_nonneg (r0 : 0 ≤ r) : 0 ≤ rinv r c := by
  simp only [rinv]
  split_ifs <;> bound

@[bound] lemma rinv_pos (r0 : 0 < r) : 0 < rinv r c := by
  simp only [rinv]
  split_ifs <;> aesop

lemma lt_rinv : x < rinv r c ↔ x < r ∧ ‖c‖ * x < 1 := by
  simp only [rinv]
  split_ifs with c0
  · simp only [c0, norm_zero, zero_mul, zero_lt_one, and_true]
  · simp only [← one_div, lt_inf_iff, lt_div_iff₀ (norm_pos_iff.mpr c0), mul_comm]

lemma le_rinv : x ≤ rinv r c ↔ x ≤ r ∧ ‖c‖ * x ≤ 1 := by
  simp only [rinv]
  split_ifs with c0
  · simp only [c0, norm_zero, zero_mul, zero_le_one, and_true]
  · simp only [← one_div, le_inf_iff, le_div_iff₀ (norm_pos_iff.mpr c0), mul_comm]

@[simp] lemma inv_rinv (r0 : 0 < r) : (rinv r⁻¹ c)⁻¹ = max r ‖c‖ := by
  by_cases c0 : c = 0
  · simp [c0, rinv, r0.le]
  · simp only [rinv, c0, ↓reduceIte, min_def, inv_le_comm₀ r0 (inv_pos.mpr (norm_pos_iff.mpr c0)),
      inv_inv, max_def]
    grind

@[simp] lemma div_rinv (r0 : 0 < r) : x / rinv r⁻¹ c = x * max r ‖c‖ := by
  simp only [div_eq_mul_inv, inv_rinv r0]

@[simp] lemma mem_ball_rinv : z ∈ ball 0 (rinv r c) ↔ ‖z‖ < r ∧ ‖c‖ * ‖z‖ < 1 := by
  simp only [ball, dist_zero_right, lt_rinv, mem_ofPred_eq]

@[simp] lemma mem_closedBall_rinv :
    z ∈ closedBall 0 (rinv r c) ↔ ‖z‖ ≤ r ∧ ‖c‖ * ‖z‖ ≤ 1 := by
  simp only [closedBall, dist_zero_right, le_rinv, mem_ofPred_eq]

@[simp] lemma zero_mem_ball_rinv (r0 : 0 < r := by norm_num) :
    0 ∈ ball (0 : ℂ) (rinv r c) := by simp; bound

@[simp] lemma zero_mem_closedBall_rinv (r0 : 0 ≤ r := by norm_num) :
    0 ∈ closedBall (0 : ℂ) (rinv r c) := by simp; bound

@[simp] lemma inv_mem_closedBall_rinv (z4 : r ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖)
    (r0 : 0 < r := by norm_num) : z⁻¹ ∈ closedBall 0 (rinv r⁻¹ c) := by
  by_cases z0 : z = 0
  · simp [z0]
    bound
  · simp only [rinv, mem_closedBall, dist_zero_right, norm_inv]
    split_ifs with c0
    · bound
    · bound [norm_pos_iff.mpr c0]

end
end Ray_Ray_Multibrot_Rinv

-- ===== Ray.Multibrot.Postcritical =====
section Ray_Ray_Multibrot_Postcritical
/-!
## Effective bounds on postcritical points for Multibrot sets

We show that any `(c,z)` with `4 ≤ abs c ≤ abs z` is postcritical.
-/

open Metric (closedBall)
open Real (exp log)
open RiemannSphere
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

variable {c z : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-- `log (log x)` is monotone for `1 < x` -/
lemma log_log_mono {x y : ℝ} (x0 : 1 < x) (xy : x ≤ y) : log (log x) ≤ log (log y) :=
  Real.log_le_log (Real.log_pos x0) (Real.log_le_log (by positivity) xy)

/-- `log (-log x)` is antitone for `0 < x < 1` -/
lemma log_neg_log_strict_anti {x y : ℝ} (x0 : 0 < x) (y0 : 0 < y) (x1 : x < 1) (y1 : y < 1) :
    log (-log y) < log (-log x) ↔ x < y := by
  have lx := neg_pos.mpr (Real.log_neg x0 x1)
  have ly := neg_pos.mpr (Real.log_neg y0 y1)
  rw [Real.log_lt_log_iff ly lx, neg_lt_neg_iff, Real.log_lt_log_iff x0 y0]

/-- `log 2 * x ≤ log (1 + x)` for `0 ≤ x ≤ 1` -/
lemma le_log_one_add {x : ℝ} (x0 : 0 ≤ x) (x1 : x ≤ 1) : log 2 * x ≤ log (1 + x) := by
  rw [Real.le_log_iff_exp_le (by linarith)] --, Real.exp_mul, Real.exp_log (by norm_num)]
  have x0' : 0 ≤ 1 - x := by linarith
  have h := convexOn_exp.2 (mem_univ 0) (mem_univ (log 2)) x0' x0 (by abel)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, Real.exp_log zero_lt_two] at h
  ring_nf at h
  rwa [mul_comm]

/-- `log (x-1) / log x` is increasing for `2 ≤ x` -/
lemma log_ratio_mono : MonotoneOn (fun x ↦ log (x-1) / log x) (Ici 2) := by
  have hd : ∀ x, 2 ≤ x → HasDerivAt (fun x ↦ log (x-1) / log x)
      ((1 / (x-1) * log x - log (x-1) * x⁻¹) / (log x)^2) x := by
    intro x x2
    have l0 : 0 < log x := Real.log_pos (by linarith)
    refine HasDerivAt.div ?_ (Real.hasDerivAt_log (by positivity)) l0.ne'
    exact HasDerivAt.log ((hasDerivAt_id _).sub_const _) (by linarith)
  have d : DifferentiableOn ℝ (fun x ↦ log (x-1) / log x) (Ici 2) :=
    fun x m ↦ (hd x m).differentiableAt.differentiableWithinAt
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact d.continuousOn
  · exact d.mono interior_subset
  · intro x m
    simp only [nonempty_Iio, interior_Ici', mem_Ioi] at m
    have l0 : 0 < log x := Real.log_pos (by linarith)
    simp only [(hd x m.le).deriv, one_div]
    refine div_nonneg ?_ (by positivity)
    simp only [sub_nonneg, mul_comm]
    apply mul_le_mul
    · exact inv_anti₀ (by linarith) (by linarith)
    · exact Real.log_le_log (by linarith) (by linarith)
    · exact Real.log_nonneg (by linarith)
    · exact inv_nonneg.mpr (by linarith)

/-- One iterate increases `log (log (abs z))` by `Ω(1)` for large `z` -/
lemma log_log_iter (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    log (log ‖z‖) + 0.548 ≤ log (log ‖f' d c z‖) := by
  have zw : (‖z‖ - 1)^1 * ‖z‖ ≤ ‖f' d c z‖ := by
    refine iter_large (d := d) (n := 1) ?_ ?_ ?_ cz
    · linarith
    · exact le_refl _
  generalize ‖f' d c z‖ = w at zw
  generalize ‖z‖ = x at zw cz z4
  clear cz
  simp only [pow_one] at zw
  have lx1 : 1 < log (x-1) :=
    lt_trans (by norm_num) (lt_of_lt_of_le lt_log_3 (Real.log_le_log (by norm_num) (by linarith)))
  have lx : 1 < log x := lt_trans lx1 (Real.log_lt_log (by linarith) (by linarith))
  have ll : 0.791 ≤ log (x-1) / log x := by
    calc log (x-1) / log x
      _ ≥ log (4-1) / log 4 := by
          apply log_ratio_mono ?_ ?_ z4
          · simp only [mem_Ici]; norm_num
          · simp only [mem_Ici]; linarith
      _ = log 3 / log 4 := by norm_num
      _ ≥ 1.098 / 1.387 := div_le_div₀ (by positivity) lt_log_3.le (by positivity) log_4_lt.le
      _ ≥ 0.791 := by norm_num
  have ll0 : 0 ≤ log (x-1) / log x := by positivity
  have ll1 : log (x-1) / log x ≤ 1 :=
    div_le_one_of_le₀ (Real.log_le_log (by linarith) (by linarith)) (by positivity)
  calc log (log w)
    _ ≥ log (log ((x-1)*x)) := log_log_mono (by nlinarith) zw
    _ = log (log x + log (x-1)) := by rw [mul_comm, Real.log_mul (by positivity) (by linarith)]
    _ = log (log x) + log (1 + log (x-1) / log x) := by rw [log_add _ _ (by linarith) (by linarith)]
    _ ≥ log (log x) + log 2 * (log (x-1) / log x) := by bound [le_log_one_add ll0 ll1]
    _ ≥ log (log x) + 0.693 * 0.791 := by bound [lt_log_2]
    _ ≥ log (log x) + 0.548 := by bound

/-- Numerical bound we need below -/
lemma log_neg_log_le : log (-log 0.216) < -0.15 + log (log 12) := by
  trans 0.5
  · rw [Real.log_lt_iff_lt_exp (by bound)]
    trans 1.6
    · rw [neg_lt, Real.lt_log_iff_exp_lt (by norm_num)]
      norm_num
      exact exp_neg_div_lt
    · norm_num
      simpa using lt_exp_div (c := 8 / 5) (a := 1) (b := 2)
  · norm_num
    rw [Real.lt_log_iff_exp_lt (by bound)]
    trans 2
    · exact exp_div_lt
    · rw [Real.lt_log_iff_exp_lt (by bound)]
      exact exp_ofNat_lt

/-- For large `c`, large `z`'s are postcritical -/
theorem postcritical_large (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    Postcritical (superF d) c z := by
  -- Record a variety of inequalities
  have d0 : 0 < d := d_pos d
  have le_z : max 4 ‖c‖ ≤ ‖z‖ := by bound
  have lcz : log (log (max 4 ‖c‖)) ≤ log (log ‖z‖) := log_log_mono (by bound) le_z
  -- Reduce to s.potential c (f' d c z) < s.potential c ↑c
  simp only [Postcritical, multibrot_p]
  set s := superF d
  rw [← Real.pow_rpow_inv_natCast s.potential_nonneg d0.ne', ←
    Real.pow_rpow_inv_natCast (s.potential_nonneg : 0 ≤ s.potential c 0) d0.ne']
  simp only [← s.potential_eqn]
  refine Real.rpow_lt_rpow s.potential_nonneg ?_ (by bound)
  generalize hw : f' d c z = w
  have e : f d c z = w := by rw [f, lift_coe', hw]
  simp only [f_0, e]; clear e
  have zw : ‖z‖ ≤ ‖w‖ := by rw [←hw]; exact le_self_iter d (by linarith) cz 1
  have cw : ‖c‖ ≤ ‖w‖ := le_trans cz zw
  -- Move to log (-log _) space
  have pw1 : s.potential c w < 1 := potential_lt_one_of_two_lt (by linarith) (by linarith)
  by_cases pc1 : s.potential c c = 1
  · linarith
  replace pc1 : s.potential c c < 1 := Ne.lt_of_le pc1 (s.potential_le_one)
  rw [←log_neg_log_strict_anti potential_pos potential_pos pw1 pc1]
  -- Bounds about `iter_error`
  have lzw : log (log ‖z‖) + 0.548 ≤ log (log ‖w‖) := by
    rw [←hw]; exact log_log_iter (by linarith) cz
  have ie : ∀ z : ℂ, 4 ≤ ‖z‖ → ‖c‖ ≤ ‖z‖ → iter_error d c z ≤ 0.15 := by
    intro z z4 cz
    refine le_trans (iter_error_le_of_z4 d z4 cz) ?_
    calc 0.8095 / (‖z‖ * log ‖z‖)
      _ ≤ 0.8095 / (4 * log 4) := by bound
      _ ≤ 0.8095 / (4 * 1.386) := by bound [lt_log_4]
      _ ≤ 0.15 := by norm_num
  have iew := ie w (by linarith) cw
  -- Use `log_neg_log_potential_approx` to replace `s.potential` with `log (log (abs _))`
  refine lt_of_lt_of_le ?_ (le_sub_iff_add_le.mp (abs_le.mp
    (log_neg_log_potential_approx d (by linarith) cw)).1)
  -- If `c` is small, we can use our potential lower bound
  by_cases c4 : ‖c‖ < 4
  · refine lt_of_le_of_lt (b := log (-log 0.216)) ?_ ?_
    · by_cases p1 : s.potential c c = 1
      · simp [p1]
        bound
      · replace p1 : s.potential c c < 1 := Ne.lt_of_le p1 s.potential_le_one
        bound
    · have w12 : 12 ≤ ‖w‖ := by
        calc ‖w‖
          _ = ‖z ^ d + c‖ := by simp only [← hw, f']
          _ ≥ ‖z ^ d‖ - ‖c‖ := by bound
          _ = ‖z‖ ^ d - ‖c‖ := by simp only [norm_pow]
          _ ≥ 4 ^ d - 4 := by bound
          _ ≥ 4 ^ 2 - 4 := by bound
          _ ≥ 12 := by norm_num
      grw [iew, ← w12]
      exact log_neg_log_le
  simp only [not_lt] at c4
  simp only [max_eq_right c4] at lcz
  -- Settle our inequality
  refine lt_of_le_of_lt (sub_le_iff_le_add.mp (abs_le.mp
    (log_neg_log_potential_approx d (by linarith) (le_refl _))).2) ?_
  have iec := ie c c4 (le_refl _)
  refine lt_of_lt_of_le (lt_of_le_of_lt (add_le_add iec lcz) ?_) (add_le_add (neg_le_neg iew) lzw)
  ring_nf; simp only [add_lt_add_iff_right]; norm_num

/-- For large `c` and small `z`, `(c,z⁻¹)` is postcritical -/
lemma postcritical_small (le : ‖z‖ ≤ rinv 4⁻¹ c) :
    (c, (z : (OnePoint ℂ))⁻¹) ∈ (superF d).post := by
  set s := superF d
  by_cases z0 : z = 0
  · simp only [z0, coe_zero, inv_zero', s.post_a]
  · rw [inv_coe z0]
    obtain ⟨z4, zc⟩ := le_rinv.mp le
    apply postcritical_large
    · simp only [norm_inv]
      rwa [le_inv_comm₀ (by bound) (norm_pos_iff.mpr z0)]
    · by_cases c0 : c = 0
      · simp only [c0, norm_zero, norm_inv, inv_nonneg, norm_nonneg]
      · simp only
        rwa [norm_inv, ← one_div, le_div_iff₀ (by simpa)]

end
end Ray_Ray_Multibrot_Postcritical

-- ===== Ray.Multibrot.RealBounds =====
section Ray_Ray_Multibrot_RealBounds
/-!
## Real iteration bounds useful for `bottcher` bounds
-/

open Complex
open Metric (closedBall mem_closedBall mem_closedBall_self)
open Real (exp log)
open Set
open scoped Real Topology
noncomputable section

variable {c z : ℂ}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-!
### Noniteration lemmas
-/

/-- Prove `c * x ≤ y` if `c ≤ 0` -/
lemma cx_le {c x y : ℝ} (h : 0 < c → c * x ≤ y) (x0 : 0 ≤ x := by bound)
    (y0 : 0 ≤ y := by bound) : c * x ≤ y := by
  by_cases c0 : c ≤ 0
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg c0 (by bound)) y0
  · exact h (by bound)

/-- Absorb a free `x` into `x⁻¹ ^ d` -/
lemma mul_inv_pow_d (d : ℕ) [Fact (2 ≤ d)] (x : 𝕜) : x * x⁻¹ ^ d = x⁻¹ ^ (d - 1) := by
  by_cases x0 : x = 0
  · simp only [x0, inv_zero, zero_mul]
    have d2 := two_le_d d
    rw [zero_pow (by omega)]
  · nth_rw 1 [← Nat.sub_add_cancel (d_ge_one d), pow_succ', ← mul_assoc, mul_inv_cancel₀ x0,
      one_mul]

/-- Loose bound on `c * x ^ d` -/
@[bound] lemma cxd_le (d : ℕ) [d2 : Fact (2 ≤ d)] (c x : ℝ) (x0 : 0 ≤ x)
    (x3 : x ≤ 3⁻¹) (cx : c * x ≤ 1) : c * x ^ d ≤ 3⁻¹ := by
  refine cx_le fun c0 ↦ ?_
  calc c * x ^ d
    _ ≤ c * x ^ 2 := by bound
    _ = c * x * x := by ring
    _ ≤ 1 * x := by bound
    _ ≤ 3⁻¹ := by bound


/-- This one needs to be higher priority to be used by `bound`, which is a bit sketchy. -/
@[aesop safe apply (rule_sets := [Bound])] public lemma cxd_lt_1 (d : ℕ) [d2 : Fact (2 ≤ d)]
    (c x : ℝ) (x0 : 0 ≤ x) (x3 : x ≤ 3⁻¹) (cx : c * x ≤ 1) : c * x ^ d < 1 :=
  lt_of_le_of_lt (cxd_le d c x x0 x3 cx) (by norm_num)

/-- This one needs to be higher priority to be used by `bound`, which is a bit sketchy. -/
@[aesop safe apply (rule_sets := [Bound])] public lemma cxd_le_1 (d : ℕ) [d2 : Fact (2 ≤ d)]
    (c x : ℝ) (x0 : 0 ≤ x) (x3 : x ≤ 3⁻¹) (cx : c * x ≤ 1) : c * x ^ d ≤ 1 :=
  (cxd_lt_1 d c x x0 x3 cx).le

/-!
### Multibrot real iteration bounds
-/

/-- Function we'll iterate in tight bounds below -/
def fb (d : ℕ) (b : ℝ) (x : ℝ) : ℝ := x ^ d / (1 - b * x ^ d)

/-- Real iterates are positive and small -/
lemma fb_nonneg_le (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (z3 : 3 ≤ z) (cz : c ≤ z) (n : ℕ) :
    (fb d c)^[n] z⁻¹ ∈ Ioc 0 z⁻¹ := by
  have czi : c * z⁻¹ ≤ 1 := by bound
  have z3 : z⁻¹ ≤ 3⁻¹ := by bound
  induction' n with n h
  · simp
    linarith
  · simp only [Function.iterate_succ_apply']
    generalize hx : (fb d c)^[n] z⁻¹ = x at h
    have cx : c * x ≤ 1 := cx_le fun c0 ↦ le_trans (by bound) czi
    simp only [fb]
    refine ⟨by bound, ?_⟩
    calc x ^ d / (1 - c * x ^ d)
      _ ≤ x ^ 2 / (1 - 3⁻¹) := by bound
      _ = x / (1 - 3⁻¹) * x := by ring
      _ ≤ 3⁻¹ / (1 - 3⁻¹) * z⁻¹ := by bound
      _ ≤ z⁻¹ := by bound

@[bound] lemma fb_nonneg (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (z3 : 3 ≤ z) (cz : c ≤ z) (n : ℕ) :
    0 ≤ (fb d c)^[n] z⁻¹ := (fb_nonneg_le d c z z3 cz n).1.le
@[bound] lemma fb_pos (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (z3 : 3 ≤ z) (cz : c ≤ z) (n : ℕ) :
    0 < (fb d c)^[n] z⁻¹ := (fb_nonneg_le d c z z3 cz n).1
@[bound] lemma fb_le_z (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (z3 : 3 ≤ z) (cz : c ≤ z) (n : ℕ) :
    (fb d c)^[n] z⁻¹ ≤ z⁻¹ := (fb_nonneg_le d c z z3 cz n).2
@[bound] lemma c_fb (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (z3 : 3 ≤ z) (cz : c ≤ z) (n : ℕ) :
    c * (fb d c)^[n] z⁻¹ ≤ 1 := by
  refine cx_le fun c0 ↦ ?_
  rw [mul_comm, ← le_div_iff₀ c0, one_div]
  trans z⁻¹
  all_goals bound
@[bound] lemma fb_le_3i (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (z3 : 3 ≤ z) (cz : c ≤ z) (n : ℕ) :
    (fb d c)^[n] z⁻¹ ≤ 3⁻¹ := le_trans (fb_le_z d c z z3 cz n) (by bound)
@[bound] lemma fb_le_1 (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (z3 : 3 ≤ z) (cz : c ≤ z) (n : ℕ) :
    (fb d c)^[n] z⁻¹ ≤ 1 := le_trans (fb_le_z d c z z3 cz n) (by bound)

@[bound] lemma fb_mono_d (d : ℕ) [Fact (2 ≤ d)] (b x : ℝ) (b0 : 0 ≤ b) (x3 : 3 ≤ x)
    (bx : b ≤ x) (n : ℕ) : b * (fb d b)^[n] x⁻¹ ^ d ≤ b * (fb 2 b)^[n] x⁻¹ ^ 2 := by
  by_cases bz : b = 0
  · simp only [bz, zero_mul, le_refl]
  replace b0 : 0 < b := by positivity
  have xb : x⁻¹ ≤ b⁻¹ := by bound
  induction' n with n uv
  · simp only [Function.iterate_zero, id_eq]
    bound
  · simp only [Function.iterate_succ_apply']
    generalize hu : (fb d b)^[n] x⁻¹ = u at uv
    generalize hv : (fb 2 b)^[n] x⁻¹ = v at uv
    refine mul_le_mul_of_nonneg_left ?_ (by bound)
    have u1 : u ^ d / (1 - b * u ^ d) ≤ 1 := by
      calc u ^ d / (1 - b * u ^ d)
        _ ≤ u / (1 - 3⁻¹) := by bound
        _ ≤ 3⁻¹ / (1 - 3⁻¹) := by bound
        _ ≤ 1 := by norm_num
    trans (fb d b u) ^ 2
    · simp only [fb]
      bound
    · simp only [fb]
      rw [mul_le_mul_iff_of_pos_left (by linarith)] at uv
      bound

@[bound] lemma fb_mono_d_weak (d : ℕ) [Fact (2 ≤ d)] (b x : ℝ) (b0 : 0 ≤ b) (x3 : 3 ≤ x)
    (bx : b ≤ x) (n : ℕ) : (fb d b)^[n] x⁻¹ ^ d ≤ (fb 2 b)^[n] x⁻¹ ^ 2 := by
  by_cases bz : b ≤ 0
  · replace b0 : b = 0 := by linarith
    simp only [b0, ge_iff_le]
    induction' n with n h
    · simp only [Function.iterate_zero, id_eq, inv_pow]
      bound
    · simp only [Function.iterate_succ_apply', fb, zero_mul, sub_zero, div_one]
      trans ((fb 2 0)^[n] x⁻¹ ^ 2) ^ d
      · bound
      · bound
  · have h := fb_mono_d d b x b0 x3 bx n
    rwa [mul_le_mul_iff_of_pos_left (by bound)] at h

@[bound] lemma f_le_fb (d : ℕ) [Fact (2 ≤ d)] (c z : ℂ) (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖)
    (n : ℕ) : ‖(fun z ↦ z ^ d / (1 + c * z ^ d))^[n] z⁻¹‖ ≤ (fb d ‖c‖)^[n] ‖z‖⁻¹ := by
  induction' n with n h
  · simp only [Function.iterate_zero, id_eq, norm_inv, le_refl]
  · simp only [Function.iterate_succ_apply']
    generalize hw : (fun z ↦ z ^ d / (1 + c * z ^ d))^[n] z⁻¹ = w at h
    generalize hx : (fb d ‖c‖)^[n] ‖z‖⁻¹ = x at h
    simp only [norm_pow, norm_div, fb] at h ⊢
    apply div_le_div₀ (by bound) (by bound) (by bound)
    calc ‖1 + c * w ^ d‖
      _ ≥ ‖(1 : ℂ)‖ - ‖c * w ^ d‖ := by bound
      _ = 1 - ‖c‖ * ‖w‖ ^ d := by simp only [norm_one, Complex.norm_mul, norm_pow]
      _ ≥ 1 - ‖c‖ * x ^ d := by bound

/-- `fb` is monotone in `z` for fixed `c` -/
@[bound] lemma fb_mono_z (d : ℕ) [Fact (2 ≤ d)] (c z : ℝ) (c3 : 3 ≤ c)
    (cz : c ≤ z) (n : ℕ) : (fb d c)^[n] z⁻¹ ≤ (fb d c)^[n] c⁻¹ := by
  induction' n with n h
  · simp
    bound
  · simp only [Function.iterate_succ_apply', fb]
    bound

/-- `fb` is monotone in `c` for fixed `z` -/
@[bound] lemma fb_mono_cz (d : ℕ) [Fact (2 ≤ d)] (c z : ℝ) (z3 : 3 ≤ z)
    (cz : c ≤ z) (n : ℕ) : (fb d c)^[n] z⁻¹ ≤ (fb d z)^[n] z⁻¹ := by
  induction' n with n h
  · simp
  · simp only [Function.iterate_succ_apply', fb]
    bound

/-- Diagonal `fb` is monotone in `c`, in two different ways -/
lemma fb_mono_c (d : ℕ) [Fact (2 ≤ d)] (c b : ℝ) (b3 : 3 ≤ b) (bc : b ≤ c) (n : ℕ) :
    (fb d c)^[n] c⁻¹ ≤ (fb d b)^[n] b⁻¹ ∧ c * (fb d c)^[n] c⁻¹ ^ d ≤ b * (fb d b)^[n] b⁻¹ ^ d := by
  induction' n with n h
  · simp only [Function.iterate_zero, id_eq, mul_inv_pow_d]
    bound
  · have dd : d * d = d + d * (d - 1) := by rw [← mul_one_add, Nat.add_sub_cancel' (d_ge_one d)]
    simp only [Function.iterate_succ_apply', fb, div_pow, ← mul_div_assoc, ← pow_mul, dd, pow_add,
      ← mul_assoc]
    bound

@[bound] lemma fb_mono_c_weak (d : ℕ) [Fact (2 ≤ d)] (c b : ℝ) (b3 : 3 ≤ b) (bc : b ≤ c)
    (n : ℕ) : (fb d c)^[n] c⁻¹ ≤ (fb d b)^[n] b⁻¹ := (fb_mono_c d c b b3 bc n).1
@[bound] lemma fb_mono_c_strong (d : ℕ) [Fact (2 ≤ d)] (c b : ℝ) (b3 : 3 ≤ b) (bc : b ≤ c)
    (n : ℕ) : c * (fb d c)^[n] c⁻¹ ^ d ≤ b * (fb d b)^[n] b⁻¹ ^ d := (fb_mono_c d c b b3 bc n).2

@[bound] lemma fb_mono_cz_weak (d : ℕ) [Fact (2 ≤ d)] {b c z : ℝ} (b3 : 3 ≤ b) (bc : b ≤ c)
    (cz : c ≤ z) (n : ℕ) : (fb d c)^[n] z⁻¹ ≤ (fb d b)^[n] b⁻¹ :=
  le_trans (by bound) (fb_mono_c_weak d c b b3 bc n)
@[bound] lemma fb_mono_cz_strong (d : ℕ) [Fact (2 ≤ d)] {b c z : ℝ} (b3 : 3 ≤ b) (bz : b ≤ z)
    (cz : c ≤ z) (n : ℕ) : c * (fb d c)^[n] z⁻¹ ^ d ≤ b * (fb d b)^[n] b⁻¹ ^ d :=
  le_trans (by bound) (fb_mono_c_strong d z b b3 bz n)

@[bound] lemma term_mono_d (d : ℕ) [Fact (2 ≤ d)] {c z : ℝ} (c0 : 0 ≤ c) (z3 : 3 ≤ z)
    (cz : c ≤ z) (n : ℕ) :
    (1 - c * (fb d c)^[n] z⁻¹ ^ d) ^ (-1 / d ^ (n + 1) : ℝ) - 1 ≤
      (1 - c * (fb 2 c)^[n] z⁻¹ ^ 2) ^ (-1 / 2 ^ (n + 1) : ℝ) - 1 := by
  apply sub_le_sub_right
  trans (1 - c * (fb 2 c)^[n] z⁻¹ ^ 2) ^ (-1 / d ^ (n + 1) : ℝ)
  · apply Real.rpow_le_rpow_of_nonpos <;> bound
  · apply Real.rpow_le_rpow_of_exponent_ge
    · bound
    · bound
    · simp only [neg_div, one_div, neg_le_neg_iff]
      bound

/-!
### Factorised bounds
-/

/-- Iteration after we pull out the `b⁻¹ ^ 2 ^ d` factor -/
def factor (d : ℕ) (b : 𝕜) (p : 𝕜 × 𝕜) : 𝕜 × 𝕜 :=
  let a := (1 - b * p.1 ^ d)⁻¹
  (p.1 ^ d * a, p.2 ^ d * a)

@[simp] lemma fst_factor (d : ℕ) (b x : ℝ) (n : ℕ) :
    ((factor d b)^[n] (x,1)).1 = (fb d b)^[n] x := by
  induction' n with n h
  · simp only [Function.iterate_zero, id_eq]
  · simp only [Function.iterate_succ_apply', factor, h, fb, div_eq_mul_inv]

/-- Factored version of `fb` iteration -/
lemma fb_eq_factor (d : ℕ) (b x : ℝ) (n : ℕ) :
    (fb d b)^[n] x = ((factor d b)^[n] (x,1)).2 * x ^ d ^ n := by
  induction' n with n h
  · simp only [Function.iterate_zero, id_eq, pow_zero, pow_one, one_mul]
  · simp only [Function.iterate_succ_apply', fb, factor, h, div_eq_mul_inv, mul_pow, ← pow_mul,
      ← pow_succ, mul_assoc, mul_comm (x ^ _), fst_factor]

/-- `factor.2` as a division -/
lemma factor_eq_div {d : ℕ} {b x : ℝ} (x0 : x ≠ 0) {n : ℕ} :
    ((factor d b)^[n] (x,1)).2 = (fb d b)^[n] x / x ^ d ^ n := by
  simp only [fb_eq_factor, mul_div_assoc, ← div_pow, div_self x0, one_pow, mul_one]

@[bound] lemma factor_pos (d : ℕ) [Fact (2 ≤ d)] (b x : ℝ) (x3 : 3 ≤ x) (bx : b ≤ x)
    (n : ℕ) : 0 < ((factor d b)^[n] (x⁻¹,1)).2 := by
  induction' n with n h
  · simp
  · simp only [Function.iterate_succ_apply', factor, fst_factor]
    bound

@[bound] lemma factor_nonneg (d : ℕ) [Fact (2 ≤ d)] (b x : ℝ) (x3 : 3 ≤ x) (bx : b ≤ x) (n : ℕ) :
    0 ≤ ((factor d b)^[n] (x⁻¹,1)).2 := (factor_pos d b x x3 bx n).le

@[bound] lemma factor_mono (d : ℕ) [Fact (2 ≤ d)] {b c z : ℝ} (b3 : 3 ≤ b) (bz : b ≤ z) (cz : c ≤ z)
    (n : ℕ) : ((factor d c)^[n] (z⁻¹, 1)).2 ≤ ((factor d b)^[n] (b⁻¹, 1)).2 := by
  induction' n with n h
  · simp
  · simp only [Function.iterate_succ_apply', factor, fst_factor]
    bound [fb_mono_cz_strong d b3 bz cz n]

@[bound] lemma fb_le_factor (d : ℕ) [Fact (2 ≤ d)] {b c z : ℝ} (b3 : 3 ≤ b) (c0 : 0 ≤ c)
    (bz : b ≤ z) (cz : c ≤ z) (n : ℕ) :
    c * (fb d c)^[n] z⁻¹ ^ d ≤ ((factor d b)^[n] (b⁻¹, 1)).2 ^ d * z⁻¹ ^ (d ^ (n + 1) - 1) := by
  have z0 : 0 < z := by linarith
  simp only [fb_eq_factor, mul_pow, ← pow_mul, ← pow_succ, mul_comm c]
  rw [pow_sub₀ _ (by positivity) (by bound), ← mul_assoc, pow_one, inv_inv]
  bound

/-!
### Doubly exponential bounds, and related

These are used to bound the tail products of `term` bounds.
-/

lemma fb_le_pow_pow (d : ℕ) [Fact (2 ≤ d)] {b : ℝ} (b3 : 3 ≤ b) (n : ℕ) :
    (fb 2 b)^[n] b⁻¹ ≤ 2 / 3 * 2⁻¹ ^ 2 ^ n := by
  induction' n with n h
  · norm_num
    simp only [one_div]
    bound
  · simp only [Function.iterate_succ_apply', fb]
    generalize hx : (fb 2 b)^[n] b⁻¹ = x at h
    calc x ^ 2 / (1 - b * x ^ 2)
      _ ≤ (2 / 3 * 2⁻¹ ^ 2 ^ n) ^ 2 / (1 - 3⁻¹) := by bound
    simp only [mul_pow, ← pow_mul, ← pow_succ, div_eq_inv_mul]
    linarith

end
end Ray_Ray_Multibrot_RealBounds


