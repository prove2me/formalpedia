-- Prove2me | Definitions.Def_ray_multibrot_connected
-- name    : ray_multibrot_connected
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T21:19:45.253991+00:00
-- url     : https://prove2.me/theorems/da7f6f3c-60d7-4b61-b1de-4b1bad7c7593
-- title:
--   ray (12/12): the Böttcher isomorphism; Multibrot and Mandelbrot sets are connected
-- statement:
--   **Douady–Hubbard.** The diagonal Böttcher map $\Phi(c) = b_c(c)$ is analytic on $\widehat{\mathbb{C}} \setminus M_d$ and is a bijection onto the open unit disk, via $\Phi(\infty) = 0$ in the coordinate $1/z$. Hence $\widehat{\mathbb{C}} \setminus M_d$ is analytically isomorphic to a disk. It follows that every Multibrot set $M_d$ ($d \ge 2$) and its complement are connected (`isConnected_multibrot`, `isConnected_compl_multibrot`). In particular the Mandelbrot set, ray's `mandelbrot` $= \{c : \lVert f_c^{\,n}(c)\rVert \not\to \infty\}$ with $f_c(z) = z^2 + c$, is connected (`isConnected_mandelbrot`).
--
--   This file is part 12 of 12 of a verbatim flattening of Geoffrey Irving's Lean 4 formalization *ray* (https://github.com/girving/ray, Apache License 2.0). Together the 12 files prove that the Mandelbrot set is connected. Each original ray module is wrapped in its own `section`, and module-system keywords are removed. A few mechanical edits avoid clashes with the full Mathlib import and avoid syntax extensions: a duplicated private definition is dropped, `ContinuousOn.partialSups` is renamed to `ContinuousOn.rayPartialSups`, `Finset.antidiagonal` is written as `Finset.HasAntidiagonal.antidiagonal`, the `bound_destruct` attribute macro is inlined, and the notation `𝕊` is replaced by `(OnePoint ℂ)`. The files are split only because of the compile-time limit. Declaration names are ray's own.
-- source:
--   Geoffrey Irving, ray: The Mandelbrot set is connected (Lean 4 formalization), https://github.com/girving/ray (Apache License 2.0), commit of 2026-08-16; module list in the file header. Mathematical background: A. Douady and J. H. Hubbard, Itération des polynômes quadratiques complexes, C. R. Acad. Sci. Paris 294 (1982); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Section 9 and Appendix; Carleson–Gamelin, Complex Dynamics, Ch. VIII.

import Definitions.Def_ray_multibrot_potential

/-!
# ray (12/12): the Böttcher isomorphism; Multibrot and Mandelbrot sets are connected

Part 12 of 12 of a flattened copy of Geoffrey Irving's Lean 4 formalization *ray*
(https://github.com/girving/ray, Apache License 2.0, Copyright Geoffrey Irving), which proves that
the Mandelbrot set is connected. Each original module is wrapped in its own `section`;
module-system keywords are removed, and a few names are adjusted to avoid clashes with Mathlib.

Original modules in this file:
* `Ray.Multibrot.Bottcher`
* `Ray.Multibrot.Isomorphism`
* `Ray.Multibrot.Connected`
* `Ray.Mandelbrot`
-/

-- ===== Ray.Multibrot.Bottcher =====
section Ray_Ray_Multibrot_Bottcher
/-!
## Effective bounds on the Multibrot `bottcher` function

We derive effective bounds and estimates for the Böttcher coordinates of the Multibrot sets.  These
are used in `Isomorphism.lean` and `Connected.lean` to prove our main theoretical results.

We mainly need that our diagonal Böttcher `bottcher d c` is analytic with derivative 1 at `∞`,
by showing that the analytically continued map is given by the infinite product for large `c`.
This does not follow immediately from our dynamical work, which covers only finite `c : ℂ`.  I'm
uneasy that I've missed some basic conceptual arguments that would get to the analyticity result
more directly, though the effective calculations we did along the way are also useful for numerics.

Our main results are:

1. If `4 ≤ ‖c‖ ≤ ‖z‖`, `s.bottcher = bottcherNear`, and thus the infinite product holds.
2. If `4 ≤ ‖c‖ ≤ ‖z‖`, `‖s.bottcher c z - z⁻¹‖ ≤ 0.943 * ‖z‖⁻¹ ^ 2`
3. `bottcher d` is monic at `∞` (has derivative 1 there)
-/

open Complex
open Function (uncurry)
open Filter (Tendsto)
open Metric (closedBall mem_closedBall mem_closedBall_self)
open Real (exp log)
open RiemannSphere
open OneDimension
open Set
open scoped OneDimension OnePoint Real RiemannSphere Topology
noncomputable section

variable {c z : ℂ}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-- `z⁻¹` is in the `superNearC` region for large `z` -/
lemma inv_mem_t (z3 : 3 < ‖z‖) (cz : ‖c‖ ≤ ‖z‖) : z⁻¹ ∈ superNearT d c := by
  simp only [mem_ofPred, norm_inv, superNearT, one_div]
  refine ⟨by bound, ?_⟩
  by_cases c0 : c = 0
  · simp [c0]
  replace c0 : 0 < ‖c‖ := norm_pos_iff.mpr c0
  calc ‖c‖ * ‖z‖⁻¹ ^ d
    _ ≤ ‖c‖ * ‖z‖⁻¹ ^ 2 := by bound
    _ = ‖c‖ * ‖z‖⁻¹ * ‖z‖⁻¹ := by ring
    _ ≤ ‖c‖ * ‖c‖⁻¹ * 3⁻¹ := by bound
    _ = 1 * 3⁻¹ := by grind
    _ < 2 / 5 := by norm_num

/-- We're in the near region -/
lemma closedBall_rinv_subset_superNearT : closedBall 0 (rinv 4⁻¹ c) ⊆ superNearT d c := by
  intro z m
  by_cases z0 : z = 0
  · simp [z0, superNearT, zero_pow (d_ne_zero _)]
  rw [mem_closedBall_rinv] at m
  rw [← inv_inv z]
  apply inv_mem_t
  · simp only [norm_inv]
    rw [lt_inv_comm₀ (by linarith) (by positivity)]
    linarith
  · rw [norm_inv, ← one_div, le_div_iff₀ (by positivity)]
    exact m.2

/-- `s.bottcher = bottcherNear` for large `z`.
    This means that `s.bottcher` is given by the infinite product formula from `BottcherNear.lean`
    for large `z`. -/
theorem bottcher_eq_bottcherNear_z (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    (superF d).bottcher c z = bottcherNear (fl (f d) ∞ c) d z⁻¹ := by
  have z0 : 0 < ‖z‖ := by linarith
  set s := superF d
  suffices e : EqOn (fun z : ℂ ↦ s.bottcher c (z : (OnePoint ℂ))⁻¹) (bottcherNear (fl (f d) ∞ c) d)
      (closedBall 0 (rinv 4⁻¹ c)) by
    have z0' : z ≠ 0 := norm_ne_zero_iff.mp z0.ne'
    convert @e z⁻¹ _
    · rw [inv_coe (inv_ne_zero z0'), inv_inv]
    · apply inv_mem_closedBall_rinv z4 cz
  have a0 : ContMDiffOnNhd I I (fun z : ℂ ↦ s.bottcher c (z : (OnePoint ℂ))⁻¹)
      (closedBall 0 (rinv 4⁻¹ c)) := by
    intro z m
    refine (s.bottcher_mAnalyticOn _ ?_).along_snd.comp _ (mAnalytic_inv.comp mAnalytic_coe _)
    exact postcritical_small (by simpa using m)
  have a1 : ContMDiffOnNhd I I (bottcherNear (fl (f d) ∞ c) d) (closedBall 0 (rinv 4⁻¹ c)) := by
    intro z m; apply AnalyticAt.mAnalyticAt
    apply bottcherNear_analytic_z (superNearF d c)
    exact closedBall_rinv_subset_superNearT m
  refine (a0.eq_of_locally_eq a1 (convex_closedBall _ _).isPreconnected ?_).self_of_nhdsSet
  use 0, zero_mem_closedBall_rinv
  have e : ∀ᶠ z in 𝓝 0, bottcherNear (fl (f d) ∞ c) d z = s.bottcherNear c (z : (OnePoint ℂ))⁻¹ := by
    simp only [Super.bottcherNear, extChartAt_inf_apply, inv_inv, toComplex_coe,
      RiemannSphere.inv_inf, toComplex_zero, sub_zero, Super.fl, Filter.eventually_true]
  refine Filter.EventuallyEq.trans ?_ (Filter.EventuallyEq.symm e)
  have i : Tendsto (fun z : ℂ ↦ (z : (OnePoint ℂ))⁻¹) (𝓝 0) (𝓝 ∞) := by
    have h : ContinuousAt (fun z : ℂ ↦ (z : (OnePoint ℂ))⁻¹) 0 :=
      (RiemannSphere.continuous_inv.comp continuous_coe).continuousAt
    simp only [ContinuousAt, coe_zero, inv_zero'] at h; exact h
  exact i.eventually (s.bottcher_eq_bottcherNear c)

/-- `bottcher' = bottcherNear` for large `c` -/
theorem bottcher_eq_bottcherNear (c4 : 4 ≤ ‖c‖) :
    bottcher' d c = bottcherNear (fl (f d) ∞ c) d c⁻¹ :=
  bottcher_eq_bottcherNear_z c4 (le_refl _)

/-- Rule out the negative real axis via smallness -/
lemma arg_ne_pi_of_small (z1 : ‖z‖ ≤ 1) : arg (1 + z) ≠ π := by
  refine (lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt ?_ (half_lt_self Real.pi_pos))).ne
  rw [Complex.abs_arg_le_pi_div_two_iff, Complex.add_re, Complex.one_re]
  calc 1 + z.re
    _ ≥ 1 + -|z.re| := by bound
    _ = 1 - |z.re| := by ring
    _ ≥ 1 - ‖z‖ := by bound
    _ ≥ 0 := by linarith

/-- Terms in the `bottcherNear` product are close to 1 -/
theorem term_approx (d : ℕ) [Fact (2 ≤ d)] (z3 : 3 < ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤ 2 * 2⁻¹ ^ n * ‖z‖⁻¹ := by
  set s := superF d
  simp only [term]
  have wc := iterates_converge (superNearF d c) n (inv_mem_t (by bound) cz)
  generalize hw : (fl (f d) ∞ c)^[n] z⁻¹ = w at wc
  replace wc : ‖w‖ ≤ ‖z‖⁻¹ := by rw [norm_inv] at wc; exact le_trans wc (by bound)
  have cw : ‖c * w ^ d‖ ≤ ‖z‖⁻¹ := by
    simp only [norm_mul, norm_pow]
    calc ‖c‖ * ‖w‖ ^ d
      _ ≤ ‖z‖ * ‖z‖⁻¹ ^ d := by bound
      _ ≤ ‖z‖ * ‖z‖⁻¹ ^ 2 := by bound
      _ = ‖z‖⁻¹ := by rw [pow_two]; field_simp
  have cw2 : ‖c * w ^ d‖ ≤ 2⁻¹ := by
    have i3 : ‖z‖⁻¹ ≤ 3⁻¹ := by bound
    linarith
  simp only [gl_f, gl]
  rw [Complex.inv_cpow _ _ (arg_ne_pi_of_small (by linarith)), ← Complex.cpow_neg]
  have dn : ‖-(1 / ((d ^ (n + 1) : ℕ) : ℂ))‖ ≤ (1 / 2 : ℝ) ^ (n + 1) := by simp; bound
  have d1 : ‖-(1 / ((d ^ (n + 1) : ℕ) : ℂ))‖ ≤ 1 := le_trans dn (by bound)
  refine le_trans (pow_small ?_ d1) ?_
  · simp only [add_sub_cancel_left, one_div, cw2]
  · rw [add_sub_cancel_left]
    calc 4 * ‖c * w ^ d‖ * ‖-(1 / ((d ^ (n + 1) : ℕ) : ℂ))‖
      _ ≤ 4 * ‖z‖⁻¹ * 2⁻¹ ^ (n + 1) := by bound
      _ ≤ 2 * 2⁻¹ ^ n * ‖z‖⁻¹ := by
        simp only [pow_succ, ← mul_assoc, mul_comm _ (2⁻¹ : ℝ)]
        ring_nf
        rfl

/-- Tight version of `term_approx`, with the bound depending on `‖c‖, ‖z‖` -/
lemma term_approx_tight_cz (d : ℕ) [Fact (2 ≤ d)] (z3 : 3 < ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤
      (1 - ‖c‖ * ((fb d ‖c‖)^[n] ‖z‖⁻¹) ^ d) ^ (-1 / d ^ (n + 1) : ℝ) - 1 := by
  set s := superF d
  generalize hw : (fl (f d) ∞ c)^[n] z⁻¹ = w
  simp only [term, gl_f, gl, hw]
  simp only [fl_f] at hw
  have czi : ‖c‖ * ‖z‖⁻¹ ≤ 1 := by bound
  have zi : ‖z‖⁻¹ ≤ 3⁻¹ := by bound
  have le := hw ▸ f_le_fb d c z z3.le cz n
  obtain ⟨y0,y3⟩ := fb_nonneg_le d ‖c‖ ‖z‖ z3.le cz n
  generalize hy : (fb d ‖c‖)^[n] ‖z‖⁻¹ = y at le y0 y3
  have cw : ‖c‖ * ‖w‖ ≤ 1 := le_trans (by bound) czi
  rw [Complex.inv_cpow, ← Complex.cpow_neg, neg_div', Nat.cast_pow]
  · generalize hp : (-1 / d ^ (n + 1) : ℝ) = p
    have hp' : (-1 / d ^ (n + 1) : ℂ) = p := by simp [← hp]
    simp only [hp']
    have p0 : p ≤ 0 := by bound
    refine le_trans (Complex.norm_one_add_cpow_sub_one_le_rpow_sub_one ?_ p0) ?_
    · simp
      bound
    · simp only [Complex.norm_mul, norm_pow, tsub_le_iff_right, sub_add_cancel]
      exact Real.rpow_le_rpow_of_nonpos (by bound) (by bound) p0
  · apply arg_ne_pi_of_small
    simp
    bound

/-- Tight version of `term_approx`, with the bound depending only on a `c, z` lower bound `b` -/
lemma term_approx_tight (d : ℕ) [Fact (2 ≤ d)] (b : ℝ) (b3 : 3 < b) (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖)
    (n : ℕ) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤
      (1 - b * ((fb d b)^[n] b⁻¹) ^ d) ^ (-1 / d ^ (n + 1) : ℝ) - 1 := by
  refine le_trans (term_approx_tight_cz d (by linarith) cz n) (sub_le_sub_right ?_ _)
  refine Real.rpow_le_rpow_of_nonpos (by bound) (sub_le_sub_left ?_ _) (by bound)
  grw [fb_mono_cz d ‖c‖ ‖z‖ (by linarith) cz n, cz]
  all_goals bound

/-- Constant version of `term_approx_tight`, based on computable bounds -/
lemma term_approx_const {d n : ℕ} [Fact (2 ≤ d)] {b t : ℝ}
    (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (b3 : 3 < b := by norm_num) (t0 : 0 < t := by norm_num)
    (crunch : (t + 1) ^ (-2 ^ (n + 1) : ℤ) ≤ 1 - b * (fb 2 b)^[n] b⁻¹ ^ 2 := by norm_num [fb]) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤ t := by
  refine le_trans (term_approx_tight d b b3 bz cz n) ?_
  rw [sub_le_iff_le_add, ← Real.rpow_inv_le_iff_of_neg (by linarith) (by bound) (by bound), inv_div,
    div_neg, div_one]
  refine le_trans ?_ (le_trans crunch (by bound))
  rw [← Real.rpow_intCast, Int.cast_neg, Int.cast_pow, Int.cast_two]
  bound

-- Weak `term` bounds for `4 ≤ ‖z‖`
lemma term_approx_4_0 (d : ℕ) [Fact (2 ≤ d)] (bz : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 0 z⁻¹ - 1‖ ≤ 0.1548 := term_approx_const bz cz
lemma term_approx_4_1 (d : ℕ) [Fact (2 ≤ d)] (bz : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 1 z⁻¹ - 1‖ ≤ 0.0071 := term_approx_const bz cz
lemma term_approx_4_2 (d : ℕ) [Fact (2 ≤ d)] (bz : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 2 z⁻¹ - 1‖ ≤ 0.00003 := term_approx_const bz cz
lemma term_approx_4_3 (d : ℕ) [Fact (2 ≤ d)] (bz : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 3 z⁻¹ - 1‖ ≤ 0.00001 := term_approx_const bz cz

-- Weak `term` bounds for `5 ≤ ‖z‖`
lemma term_approx_5_0 (d : ℕ) [Fact (2 ≤ d)] (bz : 5 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 0 z⁻¹ - 1‖ ≤ 0.1181 := term_approx_const bz cz
lemma term_approx_5_1 (d : ℕ) [Fact (2 ≤ d)] (bz : 5 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 1 z⁻¹ - 1‖ ≤ 0.0032 := term_approx_const bz cz
lemma term_approx_5_2 (d : ℕ) [Fact (2 ≤ d)] (bz : 5 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 2 z⁻¹ - 1‖ ≤ 0.00001 := term_approx_const bz cz
lemma term_approx_5_3 (d : ℕ) [Fact (2 ≤ d)] (bz : 5 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 3 z⁻¹ - 1‖ ≤ 0.00001 := term_approx_const bz cz

/-- Monomial version of `term_approx_tight`, based on computable bounds -/
lemma term_approx_pow {d n : ℕ} [Fact (2 ≤ d)] {b t zp : ℝ} {c z : ℂ} (bz : b ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) (t0 : 0 < t := by norm_num) (b3 : 3 < b := by norm_num)
    (crunch : ((t / b ^ (2 ^ (n + 1) - 1) + 1) ^ 2 ^ (n + 1))⁻¹ ≤ 1 - b * (fb 2 b)^[n] b⁻¹ ^ 2 := by
      norm_num [fb, factor])
    (zpn : zp = ‖z‖⁻¹ ^ (2 ^ (n + 1) - 1) := by simp) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤ t * zp := by
  simp only [zpn]
  refine le_trans (term_approx_tight_cz d (by linarith) cz n) ?_
  refine le_trans (term_mono_d d (norm_nonneg _) (le_trans b3.le bz) cz n) ?_
  refine le_trans (Real.one_sub_rpow_neg_sub_one_le_linear (y := b * (fb 2 b)^[n] b⁻¹ ^ 2)
    (by bound) ?_ (by bound) (by bound)) ?_
  · apply fb_mono_cz_strong 2 b3.le bz cz
  · refine le_trans (mul_le_mul_of_nonneg_left (fb_le_factor 2 b3.le (norm_nonneg _) bz cz n)
      (by bound)) ?_
    simp only [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by bound)
    rw [← le_div_iff₀ (by bound), div_le_iff₀ (by bound), sub_le_iff_le_add]
    have e : (2 : ℝ) ^ (n + 1) = (2 ^ (n + 1) : ℕ) := by simp
    rw [neg_div, one_div, neg_inv, Real.rpow_inv_le_iff_of_neg (by bound) (by bound) (by bound),
      Real.rpow_neg (by bound), e, Real.rpow_natCast]
    rw [factor_eq_div (by positivity)]
    simp only [inv_pow, div_eq_mul_inv, inv_inv, mul_pow, mul_inv, ← pow_mul, ← pow_succ]
    generalize hu : (fb 2 b)^[n] b⁻¹ ^ 2 = u at crunch
    have b0 : 0 < b := by bound
    have u0 : 0 < u := by bound
    simp only [← mul_assoc, mul_comm _ u]
    simp only [← mul_assoc, mul_comm _ u⁻¹, inv_mul_cancel₀ u0.ne', one_mul]
    rw [pow_sub₀ _ b0.ne' (by bound), pow_one, div_eq_mul_inv, mul_inv, inv_inv, ← mul_assoc,
      mul_comm _ u] at crunch
    exact crunch

-- Strong `term` bounds for `4 ≤ ‖z‖`
def term_bounds_4 (z : ℂ) : Fin 6 → ℝ :=
  ![0.619 * ‖z‖⁻¹, 0.453 * ‖z‖⁻¹ ^ 3, 0.419 * ‖z‖⁻¹ ^ 7, 0.700 * ‖z‖⁻¹ ^ 15, 3.91 * ‖z‖⁻¹ ^ 31,
    245 * ‖z‖⁻¹ ^ 63]
lemma term_approx_pow_4 (d : ℕ) [Fact (2 ≤ d)] (bz : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (n : Fin 6) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤ term_bounds_4 z n := by
  fin_cases n <;> exact term_approx_pow bz cz

-- Strong `term` bounds for `5 ≤ ‖z‖`
lemma term_approx_pow_5_0 (d : ℕ) [Fact (2 ≤ d)] (bz : 5 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 0 z⁻¹ - 1‖ ≤ 0.591 * ‖z‖⁻¹ := term_approx_pow bz cz
lemma term_approx_pow_5_1 (d : ℕ) [Fact (2 ≤ d)] (bz : 5 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 1 z⁻¹ - 1‖ ≤ 0.394 * ‖z‖⁻¹ ^ 3 := term_approx_pow bz cz
lemma term_approx_pow_5_2 (d : ℕ) [Fact (2 ≤ d)] (bz : 5 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 2 z⁻¹ - 1‖ ≤ 0.313 * ‖z‖⁻¹ ^ 7 := term_approx_pow bz cz
lemma term_approx_pow_5_3 (d : ℕ) [Fact (2 ≤ d)] (bz : 5 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 3 z⁻¹ - 1‖ ≤ 0.392 * ‖z‖⁻¹ ^ 15 := term_approx_pow bz cz

-- Strong `term` bounds for `6, 7, 8, 9 ≤ ‖z‖`
lemma term_approx_pow_6_0 (d : ℕ) [Fact (2 ≤ d)] (bz : 6 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 0 z⁻¹ - 1‖ ≤ 0.573 * ‖z‖⁻¹ := term_approx_pow bz cz
lemma term_approx_pow_7_0 (d : ℕ) [Fact (2 ≤ d)] (bz : 7 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 0 z⁻¹ - 1‖ ≤ 0.561 * ‖z‖⁻¹ := term_approx_pow bz cz
lemma term_approx_pow_8_0 (d : ℕ) [Fact (2 ≤ d)] (bz : 8 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 0 z⁻¹ - 1‖ ≤ 0.553 * ‖z‖⁻¹ := term_approx_pow bz cz
lemma term_approx_pow_9_0 (d : ℕ) [Fact (2 ≤ d)] (bz : 9 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 0 z⁻¹ - 1‖ ≤ 0.546 * ‖z‖⁻¹ := term_approx_pow bz cz

-- Strong `term` bounds for `10 ≤ ‖z‖`
def term_bounds_10 (z : ℂ) : Fin 6 → ℝ :=
  ![0.541 * ‖z‖⁻¹, 0.309 * ‖z‖⁻¹ ^ 3, 0.191 * ‖z‖⁻¹ ^ 7, 0.146 * ‖z‖⁻¹ ^ 15, 0.171 * ‖z‖⁻¹ ^ 31,
    0.465 * ‖z‖⁻¹ ^ 63]
lemma term_approx_pow_10 (d : ℕ) [Fact (2 ≤ d)] (bz : 10 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (n : Fin 6) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤ term_bounds_10 z n := by
  fin_cases n <;> exact term_approx_pow bz cz

/-- `s.bottcher c z = z⁻¹ + O(z⁻¹ ^ 2)` -/
theorem bottcher_approx_z (d : ℕ) [Fact (2 ≤ d)] (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖(superF d).bottcher c z - z⁻¹‖ ≤ 0.943 * ‖z‖⁻¹ ^ 2 := by
  set s := superF d
  have zi4 : ‖z‖⁻¹ ≤ 4⁻¹ := by bound
  simp only [bottcher_eq_bottcherNear_z z4 cz, bottcherNear, norm_mul, ← mul_sub_one,
    pow_two, ← mul_assoc, norm_inv, mul_comm ‖z‖⁻¹]
  refine mul_le_mul_of_nonneg_right ?_ (by bound)
  obtain ⟨p, h⟩ := term_prod_exists (superNearF d c) _ (inv_mem_t (by linarith) cz)
  rw [h.tprod_eq]
  refine le_trans (h.norm_sub_one_le (term_approx_pow_4 d z4 cz) (c := 2 * ‖z‖⁻¹) (a := 2⁻¹) ?_ ?_
    (by norm_num) (by norm_num) (by norm_num) ?_) ?_
  · exact fun _ _ ↦ le_trans (term_approx d (by linarith) cz _) (le_of_eq (by ring))
  · intro k
    fin_cases k <;> simp only [term_bounds_4] <;> bound
  · ring_nf
    linarith
  · simp only [term_bounds_4, Finset.prod_fin_eq_prod_range, Finset.prod_range_succ,
      Finset.range_one, Finset.prod_singleton, Nat.ofNat_pos, ↓reduceDIte, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, Nat.one_lt_ofNat, Fin.mk_one, Matrix.cons_val_one, Nat.reduceLT,
      Fin.reduceFinMk, Matrix.cons_val, Nat.lt_add_one, tsub_le_iff_right]
    have z0 : 0 < ‖z‖⁻¹ := by bound
    generalize ‖z‖⁻¹ = x at z0 z4 zi4
    have pow : ∀ k : Fin 122, x ^ (k + 1 : ℕ) ≤ 4⁻¹ ^ (k : ℕ) * x := by
      intro k; simp only [pow_succ]; bound
    simp only [inv_pow, Fin.forall_iff_castSucc, Fin.reduceLast, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
      Nat.reduceAdd, Fin.val_castSucc, pow_one, Fin.val_eq_zero, zero_add, pow_zero, inv_one,
      one_mul, le_refl, implies_true, and_true] at pow
    ring_nf
    linarith

/-- `s.bottcher c z = z⁻¹ + O(z⁻¹ ^ 2)` -/
theorem bottcher_approx_z_10 (d : ℕ) [Fact (2 ≤ d)] (z10 : 10 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖(superF d).bottcher c z - z⁻¹‖ ≤ 0.849 * ‖z‖⁻¹ ^ 2 := by
  set s := superF d
  have z4 : 4 ≤ ‖z‖ := by linarith
  have zi4 : ‖z‖⁻¹ ≤ 4⁻¹ := by bound
  simp only [bottcher_eq_bottcherNear_z z4 cz, bottcherNear, norm_mul, ← mul_sub_one,
    pow_two, ← mul_assoc, norm_inv, mul_comm ‖z‖⁻¹]
  refine mul_le_mul_of_nonneg_right ?_ (by bound)
  obtain ⟨p, h⟩ := term_prod_exists (superNearF d c) _ (inv_mem_t (by linarith) cz)
  rw [h.tprod_eq]
  refine le_trans (h.norm_sub_one_le (term_approx_pow_10 d z10 cz) (c := 2 * ‖z‖⁻¹) (a := 2⁻¹) ?_ ?_
    (by norm_num) (by norm_num) (by norm_num) ?_) ?_
  · exact fun _ _ ↦ le_trans (term_approx d (by linarith) cz _) (le_of_eq (by ring))
  · intro k
    fin_cases k <;> simp only [term_bounds_10] <;> bound
  · ring_nf
    linarith
  · simp only [term_bounds_10, Finset.prod_fin_eq_prod_range, Finset.prod_range_succ,
      Finset.range_one, Finset.prod_singleton, Nat.ofNat_pos, ↓reduceDIte, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, Nat.one_lt_ofNat, Fin.mk_one, Matrix.cons_val_one, Nat.reduceLT,
      Fin.reduceFinMk, Matrix.cons_val, Nat.lt_add_one, tsub_le_iff_right]
    have z0 : 0 < ‖z‖⁻¹ := by bound
    generalize ‖z‖⁻¹ = x at z0 z4 zi4
    have pow : ∀ k : Fin 122, x ^ (k + 1 : ℕ) ≤ 4⁻¹ ^ (k : ℕ) * x := by
      intro k; simp only [pow_succ]; bound
    simp only [inv_pow, Fin.forall_iff_castSucc, Fin.reduceLast, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
      Nat.reduceAdd, Fin.val_castSucc, pow_one, Fin.val_eq_zero, zero_add, pow_zero, inv_one,
      one_mul, le_refl, implies_true, and_true] at pow
    ring_nf
    linarith

/-- `bottcher' d c = c⁻¹ + O(c⁻¹^2)` -/
theorem bottcher_approx (d : ℕ) [Fact (2 ≤ d)] (c4 : 4 ≤ ‖c‖) :
    ‖bottcher' d c - c⁻¹‖ ≤ 0.943 * ‖c‖⁻¹ ^ 2 :=
  bottcher_approx_z d c4 (le_refl _)

/-- `s.potential c z = ‖z‖⁻¹ + O(‖z‖⁻¹ ^ 2)` -/
theorem potential_approx_strong (d : ℕ) [Fact (2 ≤ d)] (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    |(superF d).potential c z - ‖z‖⁻¹| ≤ 0.943 * ‖z‖⁻¹ ^ 2 := by
  rw [← (superF d).norm_bottcher, ← norm_inv]
  exact le_trans (abs_norm_sub_norm_le _ _)
    (by simpa only [norm_inv] using bottcher_approx_z d z4 cz)

/-- `s.potential c z = ‖z‖⁻¹ + O(‖z‖⁻¹ ^ 2)` -/
theorem potential_approx_strong_10 (d : ℕ) [Fact (2 ≤ d)] (z10 : 10 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    |(superF d).potential c z - ‖z‖⁻¹| ≤ 0.849 * ‖z‖⁻¹ ^ 2 := by
  rw [← (superF d).norm_bottcher, ← norm_inv]
  exact le_trans (abs_norm_sub_norm_le _ _)
    (by simpa only [norm_inv] using bottcher_approx_z_10 d z10 cz)

@[simp] lemma bottcher_inv_zero : bottcher_inv d 0 = 0 := by
  simp only [bottcher_inv_def, coe_zero, inv_zero', bottcher_inf]

/-- bottcher is monic at `∞` (has derivative 1) -/
theorem bottcher_hasDerivAt_one : HasDerivAt (bottcher_inv d) 1 0 := by
  rw [hasDerivAt_iff_isLittleO]
  simp only [bottcher_inv_zero, sub_zero, smul_eq_mul, mul_one]
  rw [Asymptotics.isLittleO_iff]
  intro k k0; rw [Metric.eventually_nhds_iff]
  refine ⟨min 16⁻¹ (k / 16), by bound, ?_⟩; intro z le
  simp only [dist_eq_norm, sub_zero, lt_min_iff] at le
  by_cases z0 : z = 0
  · simp only [z0, bottcher_inv_zero, sub_zero, norm_zero,
      MulZeroClass.mul_zero, le_refl]
  simp only [bottcher_inv_def, bottcher, inv_coe z0, fill_coe]
  have b := bottcher_approx d (c := z⁻¹) ?_
  · simp only [inv_inv] at b; apply le_trans b
    simp only [norm_inv, inv_inv, pow_two, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc 0.943 * ‖z‖
      _ ≤ 16 * (k / 16) := by linarith [le.2]
      _ = k := by ring
  · rw [norm_inv, le_inv_comm₀ (by norm_num) (norm_pos_iff.mpr z0)]
    linarith

/-- bottcher is nonsingular at `∞` -/
theorem bottcher_mfderiv_inf_ne_zero : mfderiv I I (bottcher d) ∞ ≠ 0 := by
  simp only [mfderiv, (bottcherMAnalytic d _ multibrotExt_inf).mdifferentiableAt (by decide), if_pos,
    writtenInExtChartAt, bottcher_inf, extChartAt_inf, extChartAt_eq_refl, Function.comp_def,
    PartialEquiv.refl_coe, id, PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, invEquiv_apply,
    RiemannSphere.inv_inf, coePartialEquiv_symm_apply, toComplex_zero, PartialEquiv.coe_trans_symm,
    PartialEquiv.symm_symm, coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply, invEquiv_symm,
    ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  rw [← bottcher_inv_def, bottcher_hasDerivAt_one.hasFDerivAt.fderiv]
  intro h
  have h1 : (ContinuousLinearMap.toSpanSingleton ℂ (1 : ℂ)) (1 : ℂ) = 0 :=
    ContinuousLinearMap.ext_iff.mp h (1 : ℂ)
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_one] at h1
  exact one_ne_zero h1

end
end Ray_Ray_Multibrot_Bottcher

-- ===== Ray.Multibrot.Isomorphism =====
section Ray_Ray_Multibrot_Isomorphism
/-!
## Böttcher coordinates form an isomorphism between the exterior Multibrot set and the unit disk

We show that

1. `(c,c)` is postcritical for each `c` not in the Multibrot set.  To see this, note that `0` and
   `∞` are the only critical points of `f z = z^d + c`, and `c` is postcritical since it is the
   image of `0` (and thus has smaller potential).
2. Therefore, the diagonal Böttcher map `bottcher d c = s.bottcher c c` is analytic throughout
   the exterior of the Multibrot set.
3. `bottcher d` is nontrivial throughout the exterior of the Multibrot set, as otherwise triviality
   spreads throughout `(OnePoint ℂ)`.
4. `bottcher d` bijects from the exterior of the Multibrot set to `ball 0 1`.
5. There is an explicit, analytic homeomorphism `bottcherHomeomorph d` from the exterior of the
   Multibrot set to `ball 0 1`.

Connectivity of the Multibrot set and its complement are easy consequences of (5); see
`Multibrot/Connected.lean` and `Mandelbrot.lean`.
-/

open Complex
open Filter (Tendsto atTop)
open Function (uncurry)
open Metric (ball closedBall isOpen_ball mem_ball_self mem_ball mem_closedBall mem_closedBall_self)
open Real (exp log)
open RiemannSphere
open OneDimension
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-!
## Injectivity of Böttcher coordinates
-/

/-- `bottcher d` is injective.

    We use induction on potential down 0, expressed using closed sets of pairs.  Intuitively,
    1. Near 0, `bottcher d` is injective since it is noncritical.
    2. The set of potentials with an injectivity counterexample is open.
    3. A limit of counterexamples is either already a counterexample, or shows that `bottcher d`
       is critical at the limit.
    4. But every value is repeated near critical points of analytic functions, so in particular
       smaller values are repeated, which gives us a smaller potential counterexample. -/
theorem bottcher_inj : InjOn (bottcher d) (multibrotExt d) := by
  -- We operate by induction on potential down to 0, expressed using closed sets of pairs.
  -- Preliminaries first:
  by_contra bad
  simp only [InjOn, not_forall, ← ne_eq] at bad
  rcases bad with ⟨x, xm, y, ym, bxy, xy⟩
  generalize hb : potential d x = b
  have b1 : b < 1 := by rwa [← hb, potential_lt_one]
  set u := {c | potential d c ≤ b}
  set t0 := u ×ˢ u
  set t1 := {q : (OnePoint ℂ) × (OnePoint ℂ) | bottcher d q.1 = bottcher d q.2 ∧ q ∈ t0}
  set t2 := {q : (OnePoint ℂ) × (OnePoint ℂ) | q.1 ≠ q.2 ∧ q ∈ t1}
  have t2ne : t2.Nonempty := by
    refine ⟨⟨x, y⟩, xy, bxy, ?_, ?_⟩
    · simp only [mem_ofPred, ← hb, le_refl, u]
    · simp only [mem_ofPred, ← hb, ← norm_bottcher, bxy, le_refl, u]
  clear x xm y ym bxy xy hb
  have ue : u ⊆ multibrotExt d := by intro c m; rw [← potential_lt_one]; exact lt_of_le_of_lt m b1
  have t01 : t1 ⊆ t0 := inter_subset_right
  have t12 : t2 ⊆ t1 := inter_subset_right
  have uc : IsClosed u := isClosed_le potential_continuous continuous_const
  have t0c : IsClosed t0 := uc.prod uc
  have t1c : IsClosed t1 := by
    rw [isClosed_iff_frequently]; intro ⟨x, y⟩ f
    have m0 : (x, y) ∈ t0 :=
      Filter.Frequently.mem_of_closed (f.mp (.of_forall fun _ m ↦ t01 m)) t0c
    refine ⟨tendsto_nhds_unique_of_frequently_eq ?_ ?_
      (f.mp (.of_forall fun _ m ↦ m.1)), m0⟩
    · exact (bottcherMAnalytic d _ (ue m0.1)).continuousAt.comp continuousAt_fst
    · exact (bottcherMAnalytic d _ (ue m0.2)).continuousAt.comp continuousAt_snd
  have t12' : closure t2 ⊆ t1 := by rw [← t1c.closure_eq]; exact closure_mono t12
  have t2c' : IsCompact (closure t2) := isClosed_closure.isCompact
  have t2ne' : (closure t2).Nonempty := t2ne.closure
  -- Find the smallest potential which (almost) violates injectivity,
  -- and a pair (x,y) which realizes it
  have pc : Continuous fun q : (OnePoint ℂ) × (OnePoint ℂ) ↦ potential d q.1 := potential_continuous.comp continuous_fst
  rcases t2c'.exists_isMinOn t2ne' pc.continuousOn with ⟨⟨x, y⟩, m2, min⟩
  simp only [isMinOn_iff] at min
  generalize xp : potential d x = p; rw [xp] at min
  have m1 := t12' m2
  have pb : p ≤ b := by rw [← xp]; exact m1.2.1
  have xm : x ∈ multibrotExt d := ue m1.2.1
  have ym : y ∈ multibrotExt d := ue m1.2.2
  have yp : potential d y = p := by rw [← norm_bottcher, ← m1.1, norm_bottcher, xp]
  have p0i : p = 0 → x = ∞ ∧ y = ∞ := by intro p0; rw [p0, potential_eq_zero] at xp yp; use xp, yp
  -- Split into three cases to find a contradiction
  by_cases xy : x ≠ y
  · -- Case 1: If x ≠ y, we can move a bit downwards in potential
    have p0 : p ≠ 0 := by
      contrapose xy; rcases p0i xy with ⟨xi, yi⟩; rw [xi, yi]
    have f : ∃ᶠ q : ℂ × ℂ in Filter.map
        (fun q : (OnePoint ℂ) × (OnePoint ℂ) ↦ (bottcher d q.1, bottcher d q.2)) (𝓝 (x, y)),
        q.1 = q.2 ∧ ‖q.1‖ < p := by
      rw [nhds_prod_eq, ← Filter.prod_map_map_eq, ← (bottcherNontrivial xm).nhds_eq_map_nhds, ←
        (bottcherNontrivial ym).nhds_eq_map_nhds, m1.1, ← nhds_prod_eq]
      apply (continuous_id.prodMk continuous_id).continuousAt.frequently
      simp only [true_and, ← yp, ← norm_bottcher]; apply frequently_smaller
      rw [← norm_ne_zero_iff, norm_bottcher, yp]; exact p0
    simp only [Filter.frequently_map] at f
    rcases(f.and_eventually (Ne.eventually_ne xy)).exists with ⟨⟨v, w⟩, ⟨bvw, pv⟩, vw⟩
    simp only [norm_bottcher] at vw bvw pv ⊢
    have pw : potential d w < p := by rwa [← norm_bottcher, ← bvw, norm_bottcher]
    have m : (v, w) ∈ t2 := ⟨vw, bvw, le_trans pv.le pb, le_trans pw.le pb⟩
    contrapose pv; clear pv; simp only [not_lt]; exact min ⟨v, w⟩ (subset_closure m)
  -- x = y, so we're at a singular point
  simp only [not_not] at xy
  rw [← xy] at m1 m2 p0i; clear xy ym yp y
  have db : mfderiv I I (bottcher d) x = 0 := by
    contrapose m2; simp only [mem_closure_iff_frequently, Filter.not_frequently]
    refine ((bottcherMAnalytic d _ xm).local_inj m2).mp (.of_forall ?_)
    intro ⟨x, y⟩ inj ⟨xy, e, _⟩; simp only at xy e inj; exact xy (inj e)
  by_cases p0 : p ≠ 0
  · -- Case 2: At a singular point we're not locally injective,
    -- so we can find a smaller potential value
    rcases not_local_inj_of_mfderiv_zero (bottcherMAnalytic d _ xm) db with ⟨r, ra, rx, e⟩
    simp only [eventually_nhdsWithin_iff, mem_compl_singleton_iff] at e
    rw [← xp, ← norm_bottcher, norm_ne_zero_iff] at p0
    have h := frequently_smaller p0
    rw [(bottcherNontrivial xm).nhds_eq_map_nhds, Filter.frequently_map] at h
    have m : ∃ᶠ z in 𝓝 x, potential d z < p ∧ (z, r z) ∈ t2 := by
      refine h.mp (e.mp (.of_forall fun z e lt ↦ ?_))
      have zx : z ≠ x := by
        contrapose lt; simp only [not_lt] at lt ⊢; simp only [lt, le_refl]
      rw [norm_bottcher, norm_bottcher, xp] at lt
      rcases e zx with ⟨rz, e⟩
      refine ⟨lt, rz.symm, e.symm, le_trans lt.le pb, ?_⟩
      rw [← norm_bottcher, ← e, norm_bottcher] at lt; exact le_trans lt.le pb
    rcases m.exists with ⟨y, yp, m⟩
    linarith [min _ (subset_closure m)]
  · -- Case 1: x = ∞, which we know is nonsingular
    simp only [not_not] at p0; rw [(p0i p0).1] at db
    exact bottcher_mfderiv_inf_ne_zero db

@[simp] lemma bottcher_coe_ne_zero : bottcher d c ≠ 0 := by
  by_cases m : ↑c ∈ multibrotExt d
  · rw [← bottcher_inf (d := d)]
    exact bottcher_inj.ne m (by simp) (by simp)
  · simp only [← potential_lt_one, not_lt] at m
    rw [← norm_ne_zero_iff, norm_bottcher]
    linarith

lemma bottcher_inj' : InjOn (bottcher' d) (multibrot d)ᶜ := by
  intro a am b bm e
  simp only [mem_compl_iff, ← multibrotExt_coe] at am bm
  simpa using bottcher_inj (d := d) am bm (by simp [bottcher, e])

lemma deriv_bottcher_ne_zero (m : c ∉ multibrot d) : deriv (bottcher' d) c ≠ 0 :=
  bottcher_inj'.deriv_ne_zero isCompact_multibrot.isClosed.isOpen_compl m (bottcher_analytic _ m)

/-!
## The external ray map, and `bottcherHomeomorph`
-/

lemma ray_exists (d : ℕ) [Fact (2 ≤ d)] :
    ∃ g, ContMDiffOnNhd I I g (bottcher d '' multibrotExt d) ∧
      ∀ z : (OnePoint ℂ), z ∈ multibrotExt d → g (bottcher d z) = z :=
  global_complex_inverse_fun_open' (bottcherMAnalytic d).contMDiffOn bottcher_inj
    isOpen_multibrotExt

/-- The inverse to `bottcher d`, defining external rays throughout the exterior -/
def ray (d : ℕ) [Fact (2 ≤ d)] : ℂ → (OnePoint ℂ) :=
  Classical.choose (ray_exists d)

/-- `ray` as an analytic `ℂ → ℂ` function -/
def inv_ray (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ :=
  fun z ↦ (ray d z)⁻¹.toComplex

/-- The function we need to plug into Grönwall's area theorem: `z / inv_ray d` -/
def pray (d : ℕ) [Fact (2 ≤ d)] (z : ℂ) : ℂ :=
  (dslope (inv_ray d) 0 z)⁻¹

/-- `ray d` is analytic on `ball 0 1` -/
theorem rayMAnalytic (d : ℕ) [Fact (2 ≤ d)] : ContMDiffOnNhd I I (ray d) (ball 0 1) := by
  rw [← bottcher_surj d]; exact (Classical.choose_spec (ray_exists d)).1

/-- `ray d` is the left inverse to `bottcher d` -/
theorem ray_bottcher {c : (OnePoint ℂ)} (m : c ∈ multibrotExt d) : ray d (bottcher d c) = c :=
  (Classical.choose_spec (ray_exists d)).2 _ m

/-- `ray d` is the right inverse to `bottcher d` -/
theorem bottcher_ray {z : ℂ} (m : z ∈ ball (0 : ℂ) 1) : bottcher d (ray d z) = z := by
  rw [← bottcher_surj d] at m; rcases m with ⟨c, m, cz⟩
  nth_rw 1 [← cz]; rw [ray_bottcher m]; exact cz

/-- `ray d` surjects from `ball 0 1` to the exterior of the Multibrot set -/
theorem ray_surj (d : ℕ) [Fact (2 ≤ d)] : ray d '' ball 0 1 = multibrotExt d := by
  rw [← bottcher_surj d]; apply Set.ext; intro c; simp only [← image_comp, mem_image]; constructor
  · intro ⟨e, m, ec⟩; simp only [Function.comp, ray_bottcher m] at ec; rwa [← ec]
  · intro m; use c, m, ray_bottcher m

/-- `bottcher d` as an (analytic) homeomorphism from `multibrotExt d` to `ball 0 1` -/
def bottcherHomeomorph (d : ℕ) [Fact (2 ≤ d)] : OpenPartialHomeomorph (OnePoint ℂ) ℂ where
  toFun := bottcher d
  invFun := ray d
  source := multibrotExt d
  target := ball 0 1
  map_source' := by intro c m; simp only [← bottcher_surj d]; exact mem_image_of_mem _ m
  map_target' := by intro z m; simp only [← ray_surj d]; exact mem_image_of_mem _ m
  left_inv' c m := ray_bottcher m
  right_inv' z m := bottcher_ray m
  open_source := isOpen_multibrotExt
  open_target := isOpen_ball
  continuousOn_toFun := (bottcherMAnalytic d).continuousOn
  continuousOn_invFun := (rayMAnalytic d).continuousOn

lemma ray_inj : InjOn (ray d) (ball (0 : ℂ) 1) :=
  (bottcherHomeomorph d).symm.injOn

lemma ray_mem_multibrotExt {z : ℂ} (m : z ∈ ball (0 : ℂ) 1) : ray d z ∈ multibrotExt d :=
  (bottcherHomeomorph d).map_target m

@[simp] lemma ray_zero : ray d 0 = ∞ := by
  simpa only [bottcher_inf] using ray_bottcher (d := d) (c := ∞) (by simp)

@[simp] lemma ray_ne_zero {z : ℂ} (m : z ∈ ball (0 : ℂ) 1) : ray d z ≠ 0 := by
  have h := (bottcherHomeomorph d).map_target m
  contrapose h
  simp [bottcherHomeomorph, h]

@[simp] lemma ray_eq_inf {z : ℂ} (m : z ∈ ball (0 : ℂ) 1) : ray d z = ∞ ↔ z = 0 := by
  rw [← ray_zero (d := d)]
  exact ray_inj.eq_iff m (by simp)

@[simp] lemma norm_bottcher_lt_one {z : (OnePoint ℂ)} (m : z ∈ multibrotExt d) : ‖bottcher d z‖ < 1 := by
  simpa [bottcherHomeomorph] using (bottcherHomeomorph d).map_source m

end
end Ray_Ray_Multibrot_Isomorphism

-- ===== Ray.Multibrot.Connected =====
section Ray_Ray_Multibrot_Connected
/-!
## The Multibrot set and its complement are connected

`bottcherHomeomorph` from `Multibrot.lean` is an analytic homeomorphism from the exterior of the
Multibrot set (with `∞` included) to `ball 0 1`.  From this, the exterior is immediately (path)
connected: it's a ball.  But also the Multibrot set itself is connected, since it is the downward
intersection of compact, connected sets (the levelsets of `potential d`).
-/

open Complex
open Filter (Tendsto atTop)
open Function (uncurry)
open Metric (ball sphere closedBall isOpen_ball mem_ball_self mem_ball mem_closedBall
  mem_closedBall_self mem_sphere)
open Real (exp log)
open RiemannSphere
open Set
open scoped OnePoint RiemannSphere Topology Real
noncomputable section

variable {c : ℂ}

-- Fix d ≥ 2
variable {d : ℕ} [Fact (2 ≤ d)]

/-- `multibrotExt` is path connected -/
theorem isPathConnected_multibrotExt (d : ℕ) [Fact (2 ≤ d)] :
    IsPathConnected (multibrotExt d) := by
  rw [← ray_surj d]; apply IsPathConnected.image_of_continuousOn
  exact (convex_ball _ _).isPathConnected (Metric.nonempty_ball.mpr one_pos)
  exact (rayMAnalytic d).continuousOn

/-- Levelsets of `potential d` are connected -/
theorem isPathConnected_potential_levelset (p : ℝ) (p0 : 0 ≤ p) (p1 : p < 1) :
    IsPathConnected (potential d ⁻¹' {p}) := by
  have e : potential d ⁻¹' {p} = ray d '' sphere 0 p := by
    apply Set.ext; intro c
    simp only [mem_preimage, mem_singleton_iff, ← norm_bottcher, mem_image, mem_sphere,
      Complex.dist_eq, sub_zero]
    constructor
    · intro h; use bottcher d c; use h; rw [ray_bottcher]
      rw [← potential_lt_one, ← norm_bottcher, h]; exact p1
    · intro ⟨e, ep, ec⟩; rw [← ec, bottcher_ray]; exact ep
      simp only [mem_ball, Complex.dist_eq, sub_zero, ep, p1]
  rw [e]; apply (isPathConnected_sphere p0).image_of_continuousOn
  exact (rayMAnalytic d).continuousOn.mono (Metric.sphere_subset_ball p1)

/-- `(multibrotEext d)ᶜ` is connected, since it is the downward intersection of the compact,
    connected sets `potential d ⁻¹' (Ici p)`. -/
theorem isConnected_compl_multibrotExt (d : ℕ) [Fact (2 ≤ d)] :
    IsConnected (multibrotExt d)ᶜ := by
  refine ⟨⟨((0 : ℂ) : (OnePoint ℂ)),?_⟩,?_⟩
  · simp only [mem_compl_iff, multibrotExt_coe, not_not, multibrot_zero]
  have e : (multibrotExt d)ᶜ = ⋂ p : Ico 0 (1 : ℝ), potential d ⁻¹' Ici p := by
    apply Set.ext; intro z
    simp only [mem_compl_iff, ← potential_lt_one, mem_iInter, mem_preimage, not_lt, mem_Ici]
    constructor; intro p1 ⟨q, m⟩; simp only [mem_Ico] at m ⊢; linarith
    intro h; contrapose h; simp only [not_le, not_forall] at h ⊢
    rcases exists_between h with ⟨y, py, y1⟩
    exact ⟨⟨y, ⟨le_trans potential_nonneg py.le, y1⟩⟩, py⟩
  rw [e]; refine @IsPreconnected.directed_iInter _ _ _ _ ?_ _ ?_ ?_ ?_
  · exact Zero.instNonempty
  · intro ⟨a, a0, a1⟩ ⟨b, b0, b1⟩
    refine ⟨⟨max a b, mem_Ico.mpr ⟨le_max_of_le_left a0, max_lt a1 b1⟩⟩, ?_, ?_⟩
    · intro z h; simp only [mem_preimage, mem_Ici, max_le_iff] at h ⊢; exact h.1
    · intro z h; simp only [mem_preimage, mem_Ici, max_le_iff] at h ⊢; exact h.2
  · intro ⟨p, m⟩; simp only
    refine IsConnected.isPreconnected (IsPathConnected.isConnected ?_)
    apply IsPathConnected.of_frontier
    · rw [frontier_Ici]; exact isPathConnected_potential_levelset _ m.1 m.2
    · exact potential_continuous
    · exact isClosed_Ici
  · intro ⟨p, m⟩; exact (isClosed_Ici.preimage potential_continuous).isCompact

/-- `multibrot d` is connected -/
theorem isConnected_multibrot (d : ℕ) [Fact (2 ≤ d)] : IsConnected (multibrot d) := by
  have e : _root_.multibrot d = (fun z : (OnePoint ℂ) ↦ z.toComplex) '' (multibrotExt d)ᶜ := by
    apply Set.ext; intro z; simp only [mem_image, mem_compl_iff]; constructor
    intro m; use z
    simp only [multibrotExt_coe, not_not, m, toComplex_coe, true_and]
    intro ⟨w, m, wz⟩; induction w using OnePoint.rec
    · contrapose m; clear m; simp only [multibrotExt_inf]
    · simp only [multibrotExt_coe, not_not, toComplex_coe] at m wz; rwa [← wz]
  rw [e]; apply (isConnected_compl_multibrotExt d).image
  refine continuousOn_toComplex.mono ?_; intro z m
  contrapose m; simp only [mem_compl_iff, mem_singleton_iff, not_not] at m
  simp only [m, notMem_compl_iff, multibrotExt_inf]

/-- `(multibrot d)ᶜ` is connected -/
theorem isConnected_compl_multibrot (d : ℕ) [Fact (2 ≤ d)] :
    IsConnected (_root_.multibrot d)ᶜ := by
  have dc : IsConnected (multibrotExt d \ {∞}) := by
    refine ⟨⟨(((3 : ℝ) : ℂ) : (OnePoint ℂ)),?_⟩,?_⟩
    constructor
    · simp only [multibrotExt_coe]; apply multibrot_two_lt
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]; norm_num; norm_num
    · simp only [mem_singleton_iff, coe_ne_inf, not_false_iff]
    · exact (isPathConnected_multibrotExt d).isConnected.isPreconnected.open_diff_singleton
        isOpen_multibrotExt _
  have e : (_root_.multibrot d)ᶜ = (fun z : (OnePoint ℂ) ↦ z.toComplex) '' (multibrotExt d \ {∞}) := by
    apply Set.ext; intro z; simp only [mem_compl_iff, mem_image]; constructor
    · intro m; use z
      simp only [multibrotExt_coe, m, toComplex_coe, not_false_iff, mem_sdiff, and_true,
        mem_singleton_iff, coe_ne_inf]
    · intro ⟨w, ⟨m, wi⟩, wz⟩; induction w using OnePoint.rec
      · contrapose wi; clear wi; simp only [mem_singleton_iff]
      · simp only [multibrotExt_coe, toComplex_coe] at m wz; rwa [← wz]
  rw [e]; apply dc.image
  refine continuousOn_toComplex.mono ?_; intro z ⟨_, i⟩
  simp only [mem_singleton_iff, mem_compl_iff] at i ⊢; exact i

end
end Ray_Ray_Multibrot_Connected

-- ===== Ray.Mandelbrot =====
section Ray_Ray_Mandelbrot
/-!
## The Mandelbrot set and its complement are connected

The rest of our proof works via manifolds and other machinery.  Here we strip that away:

1. We define the Mandebrot set directly
2. We show it is equal to `multibrot 2`
3. Thus, the Mandelbrot set and its complement are connected
-/

open Filter (Tendsto atTop)
open RiemannSphere
open Set
open scoped Topology Real
noncomputable section

/-- The Mandelbrot set: all points that do not escape to `∞` under `z ↦ z^2 + c` -/
def mandelbrot : Set ℂ :=
  {c | ¬Tendsto (fun n ↦ ‖(fun z ↦ z^2 + c)^[n] c‖) atTop atTop}

/-- The Mandelbrot set is the `d = 2` Multibrot set -/
theorem mandelbrot_eq_multibrot : mandelbrot = multibrot 2 := by
  ext c
  simp only [mandelbrot, mem_ofPred_eq, multibrot, f_f'_iter, tendsto_inf_iff_tendsto_cobounded,
    tendsto_cobounded_iff_norm_tendsto_atTop]
  rfl

/-- The Mandelbrot set is connected -/
theorem isConnected_mandelbrot : IsConnected mandelbrot := by
  rw [mandelbrot_eq_multibrot]; exact isConnected_multibrot 2

/-- The complement of the Mandelbrot set is connected -/
theorem isConnected_compl_mandelbrot : IsConnected mandelbrotᶜ := by
  rw [mandelbrot_eq_multibrot]; exact isConnected_compl_multibrot 2

end
end Ray_Ray_Mandelbrot


