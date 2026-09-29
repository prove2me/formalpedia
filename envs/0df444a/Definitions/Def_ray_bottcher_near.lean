-- Prove2me | Definitions.Def_ray_bottcher_near
-- name    : ray_bottcher_near
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T21:01:59.778634+00:00
-- url     : https://prove2.me/theorems/4c9508a2-8b94-455e-bee0-d9cc1b970928
-- title:
--   ray (6/12): Böttcher's theorem near a superattracting fixed point
-- statement:
--   **Böttcher's theorem with parameters**: if $f_c(z) = z^d + O(z^{d+1})$, $d \ge 2$, is analytic in $(c,z)$, then there is an analytic $b_c(z) = z + O(z^2)$ near $0$ with $b_c(f_c(z)) = b_c(z)^d$, jointly analytic in $(c,z)$. It is given as a convergent infinite product. The file also sets up basic analytic-manifold facts (analyticity of maps between charted spaces, the one-dimensional case $\mathbb{C}$-manifolds, and the relation between `mfderiv` and `deriv`).
--
--   This file is part 6 of 12 of a verbatim flattening of Geoffrey Irving's Lean 4 formalization *ray* (https://github.com/girving/ray, Apache License 2.0). Together the 12 files prove that the Mandelbrot set is connected. Each original ray module is wrapped in its own `section`, and module-system keywords are removed. A few mechanical edits avoid clashes with the full Mathlib import and avoid syntax extensions: a duplicated private definition is dropped, `ContinuousOn.partialSups` is renamed to `ContinuousOn.rayPartialSups`, `Finset.antidiagonal` is written as `Finset.HasAntidiagonal.antidiagonal`, the `bound_destruct` attribute macro is inlined, and the notation `𝕊` is replaced by `(OnePoint ℂ)`. The files are split only because of the compile-time limit. Declaration names are ray's own.
-- source:
--   Geoffrey Irving, ray: The Mandelbrot set is connected (Lean 4 formalization), https://github.com/girving/ray (Apache License 2.0), commit of 2026-08-16; module list in the file header. Mathematical background: A. Douady and J. H. Hubbard, Itération des polynômes quadratiques complexes, C. R. Acad. Sci. Paris 294 (1982); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Section 9 and Appendix; Carleson–Gamelin, Complex Dynamics, Ch. VIII.

import Definitions.Def_ray_hartogs

/-!
# ray (6/12): Böttcher's theorem near a superattracting fixed point

Part 6 of 12 of a flattened copy of Geoffrey Irving's Lean 4 formalization *ray*
(https://github.com/girving/ray, Apache License 2.0, Copyright Geoffrey Irving), which proves that
the Mandelbrot set is connected. Each original module is wrapped in its own `section`;
module-system keywords are removed, and a few names are adjusted to avoid clashes with Mathlib.

Original modules in this file:
* `Ray.Dynamics.BottcherNear`
* `Ray.Manifold.Manifold`
* `Ray.Manifold.Analytic`
* `Ray.Manifold.OneDimension`
-/

-- ===== Ray.Dynamics.BottcherNear =====
section Ray_Ray_Dynamics_BottcherNear
/-!
## Böttcher map near a superattracting fixpoint

We define superattracting fixed points at `0` of a parameterized analytic map `f : ℂ → ℂ → ℂ`
(namely a fixed point of order `d ≥ 2`).  Near the fixpoint, Böttcher coordinates `bottcherNear`
conjugate `f c` to `z ^ d`:

  `bottcherNear c (f c z) = bottcherNear c z ^ d`

This file defines `bottcherNear` locally near `0` using the explicit infinite product formula.
Later in `Potential.lean` we lift to 1D complex manifolds, and `Grow.lean`, `Ray.lean`, and
`Bottcher.lean` analytically continue the map to all postcritical points.

One wart: we require not only that `f c` has a zero of order `d ≥ 2`, but also that `f c` is
"monic": that the leading coefficient of the Taylor series is `1`.  This slightly simplifies the
formulas, but is probably better to remove.
-/

open Classical
open Complex (exp log cpow)
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball)
open Nat (iterate)
open Set
open scoped NNReal Topology
noncomputable section

section Bottcher

-- All information for a monic superattracting fixed point at the origin
variable {f : ℂ → ℂ}
variable {d : ℕ}
variable {z : ℂ}
variable {t : Set ℂ}
variable {a b : ℝ}

-- Facts about d
lemma SuperAt.d0 (s : SuperAt f d) : d ≠ 0 := by have h := s.d2; omega
lemma SuperAt.dp (s : SuperAt f d) : 0 < d := lt_of_lt_of_le two_pos s.d2
lemma SuperAt.drp (s : SuperAt f d) : 0 < (d : ℝ) := Nat.cast_pos.mpr s.dp
lemma SuperAt.drz (s : SuperAt f d) : (d : ℝ) ≠ 0 := s.drp.ne'
lemma SuperAt.dz (s : SuperAt f d) : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.dp.ne'
lemma SuperAt.dr2 (s : SuperAt f d) : 2 ≤ (d : ℝ) :=
  le_trans (by norm_num) (Nat.cast_le.mpr s.d2)

-- Teach `bound` that `0 < d` and `2 ≤ d`
attribute [bound_forward] SuperAt.d2 SuperAt.dp SuperAt.dr2 SuperNear.toSuperAt SuperNear.b0
  SuperNear.b1

-- More basic inequalities
@[bound_forward] lemma SuperNear.a0 (s : SuperNear f d t a b) : 0 ≤ a := by
  simpa only [norm_zero] using s.t2 s.t0

/-- `c` is nonnegative -/
@[bound] lemma SuperNear.c0 (s : SuperNear f d t a b) : 0 ≤ s.c := by
  simp only [SuperNear.c]
  bound
@[bound_forward, bound] lemma SuperNear.c1 (s : SuperNear f d t a b) : s.c < 1 := s.c1'
@[bound] lemma SuperNear.c_le_one (s : SuperNear f d t a b) : s.c ≤ 1 := by bound

/-- g 0 = 1 -/
theorem g0 {f : ℂ → ℂ} {d : ℕ} : g f d 0 = 1 := by simp only [g, if_true]

/-- Asymptotic bound on `f` based on the order `d` zero -/
theorem SuperAt.approx (s : SuperAt f d) : (fun z ↦ f z - z ^ d) =o[𝓝 0] fun z ↦ z ^ d := by
  have a := s.fa0.leading_approx
  simp only [s.fd, s.fc, sub_zero, smul_eq_mul, mul_one] at a
  exact a

/-- `f 0 = 0` -/
theorem SuperAt.f0 (s : SuperAt f d) : f 0 = 0 :=
  haveI p : orderAt f 0 > 0 := by simp [s.fd, s.dp]
  s.fa0.zero_of_order_pos p

/-- `f = z^d g` -/
theorem SuperAt.fg (s : SuperAt f d) (z : ℂ) : f z = z ^ d * g f d z := by
  by_cases z0 : z = 0
  · simp only [z0, zero_pow s.d0, s.f0, MulZeroClass.zero_mul]
  · simp only [g, z0, if_false]; field_simp [z0]

/-- `g` is analytic where `f` is -/
theorem SuperAt.ga_of_fa (s : SuperAt f d) {c : ℂ} (fa : AnalyticAt ℂ f c) :
    AnalyticAt ℂ (g f d) c := by
  rcases fa.exists_ball_analyticOnNhd with ⟨r, rp, fa⟩
  have o : IsOpen (ball c r) := isOpen_ball
  generalize ht : ball c r = t
  rw [ht] at fa o
  suffices h : AnalyticOnNhd ℂ (g f d) t by rw [← ht] at h; exact h _ (mem_ball_self rp)
  have ga : DifferentiableOn ℂ (g f d) (t \ {0}) := by
    have e : ∀ z : ℂ, z ∈ t \ {0} → g f d z = f z / z ^ d := by
      intro z zs; simp only [Set.mem_sdiff, Set.mem_singleton_iff] at zs
      simp only [g, zs.2, if_false]
    rw [differentiableOn_congr e]
    apply DifferentiableOn.div (fa.mono sdiff_subset).differentiableOn
    exact (Differentiable.pow differentiable_id _).differentiableOn
    intro z zs; exact pow_ne_zero _ (Set.mem_sdiff_singleton.mp zs).2
  rw [Complex.analyticOnNhd_iff_differentiableOn o]
  by_cases t0 : (0 : ℂ) ∉ t; · rw [Set.sdiff_singleton_eq_self t0] at ga; exact ga
  simp only [Set.not_notMem] at t0
  have gc : ContinuousAt (g f d) 0 := by
    rw [Metric.continuousAt_iff]; intro e ep
    rcases Metric.eventually_nhds_iff.mp
        (Asymptotics.isBigOWith_iff.mp (s.approx.forall_isBigOWith (by linarith : e / 2 > 0))) with
      ⟨t, tp, h⟩
    use t, tp; intro z zs; specialize h zs
    simp only [g, Complex.dist_eq]
    by_cases z0 : z = 0; · simp only [z0, sub_self, norm_zero]; exact ep
    simp only [z0, if_false, if_true]
    calc ‖f z / z ^ d - 1‖
      _ = ‖f z * (z ^ d)⁻¹ - 1‖ := by rw [div_eq_mul_inv]
      _ = ‖(f z - z ^ d) * (z ^ d)⁻¹‖ := by
        rw [mul_sub_right_distrib, mul_inv_cancel₀ (pow_ne_zero d z0)]
      _ = ‖f z - z ^ d‖ * ‖z ^ d‖⁻¹ := by rw [norm_mul, norm_inv]
      _ ≤ e / 2 * ‖z ^ d‖ * ‖z ^ d‖⁻¹ := by bound
      _ = e / 2 * (‖z ^ d‖ * ‖z ^ d‖⁻¹) := by ring
      _ ≤ e / 2 * 1 := by bound
      _ = e / 2 := by ring
      _ < e := half_lt_self ep
  exact (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (o.mem_nhds t0)).mp ⟨ga, gc⟩

/-- `g` is analytic -/
theorem SuperNear.ga (s : SuperNear f d t a b) : AnalyticOnNhd ℂ (g f d) t := fun z m ↦
  s.ga_of_fa (s.fa z m)

/-- `SuperAt → SuperNear`, manual radius version: if we know a ball where `f` is analytic and
    the resulting `g` is small, then `SuperAt` becomes `SuperNear` -/
theorem SuperAt.super_on_ball (s : SuperAt f d) {r : ℝ} (rp : 0 < r) (r2 : r ≤ a) (a0 : 0 < a)
    (a1 : a < 1) (b0 : 0 ≤ b) (b1 : b < 1) (c1 : a * (1 + b) < 1)
    (fa : AnalyticOnNhd ℂ f (ball 0 r)) (gs : ∀ {z : ℂ}, ‖z‖ < r → ‖g f d z - 1‖ < b) :
    SuperNear f d (ball 0 r) a b :=
  haveI gs : ∀ {z : ℂ}, z ≠ 0 → z ∈ ball (0 : ℂ) r → ‖f z / z ^ d - 1‖ ≤ b := by
    intro z z0 zs
    simp only [mem_ball_zero_iff] at zs
    specialize gs zs
    simp only [g, z0, if_false] at gs
    exact gs.le
  { d2 := s.d2
    fa0 := s.fa0
    fd := s.fd
    fc := s.fc
    o := isOpen_ball
    t0 := mem_ball_self rp
    gs' := fun z0 ↦ gs z0
    a1 := a1
    b0 := b0
    b1 := b1
    c1' := c1
    fa := fa
    t2 := by
      intro z zs
      simp only [mem_ball_zero_iff] at zs
      exact le_trans zs.le r2
    ft := by
      intro z zs; simp only [mem_ball_zero_iff] at zs gs ⊢
      by_cases z0 : z = 0; · simp only [z0, s.f0, rp, norm_zero]
      by_cases f0 : f z = 0
      · simp only [f0, norm_zero, rp]
      · calc ‖f z‖
          _ = ‖f z / z ^ d‖ * ‖z‖ ^ d := by
            rw [← norm_pow, ← norm_mul, div_mul_cancel₀ _ (pow_ne_zero d z0)]
          _ < ‖f z / z ^ d‖ * r ^ d := by
            apply mul_lt_mul_of_pos_left (by bound)
            simp only [Complex.norm_div, norm_pow]
            positivity
          _ = ‖f z / z ^ d - 1 + 1‖ * r ^ d := by
            simp only [Complex.norm_div, norm_pow, sub_add_cancel]
          _ ≤ (‖f z / z ^ d - 1‖ + ‖(1 : ℂ)‖) * r ^ d := by bound
          _ ≤ (b + ‖(1 : ℂ)‖) * r ^ d := by bound [gs z0 zs]
          _ ≤ (1 + b) * r ^ (d - 1) * r := by
            simp only [mul_assoc, ← pow_succ, Nat.sub_add_cancel (le_trans one_le_two s.d2), norm_one,
              add_comm b, le_refl]
          _ ≤ (1 + b) * a ^ (d - 1) * r := by bound
          _ ≤ (1 + b) * a ^ (2 - 1) * r := by bound
          _ = a * (1 + b) * r := by ring
          _ ≤ r := by bound }

/-- `SuperAt → SuperNear`, automatic radius version: given `SuperAt`, we can find a ball where the
    smallness conditions needed for `SuperNear` hold. -/
theorem SuperAt.superNear (s : SuperAt f d) : ∃ t, SuperNear f d t (1 / 2) (1 / 4) := by
  rcases s.fa0.exists_ball_analyticOnNhd with ⟨r0, r0p, fa⟩
  rcases Metric.continuousAt_iff.mp (s.ga_of_fa (fa 0 (mem_ball_self r0p))).continuousAt (1 / 4)
      (by norm_num) with
    ⟨r1, r1p, gs⟩
  set r := min r0 (min r1 (1 / 2))
  use ball 0 r
  have rp : 0 < r := by bound
  have r2 : r ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have rr1 : r ≤ r1 := le_trans (min_le_right r0 _) (min_le_left r1 _)
  simp only [g0, dist_zero_right, Complex.dist_eq] at gs
  exact s.super_on_ball rp r2 (b := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fa.mono (Metric.ball_subset_ball (min_le_left r0 _))) (fun {z} zr ↦
    gs (lt_of_lt_of_le zr rr1))

/-- `g` is small near 0 -/
theorem SuperNear.gs (s : SuperNear f d t a b) {z : ℂ} (zt : z ∈ t) : ‖g f d z - 1‖ ≤ b := by
  by_cases z0 : z = 0
  · simp only [z0, g0, sub_self, norm_zero, s.b0]
  · simp only [g, z0, if_false, s.gs' z0 zt]

/-- `g` is nonzero -/
theorem SuperNear.g_ne_zero (s : SuperNear f d t a b) {z : ℂ} (zt : z ∈ t) : g f d z ≠ 0 := by
  have h := s.gs zt; contrapose h; simp only [h]; norm_num [s.b1]

/-- `f` is zero only at zero -/
theorem SuperNear.f_ne_zero (s : SuperNear f d t a b) {z : ℂ} (zt : z ∈ t) (z0 : z ≠ 0) :
    f z ≠ 0 := by
  simp only [s.fg, mul_ne_zero (pow_ne_zero _ z0) (s.g_ne_zero zt), Ne, not_false_iff]

/-!
## The infinite product

To prove Bottcher's theorem for a monic, superattracting fixpoint, we start with

   `f z = z^d * g z`
   `g 0 = 1`

Ignoring multiple values when taking `d`th roots, we can derive the infinite product

  `(E n z)^(d^n) = f^[n] z`
  `E n z = (f^[n] z)^(1/d^n)`
  `E n z = (f (f^[n-1] z))^(1/d^n)`
  `E n z = (f ((E (n-1) z)^(d^(n-1))))^(1/d^n)`
  `E n z = ((E (n-1) z)^(d^n) * g ((E (n-1) z)^(d^(n-1))))^(1/d^n)`
  `E n z = E (n-1) z * (g ((E (n-1) z)^(d^(n-1))))^(1/d^n)`
  `E n z = E (n-1) z * (g (f^[n-1] z))^(1/d^n)`
  `E n z = z * prod_{1 < k ≤ n} (g (f^[k-1] z))^(1/d^k)`
-/

/-- `^d` shifts `term (n+1)` to `term n`:

    `(term n z)^d = (g (f^[n] z) ^ 1/d^(n+1))^d`
    `             = (g (f^[n-1] (f z)) ^ 1/d^n)`
    `             = term (n-1) (f z)` -/
theorem term_eqn (s : SuperNear f d t a b) : ∀ n, term f d n (f z) = term f d (n + 1) z ^ d := by
  intro n
  simp only [term, ← Function.iterate_succ_apply, pow_mul_nat, div_mul, pow_succ' _ (n + 1),
    mul_div_cancel_left₀ _ s.dz, Nat.succ_eq_add_one, Nat.cast_mul]

/-- The analogue of `term_eqn (-1)`:

    `(z * term 0 z)^d = (z * g z ^ 1/d)^d`
    `                 = z^d * g z`
    `                 = f z` -/
theorem term_base (s : SuperNear f d t a b) : f z = (z * term f d 0 z) ^ d := by
  rw [term]; simp only [Function.iterate_zero, id, one_div]
  rw [mul_pow, pow_mul_nat, zero_add, pow_one, inv_mul_cancel₀]
  · rw [s.fg]; simp only [Complex.cpow_one]
  · simp only [Ne, Nat.cast_eq_zero]
    have := s.d2
    omega

/-- `abs (f z) = abs (z^d * g z) ≤ c * (abs z)^d ≤ c * abs z` -/
theorem f_converges (s : SuperNear f d t a b) : z ∈ t → ‖f z‖ ≤ s.c * ‖z‖ := by
  intro zt
  simp only [s.fg, Complex.norm_mul, norm_pow]
  have gs : ‖g f d z‖ ≤ 1 + b := by
    calc ‖g f d z‖
      _ = ‖g f d z - 1 + 1‖ := by ring_nf
      _ ≤ ‖g f d z - 1‖ + ‖(1 : ℂ)‖ := by bound
      _ ≤ b + ‖(1 : ℂ)‖ := by linarith [s.gs zt]
      _ ≤ (1 + b) := by simp only [norm_one, add_comm, le_refl]
  have az1 : ‖z‖ ≤ 1 := le_trans (s.t2 zt) s.a1.le
  calc ‖z‖ ^ d * ‖g f d z‖
    _ ≤ ‖z‖ ^ 2 * (1 + b) := by bound
    _ = ‖z‖ * ‖z‖ * (1 + b) := by ring_nf
    _ ≤ a * ‖z‖ * (1 + b) := by bound [s.t2 zt]
    _ = a * (1 + b) * ‖z‖ := by ring

/-- Iterating f remains in t -/
theorem SuperNear.mapsTo (s : SuperNear f d t a b) (n : ℕ) : MapsTo f^[n] t t := by
  induction' n with n h; simp only [Set.mapsTo_id, Function.iterate_zero]
  rw [Function.iterate_succ']; exact s.ft.comp h

/-- `‖f^[n] z‖ ≤ s.c ^ n * ‖z‖` -/
theorem iterates_converge (s : SuperNear f d t a b) :
    ∀ n, z ∈ t → ‖f^[n] z‖ ≤ s.c ^ n * ‖z‖ := by
  intro n zt
  induction' n with n nh
  · simp only [Function.iterate_zero, id, pow_zero, one_mul, le_refl]
  · rw [Function.iterate_succ']
    trans s.c * ‖f^[n] z‖
    · exact f_converges s (s.mapsTo n zt)
    · calc s.c * ‖f^[n] z‖
        _ ≤ s.c * (s.c ^ n * ‖z‖) := by bound
        _ = s.c * s.c ^ n * ‖z‖ := by ring
        _ = s.c ^ (n + 1) * ‖z‖ := by rw [← pow_succ']
        _ = s.c ^ n.succ * ‖z‖ := rfl

/-- Iterates are analytic -/
theorem iterates_analytic (s : SuperNear f d t a b) : ∀ n, AnalyticOnNhd ℂ f^[n] t := by
  intro n; induction' n with n h
  · simp only [Function.iterate_zero]
    exact analyticOnNhd_id
  · rw [Function.iterate_succ']
    intro z zt
    exact (s.fa _ (s.mapsTo n zt)).comp (h z zt)

/-- `term` is analytic close to 0 -/
theorem term_analytic (s : SuperNear f d t a b) : ∀ n, AnalyticOnNhd ℂ (term f d n) t := by
  intro n z zt
  refine AnalyticAt.cpow ?_ analyticAt_const ?_
  · exact (s.ga _ (s.mapsTo n zt)).comp (iterates_analytic s n z zt)
  · exact mem_slitPlane_of_near_one (lt_of_le_of_lt (s.gs (s.mapsTo n zt)) s.b1)

@[bound] lemma SuperNear.kt_nonneg (s : SuperNear f d t a b) : 0 ≤ s.kt := by
  unfold kt; bound

/-- term converges to 1 exponentially: `‖term s n z - 1‖ = O((1 / 2) ^ n)` -/
theorem term_converges (s : SuperNear f d t a b) (n : ℕ) (zt : z ∈ t) :
    ‖term f d n z - 1‖ ≤ s.kt * (2⁻¹ : ℝ) ^ n := by
  rw [term]
  trans psg b 2⁻¹ * ‖g f d (f^[n] z) - 1‖ * ‖(1 / (d ^ (n + 1) : ℕ) : ℂ)‖
  · refine pow_small_general ?_ ?_ s.b1
    · exact s.gs (s.mapsTo n zt)
    · simp only [Nat.cast_pow, one_div, norm_inv, norm_pow, RCLike.norm_natCast]
      calc (d ^ (n + 1) : ℝ)⁻¹
        _ ≤ (2 ^ (n + 1))⁻¹ := by bound
        _ ≤ 2⁻¹ := by bound
  · simp only [Nat.cast_pow, one_div, ← div_eq_mul_inv, norm_inv, norm_pow, norm_natCast, inv_pow]
    calc psg b 2⁻¹ * ‖g f d (f^[n] z) - 1‖ / d ^ (n + 1)
      _ ≤ psg b 2⁻¹ * b / 2 ^ (n + 1) := by bound [s.gs (s.mapsTo n zt)]
      _ = s.kt / 2 ^ n := by simp only [SuperNear.kt, pow_succ']; ring

/-- `term` is nonzero, sufficiently close to 0 -/
theorem term_nonzero (s : SuperNear f d t a b) : ∀ n, z ∈ t → term f d n z ≠ 0 := by
  intro n zt
  simp [term, s.g_ne_zero (s.mapsTo n zt)]

/-- The `term` product exists and is analytic -/
theorem term_prod (s : SuperNear f d t a b) :
    ProdExistsOn (term f d) t ∧ AnalyticOnNhd ℂ (tprodOn (term f d)) t ∧
      ∀ z ∈ t, tprodOn (term f d) z ≠ 0 := by
  have a0 : 0 ≤ (2⁻¹ : ℝ) := by norm_num
  obtain ⟨p, a, nz⟩ := fast_products_converge_eventually' s.o a0 (by linarith) (term_analytic s)
    (.of_forall fun n z zt ↦ term_converges s n zt)
  exact ⟨p, a, fun z zt ↦ nz z zt (fun n ↦ term_nonzero s n zt)⟩

/-- The `term` product exists -/
theorem term_prod_exists (s : SuperNear f d t a b) : ProdExistsOn (term f d) t :=
  (term_prod s).1

/-- The `term` product is analytic in `z` -/
theorem term_prod_analytic_z (s : SuperNear f d t a b) : AnalyticOnNhd ℂ (tprodOn (term f d)) t :=
  (term_prod s).2.1

/-- The `term` product is nonzero -/
theorem term_prod_ne_zero (s : SuperNear f d t a b) (zt : z ∈ t) : tprodOn (term f d) z ≠ 0 :=
  (term_prod s).2.2 _ zt

/-- `bottcherNear` satisfies `b (f z) = (b z)^d` near 0 -/
theorem bottcherNear_eqn (s : SuperNear f d t a b) (zt : z ∈ t) :
    bottcherNear f d (f z) = bottcherNear f d z ^ d := by
  simp_rw [bottcherNear]
  have pe := (term_prod_exists s) z zt
  simp only [mul_pow, product_pow' pe]
  have pe : ProdExists fun n ↦ term f d n z ^ d := by
    rcases pe with ⟨g, hg⟩; exact ⟨_, product_pow d hg⟩
  simp only [product_split pe, ← term_eqn s, ← mul_assoc, ← mul_pow, ← term_base s]

/-- `bottcherNear_eqn`, iterated -/
theorem bottcherNear_eqn_iter (s : SuperNear f d t a b) (zt : z ∈ t) (n : ℕ) :
    bottcherNear f d (f^[n] z) = bottcherNear f d z ^ d ^ n := by
  induction' n with n h; simp only [Function.iterate_zero, id, pow_zero, pow_one]
  simp only [Function.comp, Function.iterate_succ', pow_succ, pow_mul,
    bottcherNear_eqn s (s.mapsTo n zt), h]

/-- `f^[n] 0 = 0` -/
theorem iterates_at_zero (s : SuperNear f d t a b) : ∀ n, f^[n] 0 = 0 := by
  intro n; induction' n with n h; simp only [Function.iterate_zero, id]
  simp only [Function.iterate_succ', Function.comp_apply, h, s.f0]

/-- `term s n 0 = 1` -/
theorem term_at_zero (s : SuperNear f d t a b) (n : ℕ) : term f d n 0 = 1 := by
  simp only [term, iterates_at_zero s, g0, Complex.one_cpow]

/-- `prod (term s _ 0) = 1` -/
theorem term_prod_at_zero (s : SuperNear f d t a b) : tprodOn (term f d) 0 = 1 := by
  simp_rw [tprodOn, term_at_zero s, tprod_one]

/-- `bottcherNear' 0 = 1` (so in particular `bottcherNear` is a local isomorphism) -/
theorem bottcherNear_monic (s : SuperNear f d t a b) :
    HasDerivAt (bottcherNear f d) 1 0 := by
  have dz : HasDerivAt (fun z : ℂ ↦ z) 1 0 := hasDerivAt_id 0
  have db := HasDerivAt.mul dz (term_prod_analytic_z s 0 s.t0).differentiableAt.hasDerivAt
  simp only [one_mul, MulZeroClass.zero_mul, add_zero] at db
  rw [term_prod_at_zero s] at db; exact db

/-- `bottcherNear 0 = 0` -/
@[simp] lemma bottcherNear_zero : bottcherNear f d 0 = 0 := by
  simp only [bottcherNear, MulZeroClass.zero_mul]

/-- `z ≠ 0 → bottcherNear z ≠ 0` -/
theorem bottcherNear_ne_zero (s : SuperNear f d t a b) :
    z ∈ t → z ≠ 0 → bottcherNear f d z ≠ 0 :=
  fun zt z0 ↦ mul_ne_zero z0 (term_prod_ne_zero s zt)

/-- `bottcherNear` is analytic in `z` -/
theorem bottcherNear_analytic_z (s : SuperNear f d t a b) :
    AnalyticOnNhd ℂ (bottcherNear f d) t :=
  analyticOnNhd_id.mul (term_prod_analytic_z s)

/-- `f^[n] z → 0` -/
theorem iterates_tendsto (s : SuperNear f d t a b) (zt : z ∈ t) :
    Tendsto (fun n ↦ f^[n] z) atTop (𝓝 0) := by
  by_cases z0 : z = 0; simp only [z0, iterates_at_zero s, tendsto_const_nhds]
  rw [Metric.tendsto_atTop]; intro e ep
  simp only [Complex.dist_eq, sub_zero]
  have xp : e / ‖z‖ > 0 := div_pos ep (norm_pos_iff.mpr z0)
  rcases exists_pow_lt_of_lt_one xp s.c1 with ⟨N, Nb⟩
  simp only [lt_div_iff₀ (norm_pos_iff.mpr z0)] at Nb
  use N; intro n nN
  refine lt_of_le_of_lt (iterates_converge s n zt) (lt_of_le_of_lt ?_ Nb)
  bound

/-- `bottcherNear < 1` -/
theorem bottcherNear_lt_one (s : SuperNear f d t a b) (zt : z ∈ t) :
    ‖bottcherNear f d z‖ < 1 := by
  rcases Metric.continuousAt_iff.mp (bottcherNear_analytic_z s _ s.t0).continuousAt 1 zero_lt_one
    with ⟨r, rp, rs⟩
  simp only [Complex.dist_eq, sub_zero, bottcherNear_zero] at rs
  have b' : ∀ᶠ n in atTop, ‖bottcherNear f d (f^[n] z)‖ < 1 := by
    refine (Metric.tendsto_nhds.mp (iterates_tendsto s zt) r rp).mp (.of_forall fun n h ↦ ?_)
    rw [Complex.dist_eq, sub_zero] at h; exact rs h
  rcases b'.exists with ⟨n, b⟩
  contrapose b; simp only [not_lt] at b ⊢
  simp only [bottcherNear_eqn_iter s zt n, norm_pow, one_le_pow₀ b]

/-- Linear bound on `bottcherNear` -/
theorem bottcherNear_le (s : SuperNear f d t a b) (zt : z ∈ t) :
    ‖bottcherNear f d z‖ ≤ s.k * ‖z‖ := by
  simp only [bottcherNear, norm_mul]; rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases term_prod_exists s _ zt with ⟨p, h⟩; rw [h.tprod_eq]; simp only [HasProd] at h
  apply le_of_tendsto' (Filter.Tendsto.comp continuous_norm.continuousAt h)
  intro A
  clear h
  simp only [Function.comp, norm_prod]
  have tb : ∀ n, ‖term f d n z‖ ≤ 1 + s.kt * (1 / 2 : ℝ) ^ n := by
    intro n
    calc ‖term f d n z‖
      _ = ‖1 + (term f d n z - 1)‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖term f d n z - 1‖ := by bound
      _ = 1 + ‖term f d n z - 1‖ := by norm_num
      _ ≤ 1 + s.kt * (1 / 2 : ℝ) ^ n := by bound [term_converges s n zt]
  have p : ∀ n : ℕ, 0 < (1 : ℝ) + s.kt * (1 / 2 : ℝ) ^ n :=
    fun _ ↦ by apply add_pos_of_pos_of_nonneg <;> bound
  have lb : ∀ n : ℕ, Real.log ((1 : ℝ) + s.kt * (1 / 2 : ℝ) ^ n) ≤ s.kt * (1 / 2 : ℝ) ^ n :=
    fun n ↦ le_trans (Real.log_le_sub_one_of_pos (p n)) (le_of_eq (by ring))
  refine le_trans (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun n _ ↦ tb n) ?_
  rw [← Real.exp_log (Finset.prod_pos fun n _ ↦ p n), Real.log_prod fun n _ ↦ (p n).ne']
  refine le_trans (Real.exp_le_exp.mpr (Finset.sum_le_sum fun n _ ↦ lb n)) ?_
  have geom := partial_scaled_geometric_bound (s.kt).toNNReal A one_half_pos.le
    one_half_lt_one
  simp only [Real.coe_toNNReal', s.kt_nonneg, sup_of_le_left,
    (by norm_num : (1 - 1 / 2 : ℝ)⁻¹ = 2)] at geom
  refine le_trans (Real.exp_le_exp.mpr geom) (le_of_eq ?_)
  simp only [SuperNear.k, mul_comm]

end Bottcher

-- Next we prove that everything is analytic in an additional function parameter
section BottcherC

variable {f : ℂ → ℂ → ℂ}
variable {d : ℕ}
variable {u : Set ℂ}
variable {t : Set (ℂ × ℂ)}
variable {a b : ℝ}

/-- `SuperNearC → SuperNear` at `p ∈ t` -/
theorem SuperNearC.ts (s : SuperNearC f d u t a b) {p : ℂ × ℂ} (m : p ∈ t) :
    SuperNear (f p.1) d {z | (p.1, z) ∈ t} a b :=
  s.s (s.tc m)

/-- The parameter set `u` is open -/
theorem SuperNearC.ou (s : SuperNearC f d u t a b) : IsOpen u := by
  have e : u = Prod.fst '' t := by
    ext c; simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨fun m ↦ ⟨0, (s.s m).t0⟩, fun h ↦ Exists.elim h fun z m ↦ s.tc m⟩
  rw [e]; exact isOpenMap_fst _ s.o

/-- `SuperNearC → SuperAtC` -/
theorem SuperNearC.superAtC (s : SuperNearC f d u t a b) : SuperAtC f d u :=
  { o := s.ou
    s := by
      intro c m; have s := s.s m
      exact
        { d2 := s.d2
          fa0 := s.fa0
          fd := s.fd
          fc := s.fc }
    fa := fun {c} m ↦ s.fa _ (s.s m).t0 }

/-- A Two-parameter version of `g` -/
def g2 (f : ℂ → ℂ → ℂ) (d : ℕ) := fun p : ℂ × ℂ ↦ g (f p.1) d p.2

/-- `g2` is jointly analytic where `f` is -/
theorem SuperAtC.ga_of_fa (s : SuperAtC f d u) {t : Set (ℂ × ℂ)} (o : IsOpen t)
    (fa : AnalyticOnNhd ℂ (uncurry f) t) (tc : ∀ {p : ℂ × ℂ}, p ∈ t → p.1 ∈ u) :
    AnalyticOnNhd ℂ (g2 f d) t := by
  refine Pair.hartogs o ?_ ?_
  · intro c z m
    simp only [g2, g]
    by_cases zero : z = 0; · simp only [zero, if_true]; exact analyticAt_const
    · simp only [zero, if_false]; refine AnalyticAt.div ?_ analyticAt_const (pow_ne_zero _ zero)
      refine (fa _ ?_).comp₂ analyticAt_id analyticAt_const; exact m
  · intro c z m; apply (s.s (tc m)).ga_of_fa
    refine (fa _ ?_).comp₂ analyticAt_const analyticAt_id; exact m

/-- `g2` is jointly analytic -/
theorem SuperNearC.ga (s : SuperNearC f d u t a b) : AnalyticOnNhd ℂ (g2 f d) t :=
  s.superAtC.ga_of_fa s.o s.fa fun {_} m ↦ s.tc m

/-- `SuperNearC` commutes with unions -/
theorem SuperNearC.union {I : Type} {u : I → Set ℂ} {t : I → Set (ℂ × ℂ)}
    (s : ∀ i, SuperNearC f d (u i) (t i) a b) : SuperNearC f d (⋃ i, u i) (⋃ i, t i) a b := by
  set tu := ⋃ i, t i
  have o : IsOpen tu := isOpen_iUnion fun i ↦ (s i).o
  have sm : ∀ {c z : ℂ},
      (c, z) ∈ tu → ∃ u, z ∈ u ∧ u ⊆ {z | (c, z) ∈ tu} ∧ SuperNear (f c) d u a b := by
    intro c z m; rcases Set.mem_iUnion.mp m with ⟨i, m⟩; use{z | (c, z) ∈ t i}
    simp only [Set.mem_ofPred_eq, m, Set.mem_iUnion, Set.ofPred_subset_ofPred, true_and, tu]
    constructor
    · exact fun z m ↦ ⟨i, m⟩
    · exact (s i).s ((s i).tc m)
  exact
    { o
      tc := by
        intro p m; rcases Set.mem_iUnion.mp m with ⟨i, m⟩
        exact Set.subset_iUnion _ i ((s i).tc m)
      fa := by intro p m; rcases Set.mem_iUnion.mp m with ⟨i, m⟩; exact (s i).fa _ m
      s := by
        intro c m; rcases Set.mem_iUnion.mp m with ⟨i, m⟩; have s := (s i).s m
        exact
          { d2 := s.d2
            fa0 := s.fa0
            fd := s.fd
            fc := s.fc
            o := o.snd_preimage c
            a1 := s.a1
            b0 := s.b0
            b1 := s.b1
            c1' := s.c1'
            t0 := Set.subset_iUnion _ i s.t0
            t2 := by intro z m; rcases sm m with ⟨u, m, _, s⟩; exact s.t2 m
            fa := by intro z m; rcases sm m with ⟨u, m, _, s⟩; exact s.fa _ m
            ft := by intro z m; rcases sm m with ⟨u, m, us, s⟩; exact us (s.ft m)
            gs' := by intro z z0 m; rcases sm m with ⟨u, m, _, s⟩; exact s.gs' z0 m } }

/-- `SuperAtC → SuperNearC`, staying inside `w` -/
theorem SuperAtC.superNearC' (s : SuperAtC f d u) {w : Set (ℂ × ℂ)} (wo : IsOpen w)
    (wc : ∀ c, c ∈ u → (c, (0 : ℂ)) ∈ w) : ∃ t, t ⊆ w ∧ SuperNearC f d u t (1 / 2) (1 / 4) := by
  have h : ∀ c, c ∈ u →
      ∃ r, r > 0 ∧ ball c r ⊆ u ∧ ball (c, 0) r ⊆ w ∧
        SuperNearC f d (ball c r) (ball (c, 0) r) (1 / 2) (1 / 4) := by
    intro c m
    rcases(s.fa m).exists_ball_analyticOnNhd with ⟨r0, r0p, fa⟩
    rcases Metric.isOpen_iff.mp s.o c m with ⟨r1, r1p, rc⟩
    set r2 := min r0 r1
    have fa := fa.mono (Metric.ball_subset_ball (min_le_left r0 r1))
    have rc : ball c r2 ⊆ u := le_trans (Metric.ball_subset_ball (by bound)) rc
    have ga := s.ga_of_fa isOpen_ball fa
        (by intro p m; simp only [← ball_prod_same, Set.mem_prod] at m; exact rc m.1)
    rcases Metric.isOpen_iff.mp wo (c, 0) (wc c m) with ⟨r3, r3p, rw⟩
    rcases Metric.continuousAt_iff.mp (ga (c, 0) (mem_ball_self (by bound))).continuousAt
        (1 / 4) (by norm_num) with ⟨r4, r4p, gs⟩
    set r := min (min r2 r3) (min r4 (1 / 2))
    have rp : 0 < r := by bound
    have rh : r ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    have rr4 : r ≤ r4 := le_trans (min_le_right _ _) (min_le_left r4 _)
    have rc : ball c r ⊆ u := le_trans (Metric.ball_subset_ball (by bound)) rc
    have rw : ball (c, 0) r ⊆ w :=
      _root_.trans (Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _))) rw
    use r, rp, rc, rw
    exact
      { o := isOpen_ball
        tc := by
          intro p m; simp only [← ball_prod_same, Set.mem_prod] at m
          exact Metric.ball_subset_ball (by linarith) m.1
        s := by
          intro c' m; simp only [← ball_prod_same, Set.mem_prod, m, true_and]
          apply (s.s (rc m)).super_on_ball rp rh (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num)
          · apply fa.comp₂ analyticOnNhd_const analyticOnNhd_id
            intro z zm; apply Metric.ball_subset_ball (by bound : r ≤ r2)
            simp only [← ball_prod_same, Set.mem_prod, m, true_and]; exact zm
          · simp only [Complex.dist_eq, Prod.dist_eq, sub_zero, max_lt_iff, and_imp, g2, g0] at gs
            simp only [Metric.mem_ball, Complex.dist_eq] at m
            intro z zr; exact @gs ⟨c', z⟩ (lt_of_lt_of_le m rr4) (lt_of_lt_of_le zr rr4)
        fa := fa.mono (Metric.ball_subset_ball (min_le_of_left_le (min_le_left _ _))) }
  set r := fun c : u ↦ choose (h _ c.mem)
  set v := fun c : u ↦ ball (c : ℂ) (r c)
  set t := fun c : u ↦ ball ((c : ℂ), (0 : ℂ)) (r c)
  use⋃ c : u, t c
  have e : u = ⋃ c : u, v c := by
    apply Set.ext; intro c; rw [Set.mem_iUnion]; constructor
    · intro m; use⟨c, m⟩; rcases choose_spec (h c m) with ⟨rp, _, _⟩
      exact mem_ball_self rp
    · intro m; rcases m with ⟨i, m⟩; rcases choose_spec (h _ i.mem) with ⟨_, us, _⟩
      exact us m
  have tw : (⋃ c : u, t c) ⊆ w := by
    apply Set.iUnion_subset; intro i; rcases choose_spec (h _ i.mem) with ⟨_, _, rw, _⟩; exact rw
  have si : ∀ c : u, SuperNearC f d (v c) (t c) (1 / 2) (1 / 4) := by
    intro i; rcases choose_spec (h _ i.mem) with ⟨_, _, _, s⟩; exact s
  have s := SuperNearC.union si; rw [← e] at s
  exact ⟨tw, s⟩

/-- `SuperAtC → SuperNearC` -/
theorem SuperAtC.superNearC (s : SuperAtC f d u) : ∃ t, SuperNearC f d u t (1 / 2) (1 / 4) := by
  rcases s.superNearC' isOpen_univ fun _ _ ↦ Set.mem_univ _ with ⟨t, _, s⟩; exact ⟨t, s⟩

theorem iterates_analytic_c (s : SuperNearC f d u t a b) {c z : ℂ} (n : ℕ) (m : (c, z) ∈ t) :
    AnalyticAt ℂ (fun c ↦ (f c)^[n] z) c := by
  induction' n with n nh; · simp only [Function.iterate_zero, id]; exact analyticAt_const
  · simp_rw [Function.iterate_succ']; simp only [Function.comp_apply]
    refine (s.fa _ ?_).comp (analyticAt_id.prod nh)
    exact (s.ts m).mapsTo n m

theorem term_analytic_c (s : SuperNearC f d u t a b) {c z : ℂ} (n : ℕ) (m : (c, z) ∈ t) :
    AnalyticAt ℂ (fun c ↦ term (f c) d n z) c := by
  refine AnalyticAt.cpow ?_ analyticAt_const ?_
  · have e : (fun c ↦ g (f c) d ((f c)^[n] z)) = fun c ↦ g2 f d (c, (f c)^[n] z) := rfl
    rw [e]
    refine (s.ga _ ?_).comp ?_
    · exact (s.ts m).mapsTo n m
    · apply analyticAt_id.prod (iterates_analytic_c s n m)
  · refine mem_slitPlane_of_near_one ?_
    exact lt_of_le_of_lt ((s.ts m).gs ((s.ts m).mapsTo n m)) (s.ts m).b1

/-- `term` prod is analytic in `c` -/
theorem term_prod_analytic_c (s : SuperNearC f d u t a b) {c z : ℂ} (m : (c, z) ∈ t) :
    AnalyticAt ℂ (fun c ↦ tprod fun n ↦ term (f c) d n z) c := by
  have a0 : 0 ≤ (2⁻¹ : ℝ) := by norm_num
  set t' := {c | (c, z) ∈ t}
  have o' : IsOpen t' := s.o.preimage (by continuity)
  refine (fast_products_converge_eventually' o' a0 (by linarith) ?_
    (.of_forall fun n c m ↦ term_converges (s.ts m) n m)).2.1 _ m
  exact fun n c m ↦ term_analytic_c s n m

/-- `term` prod is jointly analytic (using Hartogs's theorem for simplicity) -/
theorem term_prod_analytic (s : SuperNearC f d u t a b) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ tprod fun n ↦ term (f p.1) d n p.2) t := by
  refine Pair.hartogs s.o ?_ ?_
  · intro c z m; simp only; exact term_prod_analytic_c s m
  · intro c z m; simp only; exact term_prod_analytic_z (s.ts m) _ m

/-- `bottcherNear` is analytic in `c` -/
theorem bottcherNear_analytic_c (s : SuperNearC f d u t a b) {c z : ℂ} (m : (c, z) ∈ t) :
    AnalyticAt ℂ (fun c ↦ bottcherNear (f c) d z) c :=
  analyticAt_const.mul (term_prod_analytic_c s m)

/-- `bottcherNear` is jointly analytic -/
theorem bottcherNear_analytic (s : SuperNearC f d u t a b) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ bottcherNear (f p.1) d p.2) t := fun _ m ↦
  analyticAt_snd.mul (term_prod_analytic s _ m)

/-- `deriv f` is nonzero away from 0 -/
theorem df_ne_zero (s : SuperNearC f d u t a b) {c : ℂ} (m : c ∈ u) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (c, 0), deriv (f p.1) p.2 = 0 ↔ p.2 = 0 := by
  have df : ∀ e z, (e, z) ∈ t →
      deriv (f e) z = ↑d * z ^ (d - 1) * g (f e) d z + z ^ d * deriv (g (f e) d) z := by
    intro e z m; apply HasDerivAt.deriv
    have fg : f e = fun z ↦ z ^ d * g (f e) d z := by funext; rw [(s.ts m).fg]
    nth_rw 1 [fg]
    apply HasDerivAt.mul; apply hasDerivAt_pow
    rw [hasDerivAt_deriv_iff]; exact ((s.ts m).ga _ m).differentiableAt
  have small : ∀ᶠ p : ℂ × ℂ in 𝓝 (c, 0),
      ‖p.2 * deriv (g (f p.1) d) p.2‖ < ‖↑d * g (f p.1) d p.2‖ := by
    have ga : AnalyticAt ℂ (uncurry fun c z ↦ g (f c) d z) (c, 0) := s.ga _ (s.s m).t0
    apply ContinuousAt.eventually_lt
    · exact continuous_norm.continuousAt.comp (continuousAt_snd.mul ga.deriv2.continuousAt)
    · exact continuous_norm.continuousAt.comp (continuousAt_const.mul ga.continuousAt)
    · simp only [g0, MulZeroClass.zero_mul, norm_zero, Complex.norm_natCast, mul_one, Nat.cast_pos]
      exact (s.s m).dp
  apply small.mp
  apply (s.o.eventually_mem (s.s m).t0).mp
  refine .of_forall ?_; clear small
  intro ⟨e, w⟩ m' small; simp only [df _ _ m'] at small ⊢
  nth_rw 4 [← Nat.sub_add_cancel (Nat.succ_le_of_lt (s.s m).dp)]
  simp only [pow_add, pow_one, mul_comm _ (w ^ (d - 1)), mul_assoc (w ^ (d - 1)) _ _, ←
    left_distrib, mul_eq_zero, pow_eq_zero_iff (Nat.sub_pos_of_lt (s.s m).d2).ne']
  exact or_iff_left (add_ne_zero_of_abs_lt small)

end BottcherC

end
end Ray_Ray_Dynamics_BottcherNear

-- ===== Ray.Manifold.Manifold =====
section Ray_Ray_Manifold_Manifold
/-!
## Manifold lemmas
-/

open ChartedSpace (chartAt)
open Function (uncurry)
open Set
open scoped Manifold Topology
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H : Type} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

variable {A M : Type} [TopologicalSpace A] [TopologicalSpace M]
variable {B N : Type} [TopologicalSpace B] [TopologicalSpace N]
variable {C O : Type} [TopologicalSpace C] [TopologicalSpace O]
variable {D P : Type} [TopologicalSpace D] [TopologicalSpace P]

/-- Version of `ModelWithCorners.prod_apply` with `x ∈ H × H'` rather than `ModelProd H H'`.  This
comes up because other simplification doesn't stay in `ModelProd`. -/
@[simp]
lemma ModelWithCorners.prod_apply' {E H E' H' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') (x : H × H') :
    (I.prod I') x = (I x.1, I' x.2) :=
  ModelWithCorners.prod_apply _ _ _

variable {I : ModelWithCorners 𝕜 E A} [ChartedSpace A M]
variable {J : ModelWithCorners 𝕜 F B} [ChartedSpace B N]
variable {K : ModelWithCorners 𝕜 G C} [ChartedSpace C O]
variable {L : ModelWithCorners 𝕜 H D} [ChartedSpace D P]

section Nhds

/-- `extChartAt` as a `PartialHomeomorph` -/
def extChartAt' (I : ModelWithCorners 𝕜 E A) [I.Boundaryless] {M : Type}
    [TopologicalSpace M] [ChartedSpace A M] (x : M) : OpenPartialHomeomorph M E where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x

/-- `extChartAt.symm` maps `𝓝` to `𝓝` -/
theorem extChartAt_symm_map_nhds [I.Boundaryless] {x : M} {y : E}
    (m : y ∈ (extChartAt I x).target) :
    Filter.map (extChartAt I x).symm (𝓝 y) = 𝓝 ((extChartAt I x).symm y) :=
  (extChartAt' I x).symm.map_nhds_eq m

/-- `extChartAt.symm` maps `𝓝` to `𝓝` -/
theorem extChartAt_symm_map_nhds' (I : ModelWithCorners 𝕜 E A) [I.Boundaryless] {M : Type}
    [TopologicalSpace M] [ChartedSpace A M] (x : M) :
    Filter.map (extChartAt I x).symm (𝓝 (extChartAt I x x)) = 𝓝 x := by
  convert extChartAt_symm_map_nhds (mem_extChartAt_target x)
  simp only [PartialEquiv.left_inv _ (mem_extChartAt_source x)]
  infer_instance

/-- Nontrivial manifolds have no isolated points.
    Unfortunately, making this an instance gives "cannot find synthesization order for instance" -/
theorem AnalyticManifold.punctured_nhds_neBot (I : ModelWithCorners 𝕜 E A) [I.Boundaryless]
    [Nontrivial E] (x : M) : (𝓝[{x}ᶜ] x).NeBot := by
  have p := Module.punctured_nhds_neBot 𝕜 E (extChartAt I x x)
  simp only [← Filter.frequently_true_iff_neBot, frequently_nhdsWithin_iff, ←
    extChartAt_symm_map_nhds' I x, Filter.frequently_map, true_and,
    mem_compl_singleton_iff] at p ⊢
  apply p.mp
  apply ((isOpen_extChartAt_target x).eventually_mem (mem_extChartAt_target x)).mp
  refine .of_forall fun y m h ↦ ?_
  contrapose h; nth_rw 2 [← h]
  rw [PartialEquiv.right_inv _ m]

end Nhds

section Deriv

/-- `TangentSpace` commutes with products -/
theorem tangentSpace_prod (x : M) (y : N) :
    TangentSpace (I.prod J) (x, y) = (TangentSpace I x × TangentSpace J y) := by
  simp only [TangentSpace]

/-- `HasMFDerivAt` composition for curried functions.
    This was oddly difficult to prove. -/
theorem MDifferentiableAt.hasMFDerivAt_uncurry {f : N → O → P} {y : N} {z : O}
    (fd : MDifferentiableAt (J.prod K) L (uncurry f) (y, z))
    {df0 : TangentSpace J y →L[𝕜] TangentSpace L (f y z)}
    (fh0 : HasMFDerivAt J L (fun x ↦ f x z) y df0)
    {df1 : TangentSpace K z →L[𝕜] TangentSpace L (f y z)}
    (fh1 : HasMFDerivAt K L (fun x ↦ f y x) z df1) :
    HasMFDerivAt (J.prod K) L (uncurry f) (y, z)
      (df0.comp (ContinuousLinearMap.fst 𝕜 (TangentSpace J y) (TangentSpace K z)) +
        df1.comp (ContinuousLinearMap.snd 𝕜 (TangentSpace J y) (TangentSpace K z))) := by
  set fst := ContinuousLinearMap.fst 𝕜 (TangentSpace J y) (TangentSpace K z)
  set snd := ContinuousLinearMap.snd 𝕜 (TangentSpace J y) (TangentSpace K z)
  generalize hdf : mfderiv (J.prod K) L (uncurry f) (y, z) = df
  have fh := fd.hasMFDerivAt; rw [hdf] at fh
  suffices e : df = df0.comp fst + df1.comp snd by rw [e] at fh; exact fh
  apply ContinuousLinearMap.ext; intro ⟨u, v⟩
  have hu : ∀ u : TangentSpace J y, df (u, 0) = df0 u := by
    intro u
    have d : HasMFDerivAt J L (uncurry f ∘ fun x ↦ (x, z)) y
        (df.comp ((ContinuousLinearMap.id 𝕜 (TangentSpace J y)).prod 0)) :=
      fh.comp y ((hasMFDerivAt_id _).prodMk (hasMFDerivAt_const _ _))
    simp only [hasMFDerivAt_unique fh0 d]
    rfl
  have hv : ∀ v : TangentSpace K z, df (0, v) = df1 v := by
    intro v
    have d : HasMFDerivAt K L (uncurry f ∘ fun x ↦ (y, x)) z (df.comp
        ((0 : TangentSpace K z →L[𝕜] TangentSpace J y).prod
          (ContinuousLinearMap.id 𝕜 (TangentSpace K z)))) :=
      fh.comp z ((hasMFDerivAt_const _ _).prodMk (hasMFDerivAt_id _))
    rw [hasMFDerivAt_unique fh1 d]
    rfl
  have e : (u, v) = (u, 0) + (0, v) := by simp only [Prod.mk_add_mk, add_zero, zero_add]
  nth_rw 1 [e]
  exact (map_add df _ _).trans (by rw [hu u, hv v]; rfl)

/-- `HasMFDerivAt` composition for curried functions -/
theorem MDifferentiableAt.hasMFDerivAt_comp2 {f : N → O → P} {g : M → N} {h : M → O} {x : M}
    (fd : MDifferentiableAt (J.prod K) L (uncurry f) (g x, h x))
    {dg : TangentSpace I x →L[𝕜] TangentSpace J (g x)} (gh : HasMFDerivAt I J g x dg)
    {dh : TangentSpace I x →L[𝕜] TangentSpace K (h x)} (hh : HasMFDerivAt I K h x dh)
    {df0 : TangentSpace J (g x) →L[𝕜] TangentSpace L (f (g x) (h x))}
    (fh0 : HasMFDerivAt J L (fun y ↦ f y (h x)) (g x) df0)
    {df1 : TangentSpace K (h x) →L[𝕜] TangentSpace L (f (g x) (h x))}
    (fh1 : HasMFDerivAt K L (fun y ↦ f (g x) y) (h x) df1) :
    HasMFDerivAt I L (fun y ↦ f (g y) (h y)) x (df0.comp dg + df1.comp dh) := by
  have fh := (fd.hasMFDerivAt_uncurry fh0 fh1).comp x (gh.prodMk hh)
  exact fh

/-- More general version of `hasMFDerivAt_iff_hasDerivAt`.
    The mathlib version doesn't handle product spaces. -/
theorem hasMFDerivAt_iff_hasFDerivAt' {I : ModelWithCorners 𝕜 E A} [I.Boundaryless]
    [ChartedSpace A E] [IsManifold I ⊤ E] [ExtChartEqRefl I]
    {J : ModelWithCorners 𝕜 F B} [J.Boundaryless] [ChartedSpace B F] [IsManifold J ⊤ F]
    [ExtChartEqRefl J] {f : E → F} {x : E} {f' : E →L[𝕜] F} :
    HasMFDerivAt I J f x f' ↔ HasFDerivAt f f' x := by
  simp only [HasMFDerivAt, ModelWithCorners.range_eq_univ,
    writtenInExtChartAt, extChartAt_eq_refl, Function.comp_def, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, id]
  exact ⟨fun x ↦ hasFDerivWithinAt_univ.mp x.2,
    fun d ↦ ⟨d.continuousAt, hasFDerivWithinAt_univ.mpr d⟩⟩

/-- Variant of `mfderiv_comp` that doesn't use `∘` for better inference -/
theorem mfderiv_comp' {f : M → N} (x : M) {g : N → O} (hg : MDifferentiableAt J K g (f x))
    (hf : MDifferentiableAt I J f x) :
    mfderiv I K (fun x ↦ g (f x)) x = (mfderiv J K g (f x)).comp (mfderiv I J f x) :=
  mfderiv_comp _ hg hf

variable [IsManifold I ⊤ M] [IsManifold J ⊤ N] [IsManifold K ⊤ O] [IsManifold L ⊤ P]

/-- Chart derivatives are invertible (left inverse) -/
theorem extChartAt_mderiv_left_inverse [I.Boundaryless] {x y : M}
    (m : y ∈ (extChartAt I x).source) :
    (mfderiv (modelWithCornersSelf 𝕜 E) I (extChartAt I x).symm (extChartAt I x y)).comp
        (mfderiv I (modelWithCornersSelf 𝕜 E) (extChartAt I x) y) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I y) := by
  have m' : extChartAt I x y ∈ (extChartAt I x).target := PartialEquiv.map_source _ m
  have mc : y ∈ (chartAt A x).source := by simpa only [mfld_simps] using m
  have d0 := (contMDiffOn_extChartAt_symm (n := ⊤) _ _ m').mdifferentiableWithinAt (by decide)
  have d1 := (contMDiffAt_extChartAt' (I := I) (n := ⊤) mc).mdifferentiableWithinAt (by decide)
  replace d0 := d0.mdifferentiableAt (extChartAt_target_mem_nhds' m')
  simp only [mdifferentiableWithinAt_univ] at d1
  have c := mfderiv_comp y d0 d1
  refine Eq.trans c.symm ?_
  rw [← mfderiv_id]
  apply Filter.EventuallyEq.mfderiv_eq
  rw [Filter.eventuallyEq_iff_exists_mem]; use(extChartAt I x).source
  use extChartAt_source_mem_nhds' m
  intro z zm
  simp only [Function.comp, id, PartialEquiv.left_inv _ zm]

/-- Chart derivatives are invertible (right inverse) -/
theorem extChartAt_mderiv_right_inverse [I.Boundaryless] {x : M} {y : E}
    (m : y ∈ (extChartAt I x).target) :
    (mfderiv I (modelWithCornersSelf 𝕜 E) (extChartAt I x) ((extChartAt I x).symm y)).comp
        (mfderiv (modelWithCornersSelf 𝕜 E) I (extChartAt I x).symm y) =
      ContinuousLinearMap.id 𝕜 (TangentSpace (modelWithCornersSelf 𝕜 E) y) := by
  have m' : (extChartAt I x).symm y ∈ (extChartAt I x).source := PartialEquiv.map_target _ m
  have mc : (extChartAt I x).symm y ∈ (chartAt A x).source := by simpa only [mfld_simps] using m'
  have d0 := (contMDiffOn_extChartAt_symm (n := ⊤) _ _ m).mdifferentiableWithinAt (by decide)
  have d1 := (contMDiffAt_extChartAt' (I := I) (n := ⊤) mc).mdifferentiableWithinAt (by decide)
  replace d0 := d0.mdifferentiableAt (extChartAt_target_mem_nhds' m)
  simp only [mdifferentiableWithinAt_univ] at d1
  have c := mfderiv_comp y d1 d0
  refine Eq.trans c.symm ?_; clear c; rw [← mfderiv_id]; apply Filter.EventuallyEq.mfderiv_eq
  rw [Filter.eventuallyEq_iff_exists_mem]; use(extChartAt I x).target
  have n := extChartAt_target_mem_nhdsWithin' m'
  simp only [ModelWithCorners.range_eq_univ, nhdsWithin_univ,
    PartialEquiv.right_inv _ m] at n
  use n; intro z zm
  simp only [Function.comp, id, PartialEquiv.right_inv _ zm, Function.comp]

/-- Chart derivatives are invertible (right inverse) -/
theorem extChartAt_mderiv_right_inverse' [I.Boundaryless] {x y : M}
    (m : y ∈ (extChartAt I x).source) :
    (mfderiv I (modelWithCornersSelf 𝕜 E) (extChartAt I x) y).comp
        (mfderiv (modelWithCornersSelf 𝕜 E) I (extChartAt I x).symm (extChartAt I x y)) =
      ContinuousLinearMap.id 𝕜 (TangentSpace (modelWithCornersSelf 𝕜 E) (extChartAt I x y)) := by
  have h := extChartAt_mderiv_right_inverse (PartialEquiv.map_source _ m)
  rw [PartialEquiv.left_inv _ m] at h; exact h

end Deriv

end
end Ray_Ray_Manifold_Manifold

-- ===== Ray.Manifold.Analytic =====
section Ray_Ray_Manifold_Analytic
/-!
## Facts about analytic manifolds

This file used to define `AnalyticManifold`, but now `IsManifold I ω M` handles that natively!
-/

open ChartedSpace (chartAt)
open Function (uncurry)
open Set
open scoped ContDiff Manifold Topology
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

variable {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G C : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H D : Type} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
variable {M : Type} {I : ModelWithCorners 𝕜 E A} [TopologicalSpace M]
variable {N : Type} {J : ModelWithCorners 𝕜 F B} [TopologicalSpace N]
variable {O : Type} {K : ModelWithCorners 𝕜 G C} [TopologicalSpace O]
variable {P : Type} {L : ModelWithCorners 𝕜 H D} [TopologicalSpace P]
variable [ChartedSpace A M] [ChartedSpace B N] [ChartedSpace C O] [ChartedSpace D P]

/-- Functions are `ContMDiffAt` iff they are continuous and analytic in charts -/
theorem mAnalyticAt_iff {f : M → N} {x : M} [CompleteSpace F] :
    ContMDiffAt I J ω f x ↔ ContinuousAt f x ∧
      AnalyticWithinAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) (range I)
      (extChartAt I x x) := by
  rw [contMDiffAt_iff, contDiffWithinAt_omega_iff_analyticWithinAt]

/-- Functions are `ContMDiffAt` iff they are continuous and analytic in charts -/
theorem mAnalyticAt_iff_of_boundaryless [I.Boundaryless] [CompleteSpace F] {f : M → N}
    {x : M} :
    ContMDiffAt I J ω f x ↔ ContinuousAt f x ∧
      AnalyticAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  simp only [mAnalyticAt_iff, I.range_eq_univ, analyticWithinAt_univ]

/-- Functions are `ContMDiff` iff they are continuous and analytic in charts everywhere -/
theorem mAnalytic_iff {f : M → N} [CompleteSpace F] [IsManifold I ω M] [IsManifold J ω N] :
    ContMDiff I J ω f ↔ Continuous f ∧
      ∀ x : M, AnalyticWithinAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm)
        (range I) (extChartAt I x x) := by
  simp only [ContMDiff, contMDiffAt_iff, continuous_iff_continuousAt,
    contDiffWithinAt_omega_iff_analyticWithinAt]
  aesop

/-- Functions are `ContMDiff` iff they are continuous and analytic in charts everywhere -/
theorem mAnalytic_iff_of_boundaryless [I.Boundaryless] [IsManifold I ω M] [IsManifold J ω N]
    [CompleteSpace F] {f : M → N} :
    ContMDiff I J ω f ↔ Continuous f ∧
      ∀ x : M, AnalyticAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm)
        (extChartAt I x x) := by
  simp only [mAnalytic_iff, I.range_eq_univ, analyticWithinAt_univ]

section Iff

variable (I J)

/-- Analytic functions are analytic, and vice versa -/
theorem analyticAt_iff_mAnalyticAt [I.Boundaryless] [ChartedSpace A E] [IsManifold I ω E]
    [ChartedSpace B F] [IsManifold J ω F] [ExtChartEqRefl I] [ExtChartEqRefl J] [CompleteSpace F]
    {f : E → F} {x : E} : AnalyticAt 𝕜 f x ↔ ContMDiffAt I J ω f x := by
  simp only [mAnalyticAt_iff_of_boundaryless, extChartAt_eq_refl, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, Function.id_comp, Function.comp_id, id_eq, iff_and_self]
  exact AnalyticAt.continuousAt

end Iff

/-- Analytic functions are analytic -/
theorem AnalyticAt.mAnalyticAt {f : E → F} {x : E} (fa : AnalyticAt 𝕜 f x) [CompleteSpace F]
    (I : ModelWithCorners 𝕜 E A) [ChartedSpace A E] [IsManifold I ω E] [ExtChartEqRefl I]
    (J : ModelWithCorners 𝕜 F B) [ChartedSpace B F] [IsManifold J ω F] [ExtChartEqRefl J] :
    ContMDiffAt I J ω f x := by
  simp only [mAnalyticAt_iff, fa.continuousAt, true_and, extChartAt_eq_refl, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, Function.id_comp, Function.comp_id, id_eq]
  exact fa.analyticWithinAt

/-- ContMDiff functions are analytic -/
theorem ContMDiffAt.analyticAt [CompleteSpace F] (I : ModelWithCorners 𝕜 E A) [I.Boundaryless]
    [ChartedSpace A E] [IsManifold I ω E] [ExtChartEqRefl I] (J : ModelWithCorners 𝕜 F B)
    [ChartedSpace B F] [IsManifold J ω F] [ExtChartEqRefl J] {f : E → F} {x : E} :
    ContMDiffAt I J ω f x → AnalyticAt 𝕜 f x :=
  (analyticAt_iff_mAnalyticAt _ _).mpr

/-- Complex powers `f x ^ g x` are analytic if `f x` avoids the negative real axis  -/
theorem ContMDiffAt.cpow [NormedSpace ℂ E] [CompleteSpace E] {I : ModelWithCorners ℂ E A}
    [IsManifold I ω M] {f g : M → ℂ} {x : M} (fa : ContMDiffAt I (𝓘(ℂ, ℂ)) ω f x)
    (ga : ContMDiffAt I (𝓘(ℂ, ℂ)) ω g x) (a : 0 < (f x).re ∨ (f x).im ≠ 0) :
    ContMDiffAt I (𝓘(ℂ, ℂ)) ω (fun x ↦ f x ^ g x) x := by
  have e : (fun x ↦ f x ^ g x) = (fun p : ℂ × ℂ ↦ p.1 ^ p.2) ∘ fun x ↦ (f x, g x) := rfl
  rw [e]
  refine ((analyticAt_fst.cpow analyticAt_snd ?_).mAnalyticAt _ _).comp _ (fa.prodMk ga)
  exact a

/-- If we're analytic at a point, we're locally analytic.
This is true even with boundary, but for now we prove only the `Boundaryless` case. -/
theorem ContMDiffAt.eventually [I.Boundaryless] [J.Boundaryless] [CompleteSpace E]
    [CompleteSpace F] [IsManifold I ω M] [IsManifold J ω N] {f : M → N} {x : M}
    (fa : ContMDiffAt I J ω f x) : ∀ᶠ y in 𝓝 x, ContMDiffAt I J ω f y := by
  have ea := (mAnalyticAt_iff_of_boundaryless.mp fa).2.eventually_analyticAt
  simp only [← map_extChartAt_nhds_of_boundaryless, Filter.eventually_map] at ea
  filter_upwards [ea, (fa.continuousAt.eventually_mem ((isOpen_extChartAt_source (f x)).mem_nhds
    (mem_extChartAt_source (I := J) (f x)))).eventually_nhds,
    (isOpen_extChartAt_source x).eventually_mem (mem_extChartAt_source (I := I) x)]
  intro y a fm m
  have h := a.mAnalyticAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 F)
  clear a
  have h' := ((contMDiffOn_extChartAt_symm _).contMDiffAt
    (extChartAt_target_mem_nhds' (PartialEquiv.map_source _ fm.self_of_nhds))).comp_of_eq
      (h.comp _ (contMDiffAt_extChartAt' (extChartAt_source I x ▸ m))) ?_
  · apply h'.congr_of_eventuallyEq
    clear h h'
    apply ((isOpen_extChartAt_source x).eventually_mem m).mp
    refine fm.mp (.of_forall fun z mf m ↦ ?_)
    simp only [PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ mf, Function.comp_def]
  · simp only [Function.comp, PartialEquiv.left_inv _ m]

/-- The domain of analyticity is open -/
theorem isOpen_mAnalyticAt [I.Boundaryless] [J.Boundaryless] [CompleteSpace E]
    [CompleteSpace F] [IsManifold I ω M] [IsManifold J ω N] {f : M → N} :
    IsOpen {x | ContMDiffAt I J ω f x} := by
  rw [isOpen_iff_eventually]; intro x fa; exact fa.eventually

/-- `ContMDiffOnNhd` restricts to subsets -/
lemma ContMDiffOnNhd.mono {f : M → N} {s t : Set M} (fa : ContMDiffOnNhd I J f s) (st : t ⊆ s) :
    ContMDiffOnNhd I J f t := fun x m ↦ fa x (st m)

/-- `ContMDiffOnNhd` extends `ContMDiffOn` -/
lemma ContMDiffOnNhd.contMDiffOn {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s) :
    ContMDiffOn I J ω f s := fun x m ↦ (fa x m).contMDiffWithinAt

/-- `ContMDiffOnNhd` implies analyticity -/
lemma ContMDiffOnNhd.contMDiffAt {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s)
    {x : M} (xs : x ∈ s) : ContMDiffAt I J ω f x := fa x xs

/-- `ContMDiffOnNhd` implies continuity -/
lemma ContMDiffOnNhd.continuousAt {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s)
    {x : M} (xs : x ∈ s) : ContinuousAt f x := (fa x xs).continuousAt

/-- `ContMDiffOnNhd` implies continuity on the domain -/
lemma ContMDiffOnNhd.continuousOn {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s) :
    ContinuousOn f s := fun x m ↦ (fa x m).continuousAt.continuousWithinAt

end
end Ray_Ray_Manifold_Analytic

-- ===== Ray.Manifold.OneDimension =====
section Ray_Ray_Manifold_OneDimension
/-!
## Special properties of 1D complex manifolds

One complex dimension is special, and 1D complex manifolds inherit this specialness.

Unfortunately, a lot of proofs here are messy, as we abuse the definitional quality
of `TangentSpace I z = ℂ` to do noncanonical field arithmetic over `ℂ`.
-/

open Filter (Tendsto)
open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff Manifold Topology
noncomputable section

variable {S : Type} [TopologicalSpace S] [cs : ChartedSpace ℂ S]
variable {T : Type} [TopologicalSpace T] [ct : ChartedSpace ℂ T]
variable {U : Type} [TopologicalSpace U] [cu : ChartedSpace ℂ U]

/-- 1D tangent spaces are nontrivial -/
instance one_dimension_tangentSpace_nontrivial (z : S) : Nontrivial (TangentSpace I z) :=
  inferInstanceAs (Nontrivial ℂ)

/-- 1D tangent spaces are `NormedAddCommGroup`s -/
instance oneDimensionTangentSpaceNormedAddCommGroup (z : S) :
    NormedAddCommGroup (TangentSpace I z) :=
  inferInstanceAs (NormedAddCommGroup ℂ)

/-- 1D tangent spaces are `NormedSpace`s -/
instance oneDimensionTangentSpaceNormedSpace (z : S) : NormedSpace ℂ (TangentSpace I z) :=
  inferInstanceAs (NormedSpace ℂ ℂ)

/-- The tangent space norm is `abs`, if we unpack types -/
theorem tangentSpace_norm_eq_complex_norm (z : S) (x : TangentSpace I z) :
    ‖x‖ = Complex.instNorm.norm x := rfl

/-- Explicitly identify a 1D tangent space with `ℂ`.
    `TangentSpace` is no longer reducible, so we use this to make instance resolution
    see `ℂ` while remaining definitionally the identity. -/
def tangentToC {z : S} (x : TangentSpace I z) : ℂ := x

/-- Explicitly identify `ℂ` with a 1D tangent space (definitionally the identity) -/
def tangentOfC {z : S} (x : ℂ) : TangentSpace I z := x

/-- 1D tangent space maps are (noncanonically!) equivalent to `ℂ` (linear equivalence) -/
def mderivToScalar' (z : S) (w : T) : (TangentSpace I z →L[ℂ] TangentSpace I w) ≃ₗ[ℂ] ℂ where
  toFun x := tangentToC (x (tangentOfC 1))
  invFun x := x • ContinuousLinearMap.id ℂ ℂ
  map_add' x y := rfl
  map_smul' s x := rfl
  left_inv := by
    intro x
    apply ContinuousLinearMap.ext; intro s
    show tangentToC (z := w) (x (tangentOfC (z := z) 1)) * tangentToC (z := z) s
      = tangentToC (z := w) (x s)
    have h := x.map_smul (tangentToC (z := z) s) (tangentOfC (z := z) 1)
    have e1 : tangentToC (z := z) s • tangentOfC (z := z) 1 = s := by
      show tangentToC (z := z) s * 1 = tangentToC (z := z) s
      exact mul_one _
    rw [e1] at h
    rw [h]
    show tangentToC (z := w) (x (tangentOfC (z := z) 1)) * tangentToC (z := z) s
      = tangentToC (z := z) s * tangentToC (z := w) (x (tangentOfC (z := z) 1))
    exact mul_comm _ _
  right_inv := fun x ↦ mul_one x

/-- 1D tangent space maps are (noncanonically!) equivalent to `ℂ` (continuous linear equivalence) -/
def mderivToScalar (z : S) (w : T) : (TangentSpace I z →L[ℂ] TangentSpace I w) ≃L[ℂ] ℂ where
  toLinearEquiv := mderivToScalar' z w
  continuous_toFun := by
    show Continuous fun f : ℂ →L[ℂ] ℂ ↦ f 1
    rw [Metric.continuous_iff]; intro x e ep; use e / 2, half_pos ep; intro y xy
    simp only [dist_eq_norm] at xy ⊢
    have b := ContinuousLinearMap.le_of_opNorm_le (y - x) xy.le (1 : ℂ)
    simp only [_root_.sub_apply, norm_one, mul_one] at b ⊢
    exact lt_of_le_of_lt b (half_lt_self ep)
  continuous_invFun := by
    show Continuous fun x : ℂ ↦ (x • ContinuousLinearMap.id ℂ ℂ : ℂ →L[ℂ] ℂ)
    rw [Metric.continuous_iff]; intro x e ep; use e / 2, half_pos ep; intro y xy
    simp only [dist_eq_norm] at xy ⊢
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (half_pos ep).le fun s ↦ ?_)
      (half_lt_self ep)
    show ‖y * s - x * s‖ ≤ e / 2 * ‖s‖
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right xy.le (norm_nonneg _)

/-- Given nonzero `u`, a tangent space map `x` is `0` iff `x u = 0` -/
theorem mderiv_eq_zero_iff {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w)
    (u : TangentSpace I z) : f u = 0 ↔ f = 0 ∨ u = 0 := by
  constructor
  · rw [or_iff_not_imp_right]; intro f0 u0
    apply ContinuousLinearMap.ext; intro v
    show f v = 0
    have u0' : tangentToC u ≠ 0 := u0
    have e : v = (tangentToC v * (tangentToC u)⁻¹) • u := by
      show tangentToC v = tangentToC v * (tangentToC u)⁻¹ * tangentToC u
      rw [mul_assoc, inv_mul_cancel₀ u0', mul_one]
    rw [e, f.map_smul, f0, smul_zero]
  · intro h; cases' h with h h
    · rw [h]; rfl
    · rw [h]; exact f.map_zero

/-- Given nonzero `u`, a tangent space map `x` is `0` iff `x u = 0` -/
theorem mderiv_eq_zero_iff' {z : S} {w : T} {f : TangentSpace I z →L[ℂ] TangentSpace I w}
    {u : TangentSpace I z} (u0 : u ≠ 0) : f u = 0 ↔ f = 0 := by
  simp only [mderiv_eq_zero_iff, u0, or_false]

/-- Given nonzero `u`, a tangent space map `x` is `≠ 0` iff `x u ≠ 0` -/
theorem mderiv_ne_zero_iff {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w)
    (u : TangentSpace I z) : f u ≠ 0 ↔ f ≠ 0 ∧ u ≠ 0 := by
  simp only [← not_or]; exact Iff.not (mderiv_eq_zero_iff _ _)

/-- Given nonzero `u`, a tangent space map `x` is `≠ 0` iff `x u ≠ 0` -/
theorem mderiv_ne_zero_iff' {z : S} {w : T} {f : TangentSpace I z →L[ℂ] TangentSpace I w}
    {u : TangentSpace I z} (u0 : u ≠ 0) : f u ≠ 0 ↔ f ≠ 0 := by
  simp only [ne_eq, mderiv_ne_zero_iff, u0, not_false_eq_true, and_true]

/-- 1D map composition is zero iff either side is -/
theorem mderiv_comp_eq_zero_iff {x : S} {y : T} {z : U}
    (f : TangentSpace I y →L[ℂ] TangentSpace I z) (g : TangentSpace I x →L[ℂ] TangentSpace I y) :
    f.comp g = 0 ↔ f = 0 ∨ g = 0 := by
  rcases exists_ne (0 : TangentSpace I x) with ⟨t, t0⟩
  constructor
  · intro h; simp only [← mderiv_eq_zero_iff' t0, ContinuousLinearMap.comp_apply] at h
    by_cases g0 : g t = 0
    right; rw [mderiv_eq_zero_iff' t0] at g0; exact g0
    left; rwa [← mderiv_eq_zero_iff' g0]
  · intro h; cases' h with h h; simp only [h, g.zero_comp]; simp only [h, f.comp_zero]

/-- 1D map composition is nonzero if both sides are -/
theorem mderiv_comp_ne_zero {x : S} {y : T} {z : U}
    (f : TangentSpace I y →L[ℂ] TangentSpace I z) (g : TangentSpace I x →L[ℂ] TangentSpace I y) :
    f ≠ 0 → g ≠ 0 → f.comp g ≠ 0 := by
  intro f0 g0; simp only [Ne, mderiv_comp_eq_zero_iff, f0, g0, or_self_iff, not_false_iff]

/-- Nonzero `mfderiv` implies differentiability -/
theorem has_mfderiv_at_of_mderiv_ne_zero {f : S → T} {x : S} (d0 : mfderiv I I f x ≠ 0) :
    MDifferentiableAt I I f x := by
  contrapose d0
  simp only [mfderiv, d0]
  exact if_neg fun h ↦ h

/-- If two functions have nonzero derivative, their composition has nonzero derivative -/
theorem mderiv_comp_ne_zero' {f : T → U} {g : S → T} {x : S} :
    mfderiv I I f (g x) ≠ 0 → mfderiv I I g x ≠ 0 → mfderiv I I (fun x ↦ f (g x)) x ≠ 0 := by
  intro df dg
  have e : (fun x ↦ f (g x)) = f ∘ g := rfl
  rw [e, mfderiv_comp x (has_mfderiv_at_of_mderiv_ne_zero df) (has_mfderiv_at_of_mderiv_ne_zero dg)]
  exact mderiv_comp_ne_zero _ _ df dg

/-- Nonzero 1D derivatives are invertible -/
def mderivEquiv {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w)
    (f0 : f ≠ 0) : TangentSpace I z ≃L[ℂ] TangentSpace I w where
  toFun := f
  map_add' := f.map_add'
  map_smul' := f.map_smul'
  invFun x := tangentOfC ((tangentToC (f (tangentOfC 1)))⁻¹ * tangentToC x)
  left_inv := by
    intro x
    have u0 : tangentOfC (z := z) 1 ≠ 0 := by
      show (1 : ℂ) ≠ 0
      exact one_ne_zero
    have fu0 : tangentToC (f (tangentOfC 1)) ≠ 0 := (mderiv_ne_zero_iff' u0).mpr f0
    have e : ∀ y : TangentSpace I z,
        tangentToC (f y) = tangentToC (f (tangentOfC 1)) * tangentToC y := by
      intro y
      have h := f.map_smul (tangentToC y) (tangentOfC (z := z) 1)
      have e1 : tangentToC y • tangentOfC (z := z) 1 = y := by
        show tangentToC y * 1 = tangentToC y
        exact mul_one _
      rw [e1] at h
      rw [h]
      show tangentToC y * tangentToC (f (tangentOfC 1))
        = tangentToC (f (tangentOfC 1)) * tangentToC y
      exact mul_comm _ _
    show (tangentToC (f (tangentOfC 1)))⁻¹ * tangentToC (f x) = tangentToC x
    rw [e x, ← mul_assoc, inv_mul_cancel₀ fu0, one_mul]
  right_inv := by
    intro x
    have u0 : tangentOfC (z := z) 1 ≠ 0 := by
      show (1 : ℂ) ≠ 0
      exact one_ne_zero
    have fu0 : tangentToC (f (tangentOfC 1)) ≠ 0 := (mderiv_ne_zero_iff' u0).mpr f0
    have e : ∀ y : TangentSpace I z,
        tangentToC (f y) = tangentToC (f (tangentOfC 1)) * tangentToC y := by
      intro y
      have h := f.map_smul (tangentToC y) (tangentOfC (z := z) 1)
      have e1 : tangentToC y • tangentOfC (z := z) 1 = y := by
        show tangentToC y * 1 = tangentToC y
        exact mul_one _
      rw [e1] at h
      rw [h]
      show tangentToC y * tangentToC (f (tangentOfC 1))
        = tangentToC (f (tangentOfC 1)) * tangentToC y
      exact mul_comm _ _
    show tangentToC (f (tangentOfC ((tangentToC (f (tangentOfC 1)))⁻¹ * tangentToC x)))
      = tangentToC x
    rw [e _]
    show tangentToC (f (tangentOfC 1)) * ((tangentToC (f (tangentOfC 1)))⁻¹ * tangentToC x)
      = tangentToC x
    rw [← mul_assoc, mul_inv_cancel₀ fu0, one_mul]
  continuous_toFun := f.cont
  continuous_invFun := by
    show Continuous fun x : ℂ ↦ (tangentToC (f (tangentOfC 1)))⁻¹ * x
    exact continuous_const.mul continuous_id

theorem mderivEquiv_apply {z : S} {w : T} {f : TangentSpace I z →L[ℂ] TangentSpace I w}
    (f0 : f ≠ 0) (x : TangentSpace I z) : mderivEquiv f f0 x = f x := by rfl

theorem mderivEquiv_eq {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w)
    (f0 : f ≠ 0) : ↑(mderivEquiv f f0) = f := by
  apply ContinuousLinearMap.ext; intro x; rfl

/-- Identity derivatives are nonzero -/
theorem id_mderiv_ne_zero {z : S} : mfderiv I I (fun z ↦ z) z ≠ 0 := by
  have d : MDifferentiableAt I I (fun z ↦ z) z := mdifferentiableAt_id
  simp only [mfderiv, d, if_true, writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
    fderivWithin_univ]
  have e : (fun w ↦ extChartAt I z ((extChartAt I z).symm w)) =ᶠ[𝓝 (extChartAt I z z)] id := by
    apply ((isOpen_extChartAt_target z).eventually_mem (mem_extChartAt_target z)).mp
    refine .of_forall fun w m ↦ ?_
    simp only [id, PartialEquiv.right_inv _ m]
  simp only [e.fderiv_eq, fderiv_id, Ne, ContinuousLinearMap.ext_iff, not_forall,
    ContinuousLinearMap.id_apply, Function.comp_def]
  refine ⟨(1 : ℂ), ?_⟩
  show ¬(1 : ℂ) = 0
  exact one_ne_zero

/-- Critical points of iterations are precritical points -/
theorem critical_iter {f : S → S} {n : ℕ} {z : S} (fa : ContMDiff I I ω f)
    (c : Critical f^[n] z) : Precritical f z := by
  induction' n with n h
  · rw [Function.iterate_zero, Critical, mfderiv_id, ← ContinuousLinearMap.opNorm_zero_iff,
      ContinuousLinearMap.norm_id] at c
    norm_num at c
  · rw [Function.iterate_succ', Critical,
      mfderiv_comp z ((fa _).mdifferentiableAt (by decide))
       ((fa.iterate _ _).mdifferentiableAt (by decide)),
      mderiv_comp_eq_zero_iff] at c
    cases' c with c c; use n, c; exact h c

variable [IsManifold I ω S] [IsManifold I ω T] [IsManifold I ω U]

/-- Chart derivatives are nonzero -/
theorem extChartAt_mderiv_ne_zero' {z w : S} (m : w ∈ (extChartAt I z).source) :
    mfderiv I I (extChartAt I z) w ≠ 0 := by
  rcases exists_ne (0 : TangentSpace I w) with ⟨t, t0⟩
  rw [← mderiv_ne_zero_iff' t0]; contrapose t0
  have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_left_inverse m) t
  simp only [ContinuousLinearMap.comp_apply, t0, map_zero, ContinuousLinearMap.id_apply] at h
  exact h.symm

/-- Chart derivatives are nonzero -/
theorem extChartAt_symm_mderiv_ne_zero' {z : S} {w : ℂ} (m : w ∈ (extChartAt I z).target) :
    mfderiv I I (extChartAt I z).symm w ≠ 0 := by
  rcases exists_ne (0 : TangentSpace I w) with ⟨t, t0⟩
  rw [← mderiv_ne_zero_iff' t0]; contrapose t0
  have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_right_inverse m) t
  simp only [ContinuousLinearMap.comp_apply, t0, map_zero, ContinuousLinearMap.id_apply] at h
  exact h.symm

/-- Chart derivatives are nonzero -/
theorem extChartAt_mderiv_ne_zero (z : S) : mfderiv I I (extChartAt I z) z ≠ 0 :=
  extChartAt_mderiv_ne_zero' (mem_extChartAt_source z)

/-- Chart derivatives are nonzero -/
theorem extChartAt_symm_mderiv_ne_zero (z : S) :
    mfderiv I I (extChartAt I z).symm (extChartAt I z z) ≠ 0 :=
  extChartAt_symm_mderiv_ne_zero' (mem_extChartAt_target z)

/-- Nonzeroness of `mfderiv` reduces to nonzeroness of `deriv` -/
theorem mfderiv_eq_zero_iff_deriv_eq_zero {f : ℂ → ℂ} {z : ℂ} :
    mfderiv I I f z = 0 ↔ deriv f z = 0 := by
  by_cases d : DifferentiableAt ℂ f z
  · constructor
    · have h := d.mdifferentiableAt.hasMFDerivAt; intro e; rw [e] at h
      have p : HasFDerivAt f (0 : ℂ →L[ℂ] ℂ) z := hasMFDerivAt_iff_hasFDerivAt.mp h
      simpa using p.hasDerivAt.deriv
    · have h := d.hasDerivAt
      intro e
      rw [e] at h
      have p := h.hasFDerivAt.hasMFDerivAt
      simp only [ContinuousLinearMap.toSpanSingleton_zero] at p
      exact p.mfderiv
  · have d' : ¬MDifferentiableAt I I f z := by
      contrapose d; exact d.differentiableAt
    simp only [deriv_zero_of_not_differentiableAt d, mfderiv_zero_of_not_mdifferentiableAt d']

/-- `mfderiv ≠ 0` iff `deriv ≠ 0` -/
theorem mfderiv_ne_zero_iff_deriv_ne_zero {f : ℂ → ℂ} {z : ℂ} :
    mfderiv I I f z ≠ 0 ↔ deriv f z ≠ 0 := by rw [not_iff_not, mfderiv_eq_zero_iff_deriv_eq_zero]

/-!
## Facts about `mfderiv` related to continuity and analyticity

These facts would ideally follow from continuity and analyticity of `mfderiv`, but we can't
express that directly as `mfderiv` lives in a different type at each point.  Rather than detour
into the necessary theory, I'm going to express what I need in coordinates for now.
-/

/-- A curried function in coordinates -/
def inChart (f : ℂ → S → T) (c : ℂ) (z : S) : ℂ → ℂ → ℂ := fun e w ↦
  extChartAt I (f c z) (f e ((extChartAt I z).symm w))

/-- `inChart` is analytic -/
theorem ContMDiffAt.inChart {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) :
    AnalyticAt ℂ (uncurry (inChart f c z)) (c, _root_.extChartAt I z z) := by
  apply ContMDiffAt.analyticAt II I
  apply (contMDiffAt_extChartAt' (extChartAt_source I (f c z) ▸
    (mem_extChartAt_source (f c z)))).comp_of_eq
  apply fa.comp₂_of_eq contMDiffAt_fst
  apply ((contMDiffOn_extChartAt_symm _).contMDiffAt
    (extChartAt_target_mem_nhds' (mem_extChartAt_target z))).comp_of_eq contMDiffAt_snd
  repeat' simp only [PartialEquiv.left_inv _ (mem_extChartAt_source z)]

/-- `inChart` preserves critical points locally -/
theorem inChart_critical {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, z),
      mfderiv I I (f p.1) p.2 = 0 ↔ deriv (inChart f c z p.1) (extChartAt I z p.2) = 0 := by
  apply (fa.continuousAt.eventually_mem ((isOpen_extChartAt_source (f c z)).mem_nhds
    (mem_extChartAt_source (I := I) (f c z)))).mp
  apply ((isOpen_extChartAt_source (c, z)).eventually_mem (mem_extChartAt_source (I := II) _)).mp
  refine fa.eventually.mp (.of_forall ?_); intro ⟨e, w⟩ fa m fm
  simp only [extChartAt_prod, PartialEquiv.prod_source, extChartAt_eq_refl,
    PartialEquiv.refl_source, mem_prod, mem_univ, true_and] at m
  simp only [uncurry] at fm
  have m' := PartialEquiv.map_source _ m
  simp only [← mfderiv_eq_zero_iff_deriv_eq_zero]
  have cd : ContMDiffAt I I ω (extChartAt I (f c z)) (f e w) := contMDiffAt_extChartAt' (extChartAt_source I (f c z) ▸ fm)
  have fd : ContMDiffAt I I ω (f e ∘ (extChartAt I z).symm) (extChartAt I z w) := by
    simp only [Function.comp_def]
    exact ContMDiffAt.comp_of_eq fa.along_snd ((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' m'))
      (PartialEquiv.right_inv _ m)
  have ce : inChart f c z e = extChartAt I (f c z) ∘ f e ∘ (extChartAt I z).symm := rfl
  rw [ce,
    mfderiv_comp_of_eq (cd.mdifferentiableAt (by decide)) (fd.mdifferentiableAt (by decide)) _,
    mfderiv_comp_of_eq (fa.along_snd.mdifferentiableAt (by decide))
      (((contMDiffOn_extChartAt_symm _).contMDiffAt
        (extChartAt_target_mem_nhds' m')).mdifferentiableAt WithTop.top_ne_zero)]
  · simp only [mderiv_comp_eq_zero_iff, Function.comp]
    rw [(extChartAt I z).left_inv m]
    simp only [extChartAt_mderiv_ne_zero' fm, false_or]
    constructor
    · intro h; left; exact h
    · intro h; cases' h with h h; exact h; simpa only using extChartAt_symm_mderiv_ne_zero' m' h
  · exact PartialEquiv.left_inv _ m
  · simp only [Function.comp, PartialEquiv.left_inv _ m]

/-- `mfderiv` is nonzero near where it is nonzero (parameterized version) -/
theorem mfderiv_ne_zero_eventually' {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) (f0 : mfderiv I I (f c) z ≠ 0) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, z), mfderiv I I (f p.1) p.2 ≠ 0 := by
  set g := inChart f c z
  have g0 := inChart_critical fa
  have g0n : ∀ᶠ p : ℂ × S in 𝓝 (c, z), deriv (g p.1) (extChartAt I z p.2) ≠ 0 := by
    refine ContinuousAt.eventually_ne ?_ ?_
    · have e : (fun p : ℂ × S ↦ deriv (g p.1) (extChartAt I z p.2)) =
        (fun p : ℂ × ℂ ↦ deriv (g p.1) p.2) ∘ fun p : ℂ × S ↦ (p.1, extChartAt I z p.2) := rfl
      rw [e]
      exact fa.inChart.deriv2.continuousAt.comp_of_eq
        (continuousAt_fst.prodMk ((continuousAt_extChartAt z).comp_of_eq continuousAt_snd rfl))
        rfl
    · contrapose f0; rw [g0.self_of_nhds]; exact f0
  refine g0.mp (g0n.mp (.of_forall fun w g0 e ↦ ?_))
  rw [Ne, e]; exact g0

/-- `mfderiv` is nonzero near where it is nonzero -/
theorem mfderiv_ne_zero_eventually {f : S → T} {z : S} (fa : ContMDiffAt I I ω f z)
    (f0 : mfderiv I I f z ≠ 0) : ∀ᶠ w in 𝓝 z, mfderiv I I f w ≠ 0 := by
  set c : ℂ := 0
  set g : ℂ → S → T := fun _ z ↦ f z
  have ga : ContMDiffAt II I ω (uncurry g) (c, z) := by
    have e : uncurry g = f ∘ fun p ↦ p.2 := rfl; rw [e]
    apply ContMDiffAt.comp_of_eq fa contMDiffAt_snd; simp only
  have pc : Tendsto (fun z ↦ (c, z)) (𝓝 z) (𝓝 (c, z)) := continuousAt_const.prodMk continuousAt_id
  exact pc.eventually (mfderiv_ne_zero_eventually' ga f0)

/-- The set of noncritical points is open -/
theorem isOpen_noncritical {f : ℂ → S → T} (fa : ContMDiff II I ω (uncurry f)) :
    IsOpen {p : ℂ × S | ¬Critical (f p.1) p.2} := by
  rw [isOpen_iff_eventually]; intro ⟨c, z⟩ m; exact mfderiv_ne_zero_eventually' (fa _) m

/-- The set of critical points is closed -/
theorem isClosed_critical {f : ℂ → S → T} (fa : ContMDiff II I ω (uncurry f)) :
    IsClosed {p : ℂ × S | Critical (f p.1) p.2} := by
  have c := (isOpen_noncritical fa).isClosed_compl
  simp only [compl_ofPred, not_not] at c; exact c

/-- Osgood's theorem on 2D product manifolds: separate analyticity + continuity
    implies joint analyticity.  I'm not sure if a Hartogs' analogue is possible,
    since we use continuity to remain within the right charts. -/
theorem osgoodManifold {f : S × T → U} (fc : Continuous f)
    (f0 : ∀ x y, ContMDiffAt I I ω (fun x ↦ f (x, y)) x)
    (f1 : ∀ x y, ContMDiffAt I I ω (fun y ↦ f (x, y)) y) : ContMDiff II I ω f := by
  rw [mAnalytic_iff_of_boundaryless]; use fc; intro p; apply osgood_at'
  have fm : ∀ᶠ q in 𝓝 (extChartAt II p p),
      f ((extChartAt II p).symm q) ∈ (extChartAt I (f p)).source := by
    refine (fc.continuousAt.comp (continuousAt_extChartAt_symm p)).eventually_mem
        ((isOpen_extChartAt_source (f p)).mem_nhds ?_)
    simp only [Function.comp, (extChartAt II p).left_inv (mem_extChartAt_source _)]
    apply mem_extChartAt_source
  apply ((isOpen_extChartAt_target p).eventually_mem (mem_extChartAt_target p)).mp
  refine fm.mp (.of_forall fun q fm m ↦ ⟨?_, ?_, ?_⟩)
  · exact (continuousAt_extChartAt' fm).comp_of_eq
        (fc.continuousAt.comp (continuousAt_extChartAt_symm'' m)) rfl
  · apply ContMDiffAt.analyticAt I I
    refine (contMDiffAt_extChartAt' (extChartAt_source I (f p) ▸ fm)).comp_of_eq ?_ rfl
    rw [extChartAt_prod] at m
    simp only [Function.comp, extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
      PartialEquiv.prod_target, mem_prod_eq] at m ⊢
    exact (f0 _ _).comp _ ((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' m.1))
  · apply ContMDiffAt.analyticAt I I
    refine (contMDiffAt_extChartAt' (extChartAt_source I (f p) ▸ fm)).comp_of_eq ?_ rfl
    rw [extChartAt_prod] at m
    simp only [Function.comp, extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
      PartialEquiv.prod_target, mem_prod_eq] at m ⊢
    exact (f1 _ _).comp _ ((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' m.2))

end
end Ray_Ray_Manifold_OneDimension


