-- Prove2me | Definitions.Def_ray_osgood_series
-- name    : ray_osgood_series
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T20:53:31.075623+00:00
-- url     : https://prove2.me/theorems/c0529181-802d-44ee-bc7a-95d609c18250
-- title:
--   ray (2/12): Osgood's lemma and uniform limits of analytic functions
-- statement:
--   **Osgood's lemma**: a function $f : \mathbb{C}^2 \to E$ that is continuous and separately analytic in each variable is jointly analytic. The file also proves that uniform limits of analytic functions are analytic (via Cauchy integrals), gives results on power series and on analyticity of infinite sums, and gives convergence and analyticity of infinite products $\prod_n f_n(z)$.
--
--   This file is part 2 of 12 of a verbatim flattening of Geoffrey Irving's Lean 4 formalization *ray* (https://github.com/girving/ray, Apache License 2.0). Together the 12 files prove that the Mandelbrot set is connected. Each original ray module is wrapped in its own `section`, and module-system keywords are removed. A few mechanical edits avoid clashes with the full Mathlib import and avoid syntax extensions: a duplicated private definition is dropped, `ContinuousOn.partialSups` is renamed to `ContinuousOn.rayPartialSups`, `Finset.antidiagonal` is written as `Finset.HasAntidiagonal.antidiagonal`, the `bound_destruct` attribute macro is inlined, and the notation `𝕊` is replaced by `(OnePoint ℂ)`. The files are split only because of the compile-time limit. Declaration names are ray's own.
-- source:
--   Geoffrey Irving, ray: The Mandelbrot set is connected (Lean 4 formalization), https://github.com/girving/ray (Apache License 2.0), commit of 2026-08-16; module list in the file header. Mathematical background: A. Douady and J. H. Hubbard, Itération des polynômes quadratiques complexes, C. R. Acad. Sci. Paris 294 (1982); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Section 9 and Appendix; Carleson–Gamelin, Complex Dynamics, Ch. VIII.

import Definitions.Def_ray_analytic_basics

/-!
# ray (2/12): Osgood's lemma and uniform limits of analytic functions

Part 2 of 12 of a flattened copy of Geoffrey Irving's Lean 4 formalization *ray*
(https://github.com/girving/ray, Apache License 2.0, Copyright Geoffrey Irving), which proves that
the Mandelbrot set is connected. Each original module is wrapped in its own `section`;
module-system keywords are removed, and a few names are adjusted to avoid clashes with Mathlib.

Original modules in this file:
* `Ray.Hartogs.Osgood`
* `Ray.Analytic.Holomorphic`
* `Ray.Analytic.Uniform`
* `Ray.Analytic.Series`
* `Ray.Analytic.Products`
-/

-- ===== Ray.Hartogs.Osgood =====
section Ray_Ray_Hartogs_Osgood
/-!
## Osgood's lemma for two variables

We show that continuous, separately analytic functions over ℂ are jointly analytic:

  https://en.wikipedia.org/wiki/Osgood's_lemma

The continuity assumption is unnecessary: see `Hartogs.lean` for the stronger version requiring only
separate analyticity.  We prove it for two variables only, as that's all we need; if more variables
if need, Hartogs' should be generalized, not Osgood's.

## Proof details

Osgood's lemma follows from the multidimensional Cauchy integral formula

  `f c = (2πi)^(-d) (prod_k ∫_(C k) d(z k)) (prod_k (z k - c k)⁻¹) f z`

The `n`th multidimensional coefficient (with `n : fin d → ℕ`) looks like

  `p n = (2πi)^(-d) (prod_k ∫_(C k) d(z k)) (prod_k (z k - c k)^(-1 - n k)) f z`

For a quick refresher on why the Cauchy power series works, for `c = 0`:

  f_n = (2πi)⁻¹ ∫_C dz z^(-1-n) * f z
  f w = (2πi)⁻¹ ∫_C dz (z - w)⁻¹ * f z
      = (2πi)⁻¹ ∫_C dz (z - z * (w/z))⁻¹ * f z
      = (2πi)⁻¹ ∫_C dz (1 - w/z)⁻¹ * z⁻¹ * f z
      = (2πi)⁻¹ ∫_C dz Σ_n (w/z)^n * z⁻¹ * f z
      = Σ_n w^n (2πi)⁻¹ ∫_C dz  z⁻¹^n * z⁻¹ * f z
-/

open Complex (exp I log)
open Filter (atTop)
open Function (curry uncurry)
open Metric (ball closedBall sphere isOpen_ball ball_subset_closedBall)
open intervalIntegral
open Set
open scoped Real NNReal ENNReal Topology MeasureTheory
noncomputable section

section osgood

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {f : ℂ × ℂ → E}
variable {s : Set (ℂ × ℂ)}
variable {c0 c1 w0 w1 : ℂ}
variable {r b : ℝ}

/-- A measureable, separately analytic function of 2 complex variables near `c`.
    We assume `f` is differentiable in an open neighborhood of the closedBall for simplicity. -/
structure Separate (f : ℂ × ℂ → E) (c0 c1 : ℂ) (r b : ℝ) (s : Set (ℂ × ℂ)) : Prop where
  rp : 0 < r
  so : IsOpen s
  rs : closedBall (c0, c1) r ⊆ s
  fc : ContinuousOn f s
  fa0 : ∀ {c0 c1}, (c0, c1) ∈ s → AnalyticAt ℂ (fun z0 ↦ f (z0, c1)) c0
  fa1 : ∀ {c0 c1}, (c0, c1) ∈ s → AnalyticAt ℂ (fun z1 ↦ f (c0, z1)) c1
  bp : 0 ≤ b
  fb : ∀ {z0 z1}, z0 ∈ sphere c0 r → z1 ∈ sphere c1 r → ‖f (z0, z1)‖ ≤ b

-- Teach `bound` about the positivity fields of `Separate`
attribute [bound_forward] Separate.rp Separate.bp

theorem spheres_subset_closedBall {c0 c1 : ℂ} {r : ℝ} :
    sphere c0 r ×ˢ sphere c1 r ⊆ closedBall (c0, c1) r := by
  rw [←closedBall_prod_same, Set.subset_def]; intro z
  simp only [Set.mem_prod, mem_sphere_iff_norm, Metric.mem_closedBall, and_imp]
  rw [Complex.dist_eq, Complex.dist_eq]
  intro a b; exact ⟨le_of_eq a, le_of_eq b⟩

theorem Separate.rs' (h : Separate f c0 c1 r b s) : sphere c0 r ×ˢ sphere c1 r ⊆ s :=
  le_trans spheres_subset_closedBall h.rs

theorem mem_sphere_closed {z c : ℂ} {r : ℝ} : z ∈ sphere c r → z ∈ closedBall c r := fun h ↦
  Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp h))

/-- Spheres don't contain their center -/
theorem center_not_in_sphere {c z : ℂ} {r : ℝ} (rp : r > 0) (zs : z ∈ sphere c r) : z - c ≠ 0 := by
  simp only [mem_sphere_iff_norm] at zs
  rw [← norm_ne_zero_iff, zs]; exact rp.ne'

/-- `f` is continuous in `z0` -/
theorem Separate.fc0 (h : Separate f c0 c1 r b s) (w1m : w1 ∈ ball c1 r) :
    ContinuousOn (fun z0 ↦ f (z0, w1)) (closedBall c0 r) := by
  refine ContinuousOn.comp h.fc ?_ ?_
  · exact ContinuousOn.prodMk continuousOn_id continuousOn_const
  · intro z0 z0m; apply h.rs
    rw [← closedBall_prod_same]; exact Set.mem_prod.mpr ⟨z0m, ball_subset_closedBall w1m⟩

/-- `f` is continuous in `z1` -/
theorem Separate.fc1 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ closedBall c0 r) :
    ContinuousOn (fun z1 ↦ f (w0, z1)) (closedBall c1 r) := by
  refine ContinuousOn.comp h.fc ?_ ?_
  · exact ContinuousOn.prodMk continuousOn_const continuousOn_id
  · intro z1 z1m; apply h.rs
    rw [← closedBall_prod_same]; exact Set.mem_prod.mpr ⟨w0m, z1m⟩

/-- `f` is differentiable in `z0` -/
theorem Separate.fd0 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ closedBall c0 r)
    (w1m : w1 ∈ closedBall c1 r) : DifferentiableAt ℂ (fun z0 ↦ f (z0, w1)) w0 :=
  haveI m : (w0, w1) ∈ s := by
    apply h.rs; rw [←closedBall_prod_same]; exact Set.mem_prod.mpr ⟨w0m, w1m⟩
  AnalyticAt.differentiableAt (h.fa0 m)

/-- `f` is differentiable in `z1` -/
theorem Separate.fd1 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ closedBall c0 r)
    (w1m : w1 ∈ closedBall c1 r) : DifferentiableAt ℂ (fun z1 ↦ f (w0, z1)) w1 :=
  haveI m : (w0, w1) ∈ s := by
    apply h.rs; rw [←closedBall_prod_same]; exact Set.mem_prod.mpr ⟨w0m, w1m⟩
  AnalyticAt.differentiableAt (h.fa1 m)

/-- The 1D Cauchy series converges as expected
   (rephrasing of `hasSum_cauchy_power_series_integral`) -/
theorem cauchy1_hasSum {f : ℂ → E} {c w : ℂ} {r : ℝ} (rp : r > 0) (fc : ContinuousOn f (sphere c r))
    (wm : w ∈ ball (0 : ℂ) r) :
    HasSum
      (fun n : ℕ ↦ w ^ n • (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z)
      ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - (c + w))⁻¹ • f z) := by
  simp at wm
  have ci : CircleIntegrable f c r := ContinuousOn.circleIntegrable (by linarith) fc
  have h := hasSum_cauchyPowerSeries_integral ci wm
  simp_rw [cauchyPowerSeries_apply] at h
  generalize hs : (2*π*I : ℂ)⁻¹ = s; simp_rw [hs] at h
  generalize hg : (s • ∮ z : ℂ in C(c, r), (z - (c + w))⁻¹ • f z) = g; rw [hg] at h
  simp_rw [div_eq_mul_inv, mul_pow, ← smul_smul, circleIntegral.integral_smul, smul_comm s _] at h
  assumption

/-- Circle integrals are continuous if the function varies continuously -/
theorem ContinuousOn.circleIntegral {f : ℂ → ℂ → E} {s : Set ℂ} (rp : r > 0) (cs : IsCompact s)
    (fc : ContinuousOn (uncurry f) (s ×ˢ sphere c1 r)) :
    ContinuousOn (fun z0 ↦ ∮ z1 in C(c1, r), f z0 z1) s := by
  rcases (IsCompact.prod cs (isCompact_sphere _ _)).bddAbove_image fc.norm with ⟨b, bh⟩
  simp only [mem_upperBounds, Set.forall_mem_image] at bh
  intro z1 z1s
  have fb : ∀ᶠ x : ℂ in 𝓝[s] z1, ∀ᵐ t : ℝ, t ∈ Set.uIoc 0 (2 * π) →
      ‖deriv (circleMap c1 r) t • (fun z1 : ℂ ↦ f x z1) (circleMap c1 r t)‖ ≤ r * b := by
    apply eventually_nhdsWithin_of_forall; intro x xs
    apply MeasureTheory.ae_of_all _; intro t _; simp only [deriv_circleMap]
    rw [norm_smul]
    simp only [norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
    have bx := @bh (x, circleMap c1 r t) (Set.mk_mem_prod xs (circleMap_mem_sphere c1
      (by linarith) t))
    simp only [uncurry] at bx
    calc |r| * ‖f x (circleMap c1 r t)‖ ≤ |r| * b := by bound
      _ = r * b := by rw [abs_of_pos rp]
  refine intervalIntegral.continuousWithinAt_of_dominated_interval ?_ fb (by simp) ?_
  · apply eventually_nhdsWithin_of_forall; intro x xs
    apply ContinuousOn.aestronglyMeasurable
    apply ContinuousOn.smul
    rw [(by rfl : deriv (circleMap c1 r) = fun t ↦ deriv (circleMap c1 r) t)]
    simp only [deriv_circleMap]
    exact ContinuousOn.mul (Continuous.continuousOn (continuous_circleMap _ _)) continuousOn_const
    have comp : (fun t ↦ f x (circleMap c1 r t)) = uncurry f ∘ fun t ↦ (x, circleMap c1 r t) := by
      apply funext; intro t; simp
    simp; rw [comp]; apply ContinuousOn.comp fc
    exact ContinuousOn.prodMk continuousOn_const (Continuous.continuousOn (continuous_circleMap _ _))
    intro t _; simp; exact ⟨xs, by linarith⟩
    exact measurableSet_uIoc
  · apply MeasureTheory.ae_of_all _; intro t _; simp
    apply ContinuousOn.smul continuousOn_const
    have comp : (fun x ↦ f x (circleMap c1 r t)) = uncurry f ∘ fun x ↦ (x, circleMap c1 r t) := by
      apply funext; intro t; simp
    rw [comp]; apply ContinuousOn.comp fc (ContinuousOn.prodMk continuousOn_id continuousOn_const)
    intro x xs; simp; exact ⟨xs, by linarith⟩
    exact z1s

/-- Cauchy series terms are continuous in the function -/
theorem ContinuousOn.cauchy1 {n1 : ℕ} (rp : r > 0)
    (fc : ContinuousOn f (sphere c0 r ×ˢ sphere c1 r)) :
    ContinuousOn (fun z0 ↦ ∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0, z1))
      (sphere c0 r) := by
  apply ContinuousOn.circleIntegral rp (isCompact_sphere _ _)
  apply ContinuousOn.smul; apply ContinuousOn.pow; apply ContinuousOn.inv₀
  apply Continuous.continuousOn
  exact Continuous.sub (Continuous.snd continuous_id) continuous_const
  intro x xp; exact center_not_in_sphere rp (Set.mem_prod.mp xp).right
  apply ContinuousOn.smul; apply ContinuousOn.inv₀
  apply Continuous.continuousOn
  exact Continuous.sub (Continuous.snd continuous_id) continuous_const
  intro x xp; exact center_not_in_sphere rp (Set.mem_prod.mp xp).right
  simp; exact fc

/-- One 2D coefficient of the 2D Cauchy series -/
@[nolint unusedArguments]  -- Don't complain about the first argument
def Separate.series2Coeff (_ : Separate f c0 c1 r b s) (n0 n1 : ℕ) : E :=
  (2*π*I : ℂ)⁻¹ • ∮ z0 in C(c0, r), (z0 - c0)⁻¹ ^ n0 • (z0 - c0)⁻¹ •
    (2*π*I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0, z1)

/-- `series2Coeff` summed over `n0` -/
@[nolint unusedArguments]  -- Don't complain about the first argument
def Separate.series2CoeffN0Sum (_ : Separate f c0 c1 r b s) (n1 : ℕ) (w0 : ℂ) : E :=
  (2*π*I : ℂ)⁻¹ • ∮ z0 : ℂ in C(c0, r), (z0 - (c0 + w0))⁻¹ •
    (2*π*I : ℂ)⁻¹ • ∮ z1 : ℂ in C(c1, r), (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0, z1)

/-- Summing over `n0` in the 2D series does the right thing -/
theorem cauchy2_hasSum_n0 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r) (n1 : ℕ) :
    HasSum (fun n0 : ℕ ↦ w0 ^ n0 • h.series2Coeff n0 n1) (h.series2CoeffN0Sum n1 w0) :=
  haveI cc1 : ContinuousOn (fun z0 ↦
      (2 * π * I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0, z1))
      (sphere c0 r) :=
    ContinuousOn.smul continuousOn_const (ContinuousOn.cauchy1 h.rp (ContinuousOn.mono h.fc h.rs'))
  cauchy1_hasSum h.rp cc1 w0m

/-- Sums commute with `circle_integral` under reasonable hypotheses -/
theorem sum_integral_commute {f : ℕ → ℂ → E} {g : ℂ → E} {c : ℂ} {r : ℝ} (b : ℕ → ℝ) (rp : r > 0)
    (fc : ∀ n, ContinuousOn (f n) (sphere c r)) (fb : ∀ n z, z ∈ sphere c r → ‖f n z‖ ≤ b n)
    (bs : Summable b) (h : ∀ z, z ∈ sphere c r → HasSum (fun n ↦ f n z) (g z)) :
    HasSum (fun n ↦ ∮ z in C(c, r), f n z) (∮ z in C(c, r), g z) := by
  rw [circleIntegral]; simp_rw [circleIntegral]; simp
  apply intervalIntegral.hasSum_integral_of_dominated_convergence fun n _ ↦ r * b n
  · intro n; apply ContinuousOn.aestronglyMeasurable; apply ContinuousOn.smul
    apply ContinuousOn.mul (Continuous.continuousOn (continuous_circleMap _ _)) continuousOn_const
    apply ContinuousOn.comp (fc n) (Continuous.continuousOn (continuous_circleMap _ _))
    intro t _; exact circleMap_mem_sphere _ (by linarith) _
    exact measurableSet_uIoc
  · intro n; apply MeasureTheory.ae_of_all; intro t _; rw [norm_smul]; simp
    rw [abs_of_pos rp]
    refine mul_le_mul_of_nonneg_left ?_ rp.le
    exact fb n (circleMap c r t) (circleMap_mem_sphere _ (by linarith) _)
  · apply MeasureTheory.ae_of_all; intro t _
    exact Summable.mul_left _ bs
  · simp only [ne_eq, enorm_ne_top, not_false_eq_true, intervalIntegrable_const]
  · apply MeasureTheory.ae_of_all; intro t _
    apply HasSum.const_smul
    exact h (circleMap c r t) (circleMap_mem_sphere _ (by linarith) _)

/-- The simple bound on circle_interval -/
theorem bounded_circleIntegral {f : ℂ → E} {c : ℂ} {r b : ℝ} (rp : r > 0)
    (fc : ContinuousOn f (sphere c r)) (fb : ∀ z, z ∈ sphere c r → ‖f z‖ ≤ b) :
    ‖∮ z in C(c, r), f z‖ ≤ 2 * π * r * b := by
  rw [circleIntegral]; simp only [deriv_circleMap]
  have nonneg_2π := Real.two_pi_pos.le
  have ib : ‖(∫ t in (0)..(2*π), (circleMap 0 r t * I) • f (circleMap c r t))‖ ≤
      (∫ t in (0)..(2*π), ‖(circleMap 0 r t * I) • f (circleMap c r t)‖) :=
    intervalIntegral.norm_integral_le_integral_norm nonneg_2π
  refine le_trans ib ?_; clear ib
  simp_rw [norm_smul]
  simp only [norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, integral_const_mul]
  have mo : ∀ t, t ∈ Set.Icc 0 (2 * π) → ‖f (circleMap c r t)‖ ≤ b := fun t _ ↦
    fb (circleMap c r t) (circleMap_mem_sphere c (by linarith) t)
  have i0 : IntervalIntegrable (fun t ↦ ‖f (circleMap c r t)‖) Real.measureSpace.volume
      0 (2*π) := by
    apply ContinuousOn.intervalIntegrable
    have ca : ContinuousOn (norm : E → ℝ) Set.univ := Continuous.continuousOn continuous_norm
    refine ContinuousOn.comp ca ?_ (Set.mapsTo_univ _ _)
    apply ContinuousOn.comp fc
    exact Continuous.continuousOn (continuous_circleMap _ _)
    intro t _; exact circleMap_mem_sphere _ (by linarith) _
  have i1 : IntervalIntegrable (fun _ ↦ b) Real.measureSpace.volume 0 (2 * π) :=
    intervalIntegrable_const
  have im := intervalIntegral.integral_mono_on nonneg_2π i0 i1 mo
  simp only [integral_const, sub_zero, smul_eq_mul] at im
  calc |r| * ∫ t in (0)..(2*π), ‖f (circleMap c r t)‖
    _ ≤ |r| * (2 * π * b) := by bound
    _ = r * (2 * π * b) := by rw [abs_of_pos rp]
    _ = 2 * π * r * b := by ring

/-- Inverses are continuous on the sphere -/
theorem ContinuousOn.inv_sphere {c : ℂ} {r : ℝ} (rp : r > 0) :
    ContinuousOn (fun z ↦ (z - c)⁻¹) (sphere c r) :=
  ContinuousOn.inv₀ (ContinuousOn.sub continuousOn_id continuousOn_const) fun _ zs ↦
    center_not_in_sphere rp zs

/-- The 1D Cauchy integral without the constant has the expected bound -/
theorem cauchy1_bound {f : ℂ → E} {b r : ℝ} {c : ℂ} (rp : r > 0)
    (fc : ContinuousOn f (sphere c r)) (bh : ∀ z, z ∈ sphere c r → ‖f z‖ ≤ b) (n : ℕ) :
    ‖∮ z in C(c, r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ ≤ 2 * π * b * r⁻¹ ^ n := by
  have sb : ∀ z, z ∈ sphere c r → ‖(z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ ≤ r⁻¹ ^ n * r⁻¹ * b := by
    intro z zs; have fb := bh z zs
    rw [norm_smul, norm_smul]
    simp only [inv_pow, norm_inv, norm_pow, ge_iff_le, Metric.mem_sphere, Complex.dist_eq] at zs ⊢
    rw [zs]; ring_nf; bound
  have isb := bounded_circleIntegral rp ?_ sb
  · calc ‖∮ z in C(c, r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖
      _ ≤ 2 * π * r * (r⁻¹ ^ n * r⁻¹ * b) := isb
      _ = 2 * π * b * r⁻¹ ^ n * (r * r⁻¹) := by ring
      _ = 2 * π * b * r⁻¹ ^ n := by rw [mul_inv_cancel₀ rp.ne']; simp
  · apply ContinuousOn.smul; apply ContinuousOn.pow; exact ContinuousOn.inv_sphere rp
    apply ContinuousOn.smul; exact ContinuousOn.inv_sphere rp; assumption

/-- The 1D Cauchy integral with the constant has the expected bound -/
theorem cauchy1_bound' {f : ℂ → E} {r : ℝ} {c : ℂ} (rp : r > 0) (b : ℝ)
    (fc : ContinuousOn f (sphere c r)) (bh : ∀ z, z ∈ sphere c r → ‖f z‖ ≤ b) (n : ℕ) :
    ‖(2*π*I : ℂ)⁻¹ • ∮ z in C(c, r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ ≤ b * r⁻¹ ^ n := by
  have a : ‖(2*π*I : ℂ)⁻¹‖ = (2*π)⁻¹ := by
    simp only [mul_inv_rev, Complex.inv_I, neg_mul, norm_neg, norm_mul, Complex.norm_I,
      norm_inv, Complex.norm_real, Complex.norm_two, one_mul, mul_eq_mul_right_iff, inv_inj,
      Real.norm_eq_abs, abs_eq_self, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]
    exact Real.pi_pos.le
  rw [norm_smul, a]
  calc (2*π)⁻¹ * ‖∮ z in C(c, r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖
    _ ≤ (2*π)⁻¹ * (2*π * b * r⁻¹ ^ n) := by bound [cauchy1_bound rp fc bh n]
    _ = (2*π)⁻¹ * (2*π) * b * r⁻¹ ^ n := by ring
    _ = b * r⁻¹ ^ n := by field_simp [Real.pi_pos.ne']

/-- Corollary of cauchy1_bound used in cauchy2_hasSum_n1n0 -/
theorem cauchy2_hasSum_n1n0_bound (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r)
    (n : ℕ) {z0 : ℂ} (z0s : z0 ∈ sphere c0 r) :
    ‖w1 ^ n • (2 * π * I : ℂ)⁻¹ • (z0 - (c0 + w0))⁻¹ •
      ∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n • (z1 - c1)⁻¹ • f (z0, z1)‖ ≤
      (r - ‖w0‖)⁻¹ * b * (‖w1‖ / r) ^ n := by
  have isb := cauchy1_bound h.rp
    (ContinuousOn.mono (h.fc1 (mem_sphere_closed z0s)) Metric.sphere_subset_closedBall)
    (fun z1 z1s ↦ h.fb z0s z1s) n
  simp only [mem_sphere_iff_norm, Metric.mem_ball, dist_zero_right] at z0s w0m
  have zcw : ‖z0 - (c0 + w0)‖ ≥ r - ‖w0‖ := by
    calc ‖z0 - (c0 + w0)‖
      _ = ‖z0 - c0 + -w0‖ := by ring_nf
      _ ≥ ‖z0 - c0‖ - ‖-w0‖ := by bound
      _ = r - ‖w0‖ := by rw [z0s]; simp only [norm_neg]
  have zcw' : (‖z0 - (c0 + w0)‖)⁻¹ ≤ (r - ‖w0‖)⁻¹ := by bound
  have a : ‖(2 * π * I : ℂ)‖ = (2 * π) := by
    simp only [norm_mul, RCLike.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, mul_eq_mul_left_iff, abs_eq_self, OfNat.ofNat_ne_zero, or_false]
    bound
  rw [norm_smul, norm_smul, norm_smul, norm_pow, norm_inv, norm_inv, a]
  calc ‖w1‖ ^ n * ((2*π)⁻¹ * ((‖z0 - (c0 + w0)‖)⁻¹ *
      ‖∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n • (z1 - c1)⁻¹ • f (z0, z1)‖))
    _ ≤ ‖w1‖ ^ n * ((2 * π)⁻¹ * ((‖z0 - (c0 + w0)‖)⁻¹ * (2 * π * b * r⁻¹ ^ n))) := by bound
    _ ≤ ‖w1‖ ^ n * ((2 * π)⁻¹ * ((r - ‖w0‖)⁻¹ * (2 * π * b * r⁻¹ ^ n))) := by bound
    _ = 2 * π * (2 * π)⁻¹ * (r - ‖w0‖)⁻¹ * b * (‖w1‖ ^ n * r⁻¹ ^ n) := by ring
    _ = (r - ‖w0‖)⁻¹ * b * (‖w1‖ / r) ^ n := by
      rw [mul_inv_cancel₀ Real.two_pi_pos.ne', ← mul_pow, ← div_eq_mul_inv _ r, one_mul]

/-- 2D Cauchy series terms are geometrically bounded -/
theorem series2Coeff_bound (h : Separate f c0 c1 r b s) (n0 n1 : ℕ) :
    ‖h.series2Coeff n0 n1‖ ≤ b * r⁻¹ ^ (n0 + n1) := by
  have inner_c :
    ContinuousOn
      (fun z0 ↦ (2 * π * I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0, z1))
      (sphere c0 r) :=
    ContinuousOn.smul continuousOn_const (ContinuousOn.cauchy1 h.rp (ContinuousOn.mono h.fc h.rs'))
  have inner_b : ∀ z0 _, ‖(2*π*I : ℂ)⁻¹ • ∮ z1 in C(c1, r),
      (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0,z1)‖ ≤ b * r⁻¹ ^ n1 :=
    fun z0 z0s ↦ cauchy1_bound' h.rp b
      (ContinuousOn.mono (h.fc1 (mem_sphere_closed z0s)) Metric.sphere_subset_closedBall)
      (fun z1 ↦ h.fb z0s) n1
  have outer := cauchy1_bound' h.rp _ inner_c inner_b n0
  have e : b * r⁻¹ ^ n1 * r⁻¹ ^ n0 = b * r⁻¹ ^ (n0 + n1) := by
    rw [mul_assoc, ← pow_add, add_comm n0 _]
  rw [Separate.series2Coeff]; rw [e] at outer; exact outer

/-- The 2D Cauchy series -/
def series2 (h : Separate f c0 c1 r b s) : FormalMultilinearSeries ℂ (ℂ × ℂ) E := fun n ↦
  (Finset.range (n + 1)).sum fun n0 ↦ termCmmap ℂ n n0 (h.series2Coeff n0 (n - n0))

/-- `series2` is (roughly) geometrically bounded -/
theorem series2_norm (h : Separate f c0 c1 r b s) (n : ℕ) :
    ‖series2 h n‖ ≤ (n + 1) * b * r⁻¹ ^ n := by
  rw [series2]; simp only [inv_pow]
  have tb : ∀ n0, n0 ∈ Finset.range (n+1) →
      ‖termCmmap ℂ n n0 (h.series2Coeff n0 (n - n0))‖ ≤ b * r⁻¹ ^ n := by
    intro n0 n0n; simp at n0n
    apply le_trans (termCmmap_norm ℂ n n0 (h.series2Coeff n0 (n - n0)))
    have sb := series2Coeff_bound h n0 (n - n0)
    rw [← Nat.add_sub_assoc n0n n0, Nat.add_sub_cancel_left] at sb
    assumption
  trans (Finset.range (n + 1)).sum fun n0 ↦ ‖termCmmap ℂ n n0 (h.series2Coeff n0 (n - n0))‖
  · bound
  · trans (Finset.range (n + 1)).sum fun _ ↦ b * r⁻¹ ^ n
    · bound
    · clear tb; rw [Finset.sum_const]
      simp only [Finset.card_range, inv_pow, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring_nf; rfl

/-- `series2` converges within radius r -/
theorem cauchy2_radius (h : Separate f c0 c1 r b s) : ENNReal.ofReal r ≤ (series2 h).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro t tr
  rw [←ENNReal.toReal_lt_toReal (@ENNReal.coe_ne_top t) (@ENNReal.ofReal_ne_top r)] at tr
  rw [ENNReal.coe_toReal, ENNReal.toReal_ofReal h.rp.le] at tr
  apply FormalMultilinearSeries.le_radius_of_summable_nnnorm
  simp_rw [← norm_toNNReal, ← NNReal.summable_coe]; simp
  have lo : ∀ n : ℕ, 0 ≤ ‖series2 h n‖ * (t:ℝ)^n := by intro; bound
  have hi : ∀ n : ℕ, ‖series2 h n‖ * (t:ℝ)^n ≤ (n + 1) * b * (t / r) ^ n := by
    intro n; trans (↑n + 1) * b * r⁻¹ ^ n * (t:ℝ)^n
    · bound [series2_norm h n]
    · rw [mul_assoc ((↑n + 1) * b) _ _, ← mul_pow, inv_mul_eq_div]
  refine .of_nonneg_of_le lo hi ?_
  simp_rw [mul_comm _ b, mul_assoc b _ _]; apply Summable.mul_left b
  have trn : ‖↑t / r‖ < 1 := by simp; rw [abs_of_pos h.rp, div_lt_one h.rp]; assumption
  simp_rw [right_distrib _ _ _, one_mul]
  exact Summable.add (hasSum_coe_mul_geometric_of_norm_lt_one trn).summable
    (hasSum_geometric_of_norm_lt_one trn).summable

variable [CompleteSpace E]

/-- Simplied 1D Cauchy integral formula, assuming differentiability everywhere in the interior -/
theorem cauchy1 {r : ℝ} {c w : ℂ} {f : ℂ → E} (wm : w ∈ ball c r)
    (fc : ContinuousOn f (closedBall c r)) (fd : ∀ z, z ∈ ball c r → DifferentiableAt ℂ f z) :
    (2*π*I : ℂ)⁻¹ • (∮ z in C(c, r), (z - w)⁻¹ • f z) = f w := by
  refine Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty wm fc ?_
  intro z zm; apply fd z _; simp only [Metric.mem_ball, Set.sdiff_empty] at zm ⊢; assumption

/-- The 2D Cauchy integral formula -/
theorem cauchy2 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball c0 r) (w1m : w1 ∈ ball c1 r) :
    (2*π*I : ℂ)⁻¹ • (∮ z0 in C(c0, r), (z0 - w0)⁻¹ • (2*π*I : ℂ)⁻¹ •
      (∮ z1 in C(c1, r), (z1 - w1)⁻¹ • f (z0, z1))) =
      f (w0, w1) := by
  have h1 := fun z0 (z0m : z0 ∈ closedBall c0 r) ↦
    cauchy1 w1m (h.fc1 z0m) fun z1 z1m ↦ h.fd1 z0m (ball_subset_closedBall z1m)
  have ic1 : ContinuousOn (fun z0 ↦ (2 * π * I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - w1)⁻¹ • f (z0, z1))
      (closedBall c0 r) :=
    (h.fc0 w1m).congr h1
  have id1 : DifferentiableOn ℂ (fun z0 ↦ (2 * π * I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - w1)⁻¹
      • f (z0, z1)) (ball c0 r) := by
    rw [differentiableOn_congr fun z zs ↦ h1 z (ball_subset_closedBall zs)]
    intro z0 z0m; apply DifferentiableAt.differentiableWithinAt
    exact h.fd0 (ball_subset_closedBall z0m) (ball_subset_closedBall w1m)
  have h01 :=
    cauchy1 w0m ic1 fun z0 z0m ↦
      DifferentiableOn.differentiableAt id1 (IsOpen.mem_nhds isOpen_ball z0m)
  exact _root_.trans h01 (h1 w0 (ball_subset_closedBall w0m))

/-- Shifted inverses are continuous on the sphere -/
theorem ContinuousOn.inv_sphere_ball {c w : ℂ} {r : ℝ} (wr : w ∈ ball (0 : ℂ) r) :
    ContinuousOn (fun z ↦ (z - (c + w))⁻¹) (sphere c r) := by
  refine ContinuousOn.inv₀ (ContinuousOn.sub continuousOn_id continuousOn_const) fun z zs ↦ ?_
  rw [← norm_ne_zero_iff]
  simp only [mem_ball_zero_iff, mem_sphere_iff_norm] at zs wr
  apply ne_of_gt
  calc ‖z - (c + w)‖
    _ = ‖z - c + -w‖ := by ring_nf
    _ ≥ ‖z - c‖ - ‖-w‖ := by bound
    _ = r - ‖-w‖ := by rw [zs]
    _ = r - ‖w‖ := by rw [norm_neg]
    _ > r - r := (sub_lt_sub_left wr _)
    _ = 0 := by ring

/-- The outer n1 sum in the 2D series does the right thing -/
theorem cauchy2_hasSum_n1n0 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r)
    (w1m : w1 ∈ ball (0 : ℂ) r) :
    HasSum (fun n1 ↦ w1 ^ n1 • h.series2CoeffN0Sum n1 w0) (f (c0 + w0, c1 + w1)) := by
  have cw0m : c0 + w0 ∈ ball c0 r := by
    simpa only [Metric.mem_ball, dist_self_add_left, Complex.dist_eq, sub_zero] using w0m
  have cw1m : c1 + w1 ∈ ball c1 r := by
    simpa only [Metric.mem_ball, dist_self_add_left, dist_zero_right] using w1m
  simp_rw [Separate.series2CoeffN0Sum]
  rw [← cauchy2 h cw0m cw1m]
  generalize hs : (2 * ↑π * I)⁻¹ = s
  simp_rw [smul_comm _ s _]
  apply HasSum.const_smul
  simp_rw [← circleIntegral.integral_smul (w1 ^ _) _ _ _]
  apply sum_integral_commute (fun n ↦ (r - ‖w0‖)⁻¹ * b * (‖w1‖ / r) ^ n) h.rp
  · intro n
    apply ContinuousOn.smul continuousOn_const
    apply ContinuousOn.smul continuousOn_const
    apply ContinuousOn.smul
    exact ContinuousOn.inv_sphere_ball w0m
    apply ContinuousOn.cauchy1 h.rp
    apply ContinuousOn.mono h.fc h.rs'
  · rw [← hs]; exact fun n z0 z0s ↦ cauchy2_hasSum_n1n0_bound h w0m n z0s
  · apply Summable.mul_left
    apply summable_geometric_of_norm_lt_one
    simp only [norm_div, Real.norm_eq_abs, abs_of_pos h.rp]
    simp at w1m ⊢; exact (div_lt_one h.rp).mpr w1m
  · intro z0 z0s
    simp_rw [smul_comm s _]; simp_rw [smul_comm (w1 ^ _) _]; apply HasSum.const_smul
    have fcs : ContinuousOn (fun z1 ↦ f (z0, z1)) (sphere c1 r) :=
      ContinuousOn.mono (h.fc1 (Metric.sphere_subset_closedBall z0s))
        Metric.sphere_subset_closedBall
    have hs1 := cauchy1_hasSum h.rp fcs w1m
    simp_rw [hs, smul_comm _ s] at hs1
    assumption

/-- The 2D series converges to `f` -/
theorem cauchy2_hasSum_2d (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r)
    (w1m : w1 ∈ ball (0 : ℂ) r) :
    HasSum (fun n : ℕ × ℕ ↦ w0 ^ n.snd • w1 ^ n.fst • h.series2Coeff n.snd n.fst)
      (f (c0 + w0, c1 + w1)) := by
  generalize ha : f (c0 + w0, c1 + w1) = a
  generalize hf : (fun n : ℕ × ℕ ↦ w0 ^ n.snd • w1 ^ n.fst • h.series2Coeff n.snd n.fst) = f
  generalize hg : (fun n1 : ℕ ↦ w1 ^ n1 • h.series2CoeffN0Sum n1 w0) = g
  generalize ha' : ∑' n, f n = a'
  have gs : HasSum g a := by rw [← hg, ← ha]; exact cauchy2_hasSum_n1n0 h w0m w1m
  have fs : ∀ n1 : ℕ, HasSum (fun n0 ↦ f ⟨n1, n0⟩) (g n1) := by
    intro n1; rw [← hf, ← hg]; simp only
    simp_rw [smul_comm (w0 ^ _) _]; apply HasSum.const_smul; exact cauchy2_hasSum_n0 h w0m n1
  have fb : ∀ n : ℕ × ℕ, ‖f n‖ ≤ b * (‖w0‖ / r) ^ n.snd * (‖w1‖ / r) ^ n.fst := by
    intro n; rw [← hf]; simp
    rw [norm_smul, norm_smul, mul_assoc]
    simp only [norm_pow, ← mul_assoc]
    trans ‖w0‖ ^ n.snd * ‖w1‖ ^ n.fst * (b * r⁻¹ ^ (n.snd + n.fst))
    · bound [series2Coeff_bound h n.snd n.fst]
    · rw [pow_add, div_eq_mul_inv, div_eq_mul_inv, inv_pow, inv_pow]; ring_nf; rfl
  have sf : Summable f := by
    simp only [Metric.mem_ball, dist_zero_right] at w0m w1m
    refine .of_norm_bounded ?_ fb
    simp_rw [mul_assoc]; apply Summable.mul_left; simp_rw [mul_comm ((‖w0‖ / r) ^ _) _]
    apply Summable.mul_of_nonneg
    · exact summable_geometric_of_lt_one (by bound) ((div_lt_one h.rp).mpr w1m)
    · exact summable_geometric_of_lt_one (by bound) ((div_lt_one h.rp).mpr w0m)
    · intro n; simp only [Pi.zero_apply, div_pow]; bound
    · intro n; simp only [Pi.zero_apply, div_pow]; bound
  have fs' : HasSum f a' := by rw [← ha']; exact sf.hasSum
  have gs' := HasSum.prod_fiberwise fs' fs
  rwa [HasSum.unique gs gs']

/-- We convert the 2D sum to a 1D outer sum with an inner finite antidiagonal -/
theorem HasSum.antidiagonal_of_2d {V : Type} [AddCommMonoid V] [TopologicalSpace V]
    [ContinuousAdd V] [RegularSpace V] {f : ℕ × ℕ → V} {a : V} (h : HasSum f a) :
    HasSum (fun n ↦ (Finset.range (n + 1)).sum fun n1 ↦ f (n1, n - n1)) a := by
  generalize hg : (fun n ↦ (Finset.range (n + 1)).sum fun n1 ↦ f (n1, n - n1)) = g
  rw [←Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff] at h
  have fg : ∀ n, HasSum (fun d : Finset.HasAntidiagonal.antidiagonal n ↦
      (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨n, d⟩) (g n) := by
    intro n; simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
    have fs := hasSum_fintype fun d : ↥(Finset.HasAntidiagonal.antidiagonal n) ↦ f ↑d
    -- simp at fs,
    have e : (Finset.univ.sum fun d : ↥(Finset.HasAntidiagonal.antidiagonal n) ↦ f ↑d) = g n := by
      rw [Finset.sum_coe_sort, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← hg]
    rwa [← e]
  exact HasSum.sigma h fg

/-- `series2` converges to `f` -/
theorem cauchy2_hasSum (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r)
    (w1m : w1 ∈ ball (0 : ℂ) r) :
    HasSum (fun n ↦ series2 h n fun _ : Fin n ↦ (w0, w1)) (f (c0 + w0, c1 + w1)) := by
  have sum := (cauchy2_hasSum_2d h w0m w1m).antidiagonal_of_2d; simp only at sum
  generalize ha : f (c0 + w0, c1 + w1) = a; rw [ha] at sum; clear ha
  have e : (fun n ↦
      (Finset.range (n + 1)).sum fun n1 ↦ w0 ^ (n - n1) • w1 ^ n1 • h.series2Coeff (n - n1) n1) =
      fun n ↦ series2 h n fun _ : Fin n ↦ (w0, w1) := by
    clear sum; funext n
    rw [series2]; simp only [_root_.sum_apply]
    simp_rw [termCmmap_apply]
    nth_rw 1 [← Finset.sum_range_reflect]; simp
    apply Finset.sum_congr rfl
    intro n0 n0n'; simp only [Finset.mem_range] at n0n'
    have n0n := Nat.le_of_lt_succ n0n'
    rw [Nat.sub_sub_self n0n, min_eq_left n0n]
  rwa [←e]

/-- Osgood's lemma on a `closedBall`: `f` is jointly analytic -/
theorem osgood_h (h : Separate f c0 c1 r b s) :
    HasFPowerSeriesOnBall f (series2 h) (c0, c1) (ENNReal.ofReal r) :=
  { r_le := cauchy2_radius h
    r_pos := by simp; exact h.rp
    hasSum := by
      simp only [Metric.eball_ofReal, Metric.mem_ball, dist_zero_right, Prod.forall]
      intro w0 w1 wr; rw [Prod.norm_def] at wr
      simp only [max_lt_iff] at wr
      have w0m : w0 ∈ ball (0 : ℂ) r := by simp; exact wr.left
      have w1m : w1 ∈ ball (0 : ℂ) r := by simp; exact wr.right
      exact cauchy2_hasSum h w0m w1m }

end osgood

/-- Osgood's lemma: if `f` is separately analytic on an open set,
    it is jointly analytic on that set -/
theorem osgood {E : Type} {f : ℂ × ℂ → E} {s : Set (ℂ × ℂ)} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (o : IsOpen s) (fc : ContinuousOn f s)
    (fa0 : ∀ z0 z1 : ℂ, (z0, z1) ∈ s → AnalyticAt ℂ (fun z0 ↦ f (z0, z1)) z0)
    (fa1 : ∀ z0 z1 : ℂ, (z0, z1) ∈ s → AnalyticAt ℂ (fun z1 ↦ f (z0, z1)) z1) :
    AnalyticOnNhd ℂ f s := by
  intro c cs
  rcases Metric.isOpen_iff.mp o c cs with ⟨r, rp, rs⟩
  have rs : closedBall c (r / 2) ⊆ s := le_trans (Metric.closedBall_subset_ball (by linarith)) rs
  rcases ((isCompact_closedBall _ _).bddAbove_image (ContinuousOn.mono fc rs).norm).exists_ge 0
    with ⟨b, bp, bh⟩
  simp only [Set.forall_mem_image] at bh
  have h : Separate f c.fst c.snd (r / 2) b s :=
    { rp := by linarith
      so := o
      rs := rs
      fc := fc
      fa0 := fa0 _ _
      fa1 := fa1 _ _
      bp := bp
      fb := fun {z0 z1} z0m z1m ↦ @bh (z0, z1)
        (spheres_subset_closedBall (Set.mk_mem_prod z0m z1m)) }
  have a := (osgood_h h).analyticAt
  simpa only [Prod.mk.eta] using a

/-- Osgood's lemma at a point: if `f` is separately analytic near a point,
    it is jointly analytic there -/
theorem osgood_at' {E : Type} {f : ℂ × ℂ → E} {c : ℂ × ℂ} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (h : ∀ᶠ x : ℂ × ℂ in 𝓝 c, ContinuousAt f x ∧
      AnalyticAt ℂ (fun z ↦ f (z, x.2)) x.1 ∧ AnalyticAt ℂ (fun z ↦ f (x.1, z)) x.2) :
    AnalyticAt ℂ f c := by
  rcases eventually_nhds_iff.mp h with ⟨s, h, o, cs⟩
  exact osgood o (fun _ m ↦ (h _ m).1.continuousWithinAt) (fun _ _ m ↦ (h _ m).2.1)
    (fun _ _ m ↦ (h _ m).2.2) c cs

/-- Osgood's lemma at a point: if `f` is separately analytic near a point,
    it is jointly analytic there -/
theorem osgood_at {E : Type} {f : ℂ × ℂ → E} {c : ℂ × ℂ} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (fc : ∀ᶠ x in 𝓝 c, ContinuousAt f x)
    (fa0 : ∀ᶠ x : ℂ × ℂ in 𝓝 c, AnalyticAt ℂ (fun z ↦ f (z, x.2)) x.1)
    (fa1 : ∀ᶠ x : ℂ × ℂ in 𝓝 c, AnalyticAt ℂ (fun z ↦ f (x.1, z)) x.2) : AnalyticAt ℂ f c :=
  osgood_at' (fc.and (fa0.and fa1))

end
end Ray_Ray_Hartogs_Osgood

-- ===== Ray.Analytic.Holomorphic =====
section Ray_Ray_Analytic_Holomorphic
/-!
## Basics about complex analytic functions
-/

open Complex (exp I log)
open Filter (atTop)
open Metric (ball closedBall sphere isOpen_ball)
open Set (univ)
open scoped Real NNReal ENNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- `f : ℂ × ℂ → E` is differentiable iff it is analytic -/
theorem differentiable_iff_analytic2 {E : Type} {f : ℂ × ℂ → E} {s : Set (ℂ × ℂ)}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (o : IsOpen s) :
    DifferentiableOn ℂ f s ↔ AnalyticOnNhd ℂ f s := by
  constructor
  · intro d; apply osgood o d.continuousOn
    · intro z0 z1 zs
      rcases Metric.isOpen_iff.mp o (z0, z1) zs with ⟨r, rp, rs⟩
      have d0 : DifferentiableOn ℂ (fun z0 ↦ f (z0, z1)) (ball z0 r) := by
        apply DifferentiableOn.comp d
        exact DifferentiableOn.prodMk differentiableOn_id (differentiableOn_const _)
        intro z0 z0s; apply rs; simp at z0s ⊢; assumption
      exact (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr d0 z0 (Metric.mem_ball_self rp)
    · intro z0 z1 zs
      rcases Metric.isOpen_iff.mp o (z0, z1) zs with ⟨r, rp, rs⟩
      have d1 : DifferentiableOn ℂ (fun z1 ↦ f (z0, z1)) (ball z1 r) := by
        apply DifferentiableOn.comp d
        exact DifferentiableOn.prodMk (differentiableOn_const _) differentiableOn_id
        intro z1 z1s; apply rs; simp at z1s ⊢; assumption
      exact (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr d1 z1 (Metric.mem_ball_self rp)
  · exact fun a ↦ a.differentiableOn

/-- `f : ℂ × ℂ → E` is `ContDiffAt` iff it is analytic -/
theorem contDiffAt_iff_analytic_at2 {E : Type} {f : ℂ × ℂ → E} {x : ℂ × ℂ} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {n : WithTop ℕ∞} (n1 : 1 ≤ n) :
    ContDiffAt ℂ n f x ↔ AnalyticAt ℂ f x := by
  constructor
  · intro d
    rcases d.contDiffOn (m := 1) (by simpa) (by simp) with ⟨u, un, d⟩
    rcases mem_nhds_iff.mp un with ⟨v, uv, vo, vx⟩
    refine (differentiable_iff_analytic2 vo).mp ?_ _ vx
    exact (d.mono uv).differentiableOn (by decide)
  · intro a; exact a.contDiffAt.of_le le_top

/-- If `f` is analytic in an open ball, it has a power series over that ball -/
lemma analyticOnNhd_ball_iff_hasFPowerSeriesOnBall {f : ℂ → E} {c : ℂ} {r : ℝ≥0∞}
    (r0 : 0 < r) :
    AnalyticOnNhd ℂ f (Metric.eball c r) ↔
      ∃ p : FormalMultilinearSeries ℂ ℂ E, HasFPowerSeriesOnBall f p c r := by
  constructor
  · intro a
    obtain ⟨p,s,hs⟩ := a c (by simp only [Metric.mem_eball, edist_self, r0])
    have grow : ∀ t : ℝ≥0, 0 < t → t < r → HasFPowerSeriesOnBall f p c t := by
      intro t t0 tr
      have d : DifferentiableOn ℂ f (closedBall c t) := by
        apply (a.mono ?_).differentiableOn
        intro x m
        simp only [Metric.mem_closedBall, dist_le_coe, Metric.mem_eball,
          ← ENNReal.coe_le_coe, ← edist_nndist] at m ⊢
        order
      have ht := d.hasFPowerSeriesOnBall t0
      exact hs.hasFPowerSeriesAt.eq_formalMultilinearSeries ht.hasFPowerSeriesAt ▸ ht
    refine ⟨p, ?_, r0, ?_⟩
    · exact ENNReal.le_of_forall_pos_nnreal_lt fun t t0 tr ↦ (grow t t0 tr).r_le
    · intro y yr
      simp only [Metric.mem_eball, edist_zero_right] at yr
      obtain ⟨t,yt,tr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp yr
      have t0 : 0 < t := by
        simp only [enorm_eq_nnnorm, ENNReal.coe_lt_coe] at yt
        exact pos_of_gt yt
      refine (grow t t0 tr).hasSum ?_
      simp only [Metric.eball_coe, Metric.mem_ball, dist_zero_right]
      simpa only [← ofReal_norm, ENNReal.ofReal_lt_coe_iff, norm_nonneg] using yt
  · intro ⟨p,a⟩
    exact a.analyticOnNhd

end
end Ray_Ray_Analytic_Holomorphic

-- ===== Ray.Analytic.Uniform =====
section Ray_Ray_Analytic_Uniform
/-!
## Convergent sequences of analytic functions

We show that uniformly convergence sequences of analytic functions have analytic limits.
-/

open Complex (I)
open Filter (atTop)
open MeasureTheory.MeasureSpace (volume)
open Metric (ball closedBall sphere)
open scoped Real NNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOn_small_cball {f : ℂ → E} {z : ℂ} {r : ℝ≥0} (h : AnalyticOnNhd ℂ f (ball z r))
    (s : ℝ≥0) (sr : s < r) : AnalyticOnNhd ℂ f (closedBall z s) := by
  intro x hx
  rw [closedBall] at hx; simp at hx
  have hb : x ∈ ball z r := by
    rw [ball]; simp only [dist_lt_coe, Set.mem_ofPred_eq]; exact lt_of_le_of_lt hx sr
  exact h x hb

theorem cauchy_bound {f : ℂ → E} {c : ℂ} {r : ℝ≥0} {d : ℝ≥0} {w : ℂ} {n : ℕ} (rp : r > 0)
    (h : ∀ w ∈ closedBall c r, ‖f w‖ ≤ d) :
    ‖cauchyPowerSeries f c r n fun _ ↦ w‖ ≤ ‖w‖ ^ n * r⁻¹ ^ n * d := by
  set wr := ‖w‖ ^ n * r⁻¹ ^ n * d
  rw [cauchyPowerSeries_apply f c r n w, norm_smul]
  generalize hg : (fun z ↦ (w / (z - c)) ^ n • (z - c)⁻¹ • f z) = g
  have gs : ∀ z ∈ sphere c r, ‖g z‖ ≤ wr * r⁻¹ := by
    intro z; simp only [mem_sphere_iff_norm]; intro zr
    simp only [← hg, zr, div_pow, norm_smul, norm_div, norm_pow, norm_inv]
    have zb : z ∈ closedBall c r := by
      simp only [Metric.mem_closedBall, Complex.dist_eq, zr, le_refl]
    have zs := h z zb
    calc ‖w‖ ^ n / ↑r ^ n * (r⁻¹ * ‖f z‖)
      _ = ‖w‖ ^ n * (r⁻¹ ^ n : ℝ≥0) * (r⁻¹ * ‖f z‖) := by
        rw [div_eq_mul_inv, ← inv_pow, NNReal.coe_pow, NNReal.coe_inv]
      _ ≤ ‖w‖ ^ n * r⁻¹ ^ n * (r⁻¹ * d) := by bound
      _ = ‖w‖ ^ n * r⁻¹ ^ n * d * r⁻¹ := by ring
      _ = wr * r⁻¹ := rfl
  have cn := circleIntegral.norm_integral_le_of_norm_le_const (NNReal.coe_nonneg r) gs
  simp only [mul_inv_rev, Complex.inv_I, norm_neg, norm_mul, Complex.norm_I, norm_inv,
    Complex.norm_real, Complex.norm_two, one_mul, div_pow, Real.norm_eq_abs] at hg cn ⊢
  have p3 : ‖π‖ = π := abs_of_nonneg (by bound)
  calc ‖π‖⁻¹ * 2⁻¹ * ‖circleIntegral g c ↑r‖
    _ ≤ ‖π‖⁻¹ * 2⁻¹ * (2 * π * r * (wr * r⁻¹)) := by bound
    _ = π * ‖π‖⁻¹ * (r * r⁻¹) * wr := by ring
    _ = π * π⁻¹ * (r * r⁻¹) * wr := by rw [p3]
    _ = 1 * (r * r⁻¹) * wr := by rw [mul_inv_cancel₀ Real.pi_ne_zero]
    _ = wr := by field_simp; norm_cast; field_simp; simp

theorem circleIntegral_sub {f g : ℂ → E} {c : ℂ} {r : ℝ} (fi : CircleIntegrable f c r)
    (gi : CircleIntegrable g c r) :
    circleIntegral f c r - circleIntegral g c r = circleIntegral (f - g) c r := by
  rw [circleIntegral]
  generalize hf : (fun θ : ℝ ↦ deriv (circleMap c r) θ • f (circleMap c r θ)) = fc
  rw [circleIntegral]
  generalize hg : (fun θ : ℝ ↦ deriv (circleMap c r) θ • g (circleMap c r θ)) = gc
  rw [circleIntegral]
  generalize hfg : (fun θ : ℝ ↦ deriv (circleMap c r) θ • (f - g) (circleMap c r θ)) = fgc
  have hs : fc - gc = fgc := by
    rw [← hf, ← hg, ← hfg]; funext
    simp only [deriv_circleMap, Pi.sub_apply, smul_sub]
  rw [← hs]; clear hfg hs fgc; symm
  have fci := CircleIntegrable.out fi; rw [hf] at fci
  have gci := CircleIntegrable.out gi; rw [hg] at gci
  exact intervalIntegral.integral_sub fci gci

theorem circleMap_nz {c : ℂ} {r : ℝ≥0} {θ : ℝ} (rp : r > 0) : circleMap c r θ - c ≠ 0 := by
  simp only [circleMap_sub_center, Ne, circleMap_eq_center_iff, NNReal.coe_eq_zero]
  intro h; rw [h] at rp; simp only [gt_iff_lt, not_lt_zero] at rp

theorem cauchy_is_circleIntegrable {f : ℂ → E} {c : ℂ} {r : ℝ≥0} (n : ℕ) (w : ℂ) (rp : r > 0)
    (h : ContinuousOn f (closedBall c r)) :
    CircleIntegrable (fun z ↦ (w ^ n / (z - c) ^ n) • ((z - c)⁻¹ • f z)) c r := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.smul ?_ ?_
  · refine continuousOn_const.div ?_ ?_
    · apply Continuous.continuousOn
      fun_prop
    · simp [rp.ne']
  · refine ContinuousOn.smul ?_ ?_
    · apply Continuous.continuousOn
      refine Continuous.inv₀ (by continuity) fun x ↦ circleMap_nz rp
    · refine ContinuousOn.comp h (Continuous.continuousOn (by continuity)) ?_
      intro θ _; exact circleMap_mem_closedBall c (NNReal.coe_nonneg r) θ

theorem cauchy_sub {f g : ℂ → E} {c : ℂ} {r : ℝ≥0} (n : ℕ) (w : ℂ) (rp : r > 0)
    (cf : ContinuousOn f (closedBall c r)) (cg : ContinuousOn g (closedBall c r)) :
    ((cauchyPowerSeries f c r n fun _ ↦ w) - cauchyPowerSeries g c r n fun _ ↦ w) =
      cauchyPowerSeries (f - g) c r n fun _ ↦ w := by
  rw [cauchyPowerSeries_apply f c r n w]
  rw [cauchyPowerSeries_apply g c r n w]
  rw [cauchyPowerSeries_apply (f - g) c r n w]
  set s : ℂ := (2 * π * I)⁻¹
  simp only [div_pow, Pi.sub_apply, smul_sub]
  have fi := cauchy_is_circleIntegrable n w rp cf
  have gi := cauchy_is_circleIntegrable n w rp cg
  have cia := circleIntegral_sub fi gi
  rw [← smul_sub, cia]
  clear cia fi gi cf cg rp
  have flip :
    ((fun z ↦ (w ^ n / (z - c) ^ n) • ((z - c)⁻¹ • f z)) - fun z ↦
        (w ^ n / (z - c) ^ n) • ((z - c)⁻¹ • g z)) =
      fun z ↦ (w ^ n / (z - c) ^ n) • ((z - c)⁻¹ • f z) -
        (w ^ n / (z - c) ^ n) • ((z - c)⁻¹ • g z) :=
    rfl
  simp only [flip]

theorem cauchy_dist {f g : ℂ → E} {c : ℂ} {r : ℝ≥0} {d : ℝ≥0} (n : ℕ) (w : ℂ) (rp : r > 0)
    (cf : ContinuousOn f (closedBall c r)) (cg : ContinuousOn g (closedBall c r))
    (h : ∀ z, z ∈ closedBall c r → ‖f z - g z‖ ≤ d) :
    dist (cauchyPowerSeries f c r n fun _ ↦ w) (cauchyPowerSeries g c r n fun _ ↦ w) ≤
      ‖w‖ ^ n * r⁻¹ ^ n * d := by
  rw [dist_eq_norm, cauchy_sub n w rp cf cg]
  refine cauchy_bound rp ?_; intro z zr; simp at h zr; refine h z zr

variable [CompleteSpace E]

theorem cauchy_on_cball_radius {f : ℂ → E} {z : ℂ} {r : ℝ≥0} (rp : r > 0)
    (h : AnalyticOnNhd ℂ f (closedBall z r)) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f z r) z r := by
  have hd : DifferentiableOn ℂ f (closedBall z r) := by
    intro x H; exact AnalyticAt.differentiableWithinAt (h x H)
  set p : FormalMultilinearSeries ℂ ℂ E := cauchyPowerSeries f z r
  exact DifferentiableOn.hasFPowerSeriesOnBall hd rp

theorem analyticOn_cball_radius {f : ℂ → E} {z : ℂ} {r : ℝ≥0} (rp : r > 0)
    (h : AnalyticOnNhd ℂ f (closedBall z r)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ E, HasFPowerSeriesOnBall f p z r :=
  ⟨cauchyPowerSeries f z r, cauchy_on_cball_radius rp h⟩

theorem analyticOn_ball_radius {f : ℂ → E} {z : ℂ} {r : ℝ≥0} (rp : r > 0)
    (h : AnalyticOnNhd ℂ f (ball z r)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ E, HasFPowerSeriesOnBall f p z r := by
  have h0 := analyticOn_small_cball h (r / 2) (NNReal.half_lt_self <| rp.ne')
  rcases analyticOn_cball_radius (half_pos rp) h0 with ⟨p, ph⟩
  set R := FormalMultilinearSeries.radius p
  refine
    ⟨p, {
        r_le := ?_
        r_pos := ENNReal.coe_pos.mpr rp
        hasSum := ?_ }⟩
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro t tp tr
    have ht := analyticOn_small_cball h t (ENNReal.coe_lt_coe.mp tr)
    rcases analyticOn_cball_radius tp ht with ⟨p', hp'⟩
    have pp : p = p' := HasFPowerSeriesAt.eq_formalMultilinearSeries ⟨↑(r / 2), ph⟩ ⟨t, hp'⟩
    rw [← pp] at hp'
    refine hp'.r_le
  · intro y yr
    rw [Metric.mem_eball] at yr
    rcases exists_between yr with ⟨t, t0, t1⟩
    have t1' : t.toNNReal < r := by
      rw [← WithTop.coe_lt_coe]; exact lt_of_le_of_lt ENNReal.coe_toNNReal_le_self t1
    have ht := analyticOn_small_cball h t.toNNReal t1'
    have tp : 0 < ENNReal.toNNReal t :=
      ENNReal.toNNReal_pos (ne_of_gt <| pos_of_gt t0) (ne_top_of_lt t1)
    rcases analyticOn_cball_radius tp ht with ⟨p', hp'⟩
    have pp : p = p' :=
      HasFPowerSeriesAt.eq_formalMultilinearSeries ⟨↑(r / 2), ph⟩ ⟨t.toNNReal, hp'⟩
    rw [← pp] at hp'
    refine hp'.hasSum ?_
    rw [Metric.mem_eball]
    calc edist y 0
      _ < t := t0
      _ = ↑t.toNNReal := (ENNReal.coe_toNNReal <| ne_top_of_lt t1).symm

/-- Uniform limits of analytic functions are analytic -/
theorem uniform_analytic_lim {I : Type} [Lattice I] [Nonempty I] {f : I → ℂ → E} {g : ℂ → E}
    {s : Set ℂ} (o : IsOpen s) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (u : TendstoUniformlyOn f g atTop s) : AnalyticOnNhd ℂ g s := by
  intro c hc
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (o.mem_nhds hc) with ⟨r, rp, cb⟩
  lift r to ℝ≥0 using rp.le
  simp only [NNReal.coe_pos] at rp
  have hb : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c r) := fun n ↦ (h n).mono cb
  set pr := fun n ↦ cauchyPowerSeries (f n) c r
  have hpf : ∀ n, HasFPowerSeriesOnBall (f n) (pr n) c r := by
    intro n
    have cs := cauchy_on_cball_radius rp (hb n)
    have pn : pr n = cauchyPowerSeries (f n) c r := rfl
    rw [← pn] at cs; exact cs
  have cfs : ∀ n, ContinuousOn (f n) s := fun n ↦ AnalyticOnNhd.continuousOn (h n)
  have cf : ∀ n, ContinuousOn (f n) (closedBall c r) := fun n ↦ ContinuousOn.mono (cfs n) cb
  have cg : ContinuousOn g (closedBall c r) :=
    ContinuousOn.mono (TendstoUniformlyOn.continuousOn u (.of_forall cfs)) cb
  clear h hb hc o cfs
  set p := cauchyPowerSeries g c r
  refine
    HasFPowerSeriesOnBall.analyticAt
      { r_le := le_radius_cauchyPowerSeries g c r
        r_pos := ENNReal.coe_pos.mpr rp
        hasSum := ?_ }
  intro y yb
  have yr := yb; simp at yr
  set a := ‖y‖ / r
  have a0 : a ≥ 0 := by bound
  have a1 : a < 1 := (div_lt_one (NNReal.coe_pos.mpr rp)).mpr yr
  have a1p : 1 - a > 0 := by bound
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro e ep
  generalize d4 : (1 - a) * (e / 4) = d
  have dp : d > 0 := by rw [← d4]; bound
  rcases Filter.eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp u d dp) with ⟨n, hn'⟩
  set hn := hn' n; simp at hn; clear hn' u
  have dfg : dist (f n (c + y)) (g (c + y)) ≤ d := by
    apply le_of_lt; rw [dist_comm]
    refine hn (c + y) ?_
    apply cb
    simp; exact yr.le
  set hs := (hpf n).hasSum yb
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop] at hs
  rcases hs d dp with ⟨N, NM⟩; clear hs
  exists N; intro M NlM
  have dpf := (NM M NlM).le; clear NM NlM N yb
  have dppr : dist (M.sum fun k : ℕ ↦ p k fun _ ↦ y)
      (M.sum fun k : ℕ ↦ pr n k fun _ ↦ y) ≤ e / 4 := by
    trans M.sum fun k : ℕ ↦ dist (p k fun _ ↦ y) (pr n k fun _ ↦ y)
    apply dist_sum_sum_le M (fun k : ℕ ↦ p k fun _ ↦ y) fun k : ℕ ↦ pr n k fun _ ↦ y
    trans M.sum fun k ↦ a ^ k * d
    · apply Finset.sum_le_sum; intro k _
      have hak : a ^ k = ‖y‖ ^ k * r⁻¹ ^ k := by
        calc (‖y‖ / r) ^ k
          _ = (‖y‖ * r⁻¹) ^ k := by rw [div_eq_mul_inv, NNReal.coe_inv]
          _ = ‖y‖ ^ k * r⁻¹ ^ k := mul_pow _ _ _
      rw [hak]
      generalize hd' : d.toNNReal = d'
      have dd : (d' : ℝ) = d := by rw [← hd']; exact Real.coe_toNNReal d dp.le
      have hcb : ∀ z, z ∈ closedBall c r → ‖g z - f n z‖ ≤ d' := by
        intro z zb
        simp only [dist_eq_norm] at hn
        exact le_trans (hn z (cb zb)).le (le_of_eq dd.symm)
      exact _root_.trans (cauchy_dist k y rp cg (cf n) hcb)
        (mul_le_mul_of_nonneg_left (le_of_eq dd) (by bound))
    · have pgb : (M.sum fun k ↦ a ^ k) ≤ (1 - a)⁻¹ := partial_geometric_bound M a0 a1
      calc
        (M.sum fun k ↦ a ^ k * d) = (M.sum fun k ↦ a ^ k) * d := by rw [← Finset.sum_mul]
        _ ≤ (1 - a)⁻¹ * d := by bound
        _ = (1 - a)⁻¹ * ((1 - a) * (e / 4)) := by rw [← d4]
        _ = (1 - a) * (1 - a)⁻¹ * (e / 4) := by ring
        _ = 1 * (e / 4) := by rw [mul_inv_cancel₀ a1p.ne']
        _ = e / 4 := by ring
  generalize hMp : M.sum (fun k : ℕ ↦ p k fun _ ↦ y) = Mp; rw [hMp] at dppr
  generalize hMpr : M.sum (fun k ↦ pr n k fun _ ↦ y) = Mpr; rw [hMpr] at dpf dppr
  calc dist Mp (g (c + y))
    _ ≤ dist Mp (f n (c + y)) + dist (f n (c + y)) (g (c + y)) := dist_triangle _ _ _
    _ ≤ dist Mp Mpr + dist Mpr (f n (c + y)) + d := by bound
    _ ≤ e / 4 + d + d := by bound
    _ = e / 4 + 2 * (1 - a) * (e / 4) := by rw [← d4]; ring
    _ ≤ e / 4 + 2 * (1 - 0) * (e / 4) := by bound
    _ = 3 / 4 * e := by ring
    _ < 1 * e := (mul_lt_mul_of_pos_right (by norm_num) ep)
    _ = e := by simp

end
end Ray_Ray_Analytic_Uniform

-- ===== Ray.Analytic.Series =====
section Ray_Ray_Analytic_Series
/-!
## Infinite series of analytic functions

Uniformly convergent series of analytic functions have analytic limits.
-/

open Complex
open Filter (atTop)
open Metric (ball closedBall sphere)
open scoped Real NNReal ENNReal Topology symmDiff
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type} [NormedAddCommGroup G]

/-- Summability restricted to sets -/
def SummableOn (f : ℕ → ℂ → E) (s : Set ℂ) :=
  ∀ z, z ∈ s → Summable fun n ↦ f n z

/-- `n ↦ f n z` has a convergent sum for each `z ∈ s` -/
def HasSumOn (f : ℕ → ℂ → E) (g : ℂ → E) (s : Set ℂ) :=
  ∀ z, z ∈ s → HasSum (fun n ↦ f n z) (g z)

/-- The parameterized limit of an infinite sum, if it exists -/
noncomputable def tsumOn (f : ℕ → ℂ → E) := fun z ↦ tsum fun n ↦ f n z

/-- Uniform convergence of sums on a set -/
def HasUniformSum (f : ℕ → ℂ → E) (g : ℂ → E) (s : Set ℂ) :=
  TendstoUniformlyOn (fun (N : Finset ℕ) z ↦ N.sum fun n ↦ f n z) g atTop s

/-- Uniform vanishing means late sums are uniformly small -/
def UniformVanishing (f : ℕ → ℂ → E) (s : Set ℂ) :=
  ∀ e : ℝ, e > 0 → ∃ n : ℕ, ∀ (N : Finset ℕ) (z), Late N n → z ∈ s → (N.sum fun n ↦ ‖f n z‖) < e

/-- Uniformly vanishing series results in uniform Cauchy sequences of finite sums -/
theorem uniformVanishing_to_uniform_cauchy_series {f : ℕ → ℂ → G} {s : Set ℂ}
    (h : UniformVanishing f s) :
    UniformCauchySeqOn (fun (N : Finset ℕ) z ↦ N.sum fun n ↦ f n z) atTop s := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro e ep
  rcases h e ep with ⟨m, hm⟩
  use Finset.range m
  intro A HA B HB z zs
  calc dist (A.sum fun n ↦ f n z) (B.sum fun n ↦ f n z)
    _ ≤ (A ∆ B).sum fun n ↦ ‖f n z‖ := symmDiff_bound _ _ _
    _ < e := hm (A ∆ B) z (symmDiff_late HA HB) zs

/-- Geometric bounds with c ≤ 0 are degenerate -/
theorem CNonpos.degenerate {f : ℕ → ℂ → G} {s : Set ℂ} {c a : ℝ} (c0 : c ≤ 0) (a0 : 0 ≤ a)
    (hf : ∀ n z, z ∈ s → ‖f n z‖ ≤ c * a ^ n) : ∀ n z, z ∈ s → f n z = 0 := by
  intro n z zs; specialize hf n z zs
  have ca : c * a ^ n ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨c0, by bound⟩)
  exact norm_eq_zero.mp (le_antisymm (le_trans hf ca) (norm_nonneg _))

/-- Adding one more term to a sum adds it, `Stream'.get` version to keep terms type-correct
    at low transparency -/
theorem sum_cons_get {a t : G} {q : Stream' G} (h : HasSum q.get t) :
    HasSum (Stream'.cons a q).get (a + t) := by
  rw [HasSum] at h ⊢
  have ha := Filter.Tendsto.comp (Continuous.tendsto (continuous_const_add a) t) h
  have s : ((fun z ↦ a + z) ∘ fun N : Finset ℕ ↦ N.sum q.get) =
      (fun N : Finset ℕ ↦ N.sum (Stream'.cons a q).get) ∘ push := by
    apply funext; intro N
    simp only [Function.comp_apply]
    exact push_sum_get
  rw [s] at ha
  exact tendsto_comp_push.mp ha

/-- Adding one more term to a sum adds it -/
theorem sum_cons {a g : G} {f : ℕ → G} (h : HasSum f g) :
    HasSum (Stream'.cons a f) (a + g) :=
  sum_cons_get (q := f) h

/-- Adding one more term to a sum adds it (`tprod` version) -/
lemma sum_cons' {a : G} {f : ℕ → G} (h : Summable f) :
    tsum (Stream'.cons a f) = a + tsum f := by
  rcases h with ⟨g, h⟩; rw [HasSum.tsum_eq h]; exact HasSum.tsum_eq (sum_cons h)

/-- Dropping the first term subtracts it -/
lemma sum_drop {f : ℕ → G} {g : G} (h : HasSum f g) :
    HasSum (fun n ↦ f (n + 1)) (g - f 0) := by
  rw [hasSum_nat_add_iff (f := f) 1]
  simpa using h

/-- Dropping the first term subtracts it (`tsum` version) -/
lemma tsum_drop {f : ℕ → G} (h : Summable f) :
    ∑' n, f n = f 0 + ∑' n, f (n + 1) := by
  rw [(sum_drop h.hasSum).tsum_eq, add_sub_cancel]

variable [CompleteSpace E] [CompleteSpace G]

/-- Uniformly vanishing series are summable -/
theorem uniformVanishing_to_summable {f : ℕ → ℂ → G} {s : Set ℂ} {z : ℂ} (zs : z ∈ s)
    (h : UniformVanishing f s) : Summable fun n ↦ f n z := by
  rw [summable_iff_vanishing_norm]; intro e ep
  rcases h e ep with ⟨m, hm⟩
  use Finset.range m; intro A d
  calc ‖A.sum (fun n ↦ f n z)‖
    _ ≤ A.sum (fun n ↦ ‖f n z‖) := by bound
    _ < e := hm _ _ (late_iff_disjoint_range.mpr d) zs

/-- If a series is uniformly vanishing, it tends to its limit uniformly -/
theorem uniformVanishing_to_tendsto_uniformly_on {f : ℕ → ℂ → G} {s : Set ℂ}
    (h : UniformVanishing f s) : HasUniformSum f (tsumOn f) s := by
  rw [HasUniformSum, Metric.tendstoUniformlyOn_iff]
  intro e ep
  rcases h (e / 4) (by linarith) with ⟨m, hm⟩
  rw [Filter.eventually_atTop]
  use Finset.range m
  intro N Nm z zs
  rw [tsumOn]
  generalize G : tsum (fun n ↦ f n z) = g
  have S : Summable (fun n ↦ f n z) := uniformVanishing_to_summable zs h
  have GS : HasSum (fun n ↦ f n z) g := by rw [← G]; exact Summable.hasSum S
  clear S
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop] at GS
  rcases GS (e / 4) (by linarith) with ⟨M, HM⟩; clear GS G h
  set A := N ∪ M \ N
  have AM : M ⊆ A := subset_union_sdiff _ _
  simp at HM
  specialize HM A AM
  rw [dist_comm] at HM
  calc dist g (N.sum fun n ↦ f n z)
    _ ≤ dist g (A.sum fun n ↦ f n z) + dist (A.sum fun n ↦ f n z) (N.sum fun n ↦ f n z) := by bound
    _ ≤ e / 4 + dist (A.sum fun n ↦ f n z) (N.sum fun n ↦ f n z) := by linarith
    _ = e / 4 + dist ((N.sum fun n ↦ f n z) + (M \ N).sum fun n ↦ f n z)
        (N.sum fun n ↦ f n z) := by rw [Finset.sum_union Finset.disjoint_sdiff]
    _ = e / 4 + ‖((N.sum fun n ↦ f n z) + (M \ N).sum fun n ↦ f n z) -
        N.sum fun n ↦ f n z‖ := by rw [dist_eq_norm]
    _ = e / 4 + ‖(M \ N).sum fun n ↦ f n z‖ := by rw [add_sub_cancel_left]
    _ ≤ e / 4 + (M \ N).sum fun n ↦ ‖f n z‖ := by
      linarith [finset_norm_sum_le (M \ N) fun n ↦ f n z]
    _ ≤ e / 4 + e / 4 := by linarith [hm (M \ N) z (sdiff_late M Nm) zs]
    _ = e / 2 := by ring
    _ < e := by linarith

/-- Uniformly exponentially converging series converge uniformly -/
theorem fast_series_converge_uniformly_on {f : ℕ → ℂ → G} {s : Set ℂ} {c a : ℝ} (a0 : 0 ≤ a)
    (a1 : a < 1) (hf : ∀ n z, z ∈ s → ‖f n z‖ ≤ c * a ^ n) : HasUniformSum f (tsumOn f) s := by
  by_cases c0 : c ≤ 0
  · have fz := CNonpos.degenerate c0 a0 hf
    rw [HasUniformSum, Metric.tendstoUniformlyOn_iff]
    intro e ep; refine .of_forall ?_; intro n z zs
    rw [tsumOn]
    simp_rw [fz _ z zs]
    simp only [tsum_zero, Finset.sum_const_zero, dist_zero_left, norm_zero]
    assumption
  · simp only [not_le] at c0
    apply uniformVanishing_to_tendsto_uniformly_on
    intro e ep
    set t := (1 - ↑a) / ↑c * (e / 2)
    have tp : t > 0 := by bound
    rcases exists_pow_lt_of_lt_one tp a1 with ⟨n, nt⟩
    use n; intro N z NL zs
    have a1p : 1 - (a : ℝ) > 0 := by linarith
    calc (N.sum fun n ↦ ‖f n z‖)
      _ ≤ N.sum fun n ↦ c * a ^ n := Finset.sum_le_sum fun n _ ↦ hf n z zs
      _ = c * N.sum fun n ↦ a ^ n := (Finset.mul_sum _ _ _).symm
      _ ≤ c * (a ^ n * (1 - a)⁻¹) := by bound [late_geometric_bound NL a0 a1]
      _ = a ^ n * (c * (1 - a)⁻¹) := by ring
      _ ≤ t * (c * (1 - a)⁻¹) := by bound
      _ = (1 - a) / c * (e / 2) * (c * (1 - a)⁻¹) := rfl
      _ = (1 - a) * (1 - a)⁻¹ * (c / c) * (e / 2) := by ring
      _ = 1 * 1 * (e / 2) := by rw [mul_inv_cancel₀ a1p.ne', div_self c0.ne']
      _ = e / 2 := by ring
      _ < e := by linarith

/-- Exponentially converging series converge -/
theorem fast_series_converge_at {f : ℕ → G} {c a : ℝ} (a0 : 0 ≤ a) (a1 : a < 1)
    (hf : ∀ n, ‖f n‖ ≤ c * a ^ n) : Summable f := by
  set s : Set ℂ := {0}
  set g : ℕ → ℂ → G := fun n _ ↦ f n
  have hg : ∀ n z, z ∈ s → ‖g n z‖ ≤ c * a ^ n := fun n z _ ↦ hf n
  have u := fast_series_converge_uniformly_on a0 a1 hg
  rw [HasUniformSum] at u
  rw [tendstoUniformlyOn_singleton_iff_tendsto] at u
  apply HasSum.summable; assumption

/-- Analytic series that converge exponentially converge to analytic functions -/
theorem fast_series_converge {f : ℕ → ℂ → E} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (a0 : 0 ≤ a) (a1 : a < 1) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (hf : ∀ n z, z ∈ s → ‖f n z‖ ≤ c * a ^ n) :
    ∃ g : ℂ → E, AnalyticOnNhd ℂ g s ∧ HasSumOn f g s := by
  use tsumOn f; constructor
  · exact uniform_analytic_lim o (fun N ↦ N.analyticOnNhd_fun_sum fun _ _ ↦ h _)
      (fast_series_converge_uniformly_on a0 a1 hf)
  · exact fun z zs ↦ Summable.hasSum (fast_series_converge_at a0 a1 fun n ↦ hf n z zs)

/-- Analytic series that converge exponentially converge to analytic functions, tsum version -/
theorem fast_series_converge_tsum_at {f : ℕ → ℂ → E} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (a0 : 0 ≤ a) (a1 : a < 1) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (hf : ∀ n z, z ∈ s → ‖f n z‖ ≤ c * a ^ n) :
    AnalyticOnNhd ℂ (fun z ↦ ∑' n, f n z) s := by
  obtain ⟨g, ga, gs⟩ := fast_series_converge o a0 a1 h hf
  rwa [analyticOnNhd_congr (g := g) o]
  intro z m
  simp only [(gs z m).tsum_eq]

end
end Ray_Ray_Analytic_Series

-- ===== Ray.Analytic.Products =====
section Ray_Ray_Analytic_Products
/-!
## Infinite products of analytic functions

We define convergence of infinite products, and show that uniform limits of products of
analytic functions are analytic.
-/

open Complex (exp log)
open Filter (atTop)
open Metric (ball closedBall sphere)
open Set
open scoped Classical Real NNReal ENNReal Topology
noncomputable section

variable {ι : Type}

/-!
### Basics about products of sequences
-/

/-- Powers commute with products -/
theorem product_pow {f : ℕ → ℂ} {g : ℂ} (p : ℕ) (h : HasProd f g) :
    HasProd (fun n ↦ f n ^ p) (g ^ p) := by
  rw [HasProd]; simp_rw [Finset.prod_pow]
  exact Filter.Tendsto.comp (Continuous.tendsto (continuous_pow p) g) h

/-- Powers commute with products (`tprod` version) -/
theorem product_pow' {f : ℕ → ℂ} {p : ℕ} (h : ProdExists f) :
    tprod f ^ p = tprod fun n ↦ f n ^ p := by
  rcases h with ⟨g, h⟩; rw [HasProd.tprod_eq h]; rw [HasProd.tprod_eq _]; exact product_pow p h

/-- Adding one more term to a product multiplies by it, `Stream'.get` version to keep terms
    type-correct at low transparency -/
theorem product_cons_get {a t : ℂ} {q : Stream' ℂ} (h : HasProd q.get t) :
    HasProd (Stream'.cons a q).get (a * t) := by
  rw [HasProd] at h ⊢
  have ha := Filter.Tendsto.comp (Continuous.tendsto (continuous_const_mul a) t) h
  have s : ((fun z ↦ a * z) ∘ fun N : Finset ℕ ↦ N.prod q.get) =
      (fun N : Finset ℕ ↦ N.prod (Stream'.cons a q).get) ∘ push := by
    apply funext; intro N
    simp only [Function.comp_apply]
    exact push_prod_get
  rw [s] at ha
  exact tendsto_comp_push.mp ha

/-- Adding one more term to a product multiplies by it -/
theorem product_cons {a g : ℂ} {f : ℕ → ℂ} (h : HasProd f g) :
    HasProd (Stream'.cons a f) (a * g) :=
  product_cons_get (q := f) h

/-- Adding one more term to a product multiplies by it (`tprod` version) -/
theorem product_cons' {a : ℂ} {f : ℕ → ℂ} (h : ProdExists f) :
    tprod (Stream'.cons a f) = a * tprod f := by
  rcases h with ⟨g, h⟩; rw [HasProd.tprod_eq h]; exact HasProd.tprod_eq (product_cons h)

/-- Dropping a nonzero term divides by it, `Stream'.get` version -/
theorem product_drop_get {q : Stream' ℂ} {t : ℂ} (q0 : q.head ≠ 0) (h : HasProd q.get t) :
    HasProd q.tail.get (t / q.head) := by
  have c := product_cons_get (a := q.head⁻¹) h
  rw [HasProd]
  rw [inv_mul_eq_div, HasProd, SummationFilter.unconditional_filter, ← tendsto_comp_push,
    ← tendsto_comp_push] at c
  have s : ((fun N : Finset ℕ ↦ N.prod (Stream'.cons q.head⁻¹ q).get) ∘ push) ∘ push =
      fun N : Finset ℕ ↦ N.prod q.tail.get := by
    apply funext; intro N
    simp only [Function.comp_apply]
    have e1 := push_prod_get (a := q.head⁻¹) (g := q) (N := push N)
    have e2 := push_prod_get (a := q.head) (g := q.tail) (N := N)
    rw [Stream'.eta q] at e2
    rw [← e1, ← e2, ← mul_assoc, inv_mul_cancel₀ q0, one_mul]
  rw [s] at c; exact c

/-- Dropping a nonzero term divides by it -/
theorem product_drop {f : ℕ → ℂ} {g : ℂ} (f0 : f 0 ≠ 0) (h : HasProd f g) :
    HasProd (fun n ↦ f (n + 1)) (g / f 0) :=
  product_drop_get (q := f) f0 h

/-- Dropping a nonzero term divides by it (`tprod` version) -/
theorem product_drop' {f : ℕ → ℂ} (f0 : f 0 ≠ 0) (h : ProdExists f) :
    (tprod fun n ↦ f (n + 1)) = tprod f / f 0 := by
  rcases h with ⟨g, h⟩; rw [HasProd.tprod_eq h]; rw [HasProd.tprod_eq _]; exact product_drop f0 h

/-- Products that start with zero are zero -/
theorem product_head_zero {f : ℕ → ℂ} (f0 : f 0 = 0) : HasProd f 0 := by
  rw [HasProd, SummationFilter.unconditional_filter, Metric.tendsto_atTop]; intro e ep
  use Finset.range 1; intro N N1
  simp at N1; rw [Finset.prod_eq_zero N1 f0]; simpa

/-- Separate out head and tail in a product -/
theorem product_split {f : ℕ → ℂ} (h : ProdExists f) :
    tprod f = f 0 * tprod fun n ↦ f (n + 1) := by
  by_cases f0 : f 0 = 0; · rw [f0, (product_head_zero f0).tprod_eq]; simp
  rw [product_drop' f0 h]; field_simp

/-!
### Infinite products of analytic functions
-/

/-- Analytic products that converge exponentially converge to analytic functions.
    For now, we require the constant to be `≤ 1/2` so that we can take logs without
    care, and get nonzero results. -/
theorem fast_products_converge {f : ℕ → ℂ → ℂ} {s : Set ℂ} {a c : ℝ} (o : IsOpen s)
    (c12 : c ≤ 1 / 2) (a0 : a ≥ 0) (a1 : a < 1) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (hf : ∀ n z, z ∈ s → ‖f n z - 1‖ ≤ c * a ^ n) :
    ∃ g : ℂ → ℂ, HasProdOn f g s ∧ AnalyticOnNhd ℂ g s ∧ ∀ z, z ∈ s → g z ≠ 0 := by
  set fl := fun n z ↦ log (f n z)
  have near1 : ∀ n z, z ∈ s → ‖f n z - 1‖ ≤ 1 / 2 := by
    intro n z zs
    calc ‖f n z - 1‖
      _ ≤ c * a ^ n := hf n z zs
      _ ≤ (1 / 2 : ℝ) * (1:ℝ) ^ n := by bound
      _ = 1 / 2 := by norm_num
  have near1' : ∀ n z, z ∈ s → ‖f n z - 1‖ < 1 := fun n z zs ↦
    lt_of_le_of_lt (near1 n z zs) (by linarith)
  have expfl : ∀ n z, z ∈ s → exp (fl n z) = f n z := by
    intro n z zs; refine Complex.exp_log ?_
    exact near_one_avoids_zero (near1' n z zs)
  have hl : ∀ n, AnalyticOnNhd ℂ (fl n) s := fun n ↦
    (h n).clog (fun z m ↦ mem_slitPlane_of_near_one (near1' n z m))
  set c2 := 2 * c
  have hfl : ∀ n z, z ∈ s → ‖fl n z‖ ≤ c2 * a ^ n := by
    intro n z zs
    calc ‖fl n z‖
      _ = ‖log (f n z)‖ := rfl
      _ ≤ 2 * ‖f n z - 1‖ := (log_small (near1 n z zs))
      _ ≤ 2 * (c * a ^ n) := by linarith [hf n z zs]
      _ = 2 * c * a ^ n := by ring
      _ = c2 * a ^ n := rfl
  rcases fast_series_converge o a0 a1 hl hfl with ⟨gl, gla, us⟩
  generalize hg : (fun z ↦ exp (gl z)) = g
  use g; refine ⟨?_, ?_, ?_⟩
  · intro z zs
    specialize us z zs
    have comp :
      Filter.Tendsto (exp ∘ fun N : Finset ℕ ↦ N.sum fun n ↦ fl n z) atTop (𝓝 (exp (gl z))) :=
      Filter.Tendsto.comp (Continuous.tendsto Complex.continuous_exp _) us
    have expsum0 : (exp ∘ fun N : Finset ℕ ↦ N.sum fun n ↦ fl n z) = fun N : Finset ℕ ↦
        N.prod fun n ↦ f n z := by
      apply funext; intro N; simp; rw [Complex.exp_sum]; simp_rw [expfl _ z zs]
    rw [expsum0] at comp; rw [← hg]; assumption
  · rw [← hg]; exact fun z zs ↦ analyticAt_cexp.comp (gla z zs)
  · simp only [Complex.exp_ne_zero, Ne, not_false_iff, imp_true_iff, ← hg]

/-- Same as above, but remove the requirement that `c ≤ 1/2` by peeling off the first few terms -/
theorem fast_products_converge_eventually {f : ℕ → ℂ → ℂ} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (a0 : 0 ≤ a) (a1 : a < 1) (fa : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (fb : ∀ᶠ n in atTop, ∀ z ∈ s, ‖f n z - 1‖ ≤ c * a ^ n) :
    ∃ g : ℂ → ℂ, HasProdOn f g s ∧ AnalyticOnNhd ℂ g s ∧
      ∀ z, z ∈ s → (∀ n, f n z ≠ 0) → g z ≠ 0 := by
  -- We need `c * a ^ n0 ≤ 1 / 2`, or `a ^ n0 ≤ 1 / (2 * c)`.
  have ta := (tendsto_const_nhds (x := c)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one a0 a1)
  simp only [mul_zero] at ta
  have low := ta.eventually_le_const (u := 1/2) (by norm_num)
  obtain ⟨N, h⟩ := Filter.eventually_atTop.mp (fb.and low)
  have fa' := fun n ↦ fa (N + n)
  have fb' : ∀ n z, z ∈ s → ‖f (N + n) z - 1‖ ≤ c * a ^ N * a ^ n := by
    intro n z zs
    exact le_trans ((h (N + n) (by omega)).1 z zs) (by simp only [pow_add, mul_assoc, le_refl])
  obtain ⟨g, fg, ga, g0⟩ := fast_products_converge o (h N (le_refl _)).2 a0 a1 fa' fb'
  refine ⟨fun z ↦ (∏ n ∈ Finset.range N, f n z) * g z, ?_, ?_, ?_⟩
  · intro z zs
    specialize fg z zs
    simp only at fg ⊢
    clear zs g0 ga fb' fa' h low ta fb fa a1 a0 o c a s
    suffices P : ∀ M, M ≤ N → HasProd (fun n ↦ f (N - M + n) z)
        ((∏ n ∈ Finset.range M, f (N - M + n) z) * g z) by
      simpa only [tsub_self, zero_add] using P N (le_refl _)
    intro M MN
    induction' M with M H
    · simpa using fg
    · specialize H (by omega)
      have e : ∀ k, (N - (M + 1) + (k + 1)) = (N - M + k) := by grind
      have ec : (Stream'.cons (f (N - (M + 1)) z) fun n ↦ f (N - M + n) z) =
          fun n ↦ f (N - (M + 1) + n) z := by
        ext n
        induction' n with n h
        · simp only [Stream'.get, Stream'.cons, add_zero]
        · simp only [Stream'.get, Stream'.cons]
          grind
      simpa only [Finset.prod_range_succ', e, add_zero, mul_comm _ (f _ _), mul_assoc (f _ _),
        ec] using product_cons (a := f (N - (M + 1)) z) H
  · exact (Finset.analyticOnNhd_fun_prod _ fun n _ ↦ fa n).mul ga
  · intro z zs f0
    simp [g0 z zs, Finset.prod_eq_zero_iff, f0]

/-- Same as `fast_products_converge`, but converge to `tprodOn` -/
theorem fast_products_converge' {f : ℕ → ℂ → ℂ} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (c12 : c ≤ 1 / 2) (a0 : 0 ≤ a) (a1 : a < 1) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (hf : ∀ n z, z ∈ s → ‖f n z - 1‖ ≤ c * a ^ n) :
    ProdExistsOn f s ∧ AnalyticOnNhd ℂ (tprodOn f) s ∧ ∀ z, z ∈ s → tprodOn f z ≠ 0 := by
  rcases fast_products_converge o c12 a0 a1 h hf with ⟨g, gp, ga, g0⟩
  refine ⟨?_, ?_, ?_⟩
  · exact fun z zs ↦ ⟨g z, gp z zs⟩
  · rwa [← analyticOnNhd_congr o fun z zs ↦ (gp.tprodOn_eq z zs).symm]
  · intro z zs; rw [gp.tprodOn_eq z zs]; exact g0 z zs

/-- Same as `fast_products_converge_eventually`, but converge to `tprodOn` -/
theorem fast_products_converge_eventually' {f : ℕ → ℂ → ℂ} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (a0 : 0 ≤ a) (a1 : a < 1) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (hf : ∀ᶠ n in atTop, ∀ z ∈ s, ‖f n z - 1‖ ≤ c * a ^ n) :
    ProdExistsOn f s ∧ AnalyticOnNhd ℂ (tprodOn f) s ∧
      ∀ z, z ∈ s → (∀ n, f n z ≠ 0) → tprodOn f z ≠ 0 := by
  rcases fast_products_converge_eventually o a0 a1 h hf with ⟨g, gp, ga, g0⟩
  refine ⟨?_, ?_, ?_⟩
  · exact fun z zs ↦ ⟨g z, gp z zs⟩
  · rwa [← analyticOnNhd_congr o fun z zs ↦ (gp.tprodOn_eq z zs).symm]
  · intro z zs; rw [gp.tprodOn_eq z zs]; exact g0 z zs

/-!
### Reasonably tight bounds on products
-/

lemma norm_mul_sub_one_le {a b : ℂ} :
    ‖a * b - 1‖ ≤ (1 + ‖a - 1‖) * (1 + ‖b - 1‖) - 1 := by
  -- Ugly semi-GPT 5.1 proof, but meh, it works.
  have h1 : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring_nf
  have h2 : ‖a * b - 1‖ ≤ ‖(a - 1) * (b - 1) + (a - 1)‖ + ‖b - 1‖ := by
    simpa [h1, add_assoc] using (norm_add_le ((a - 1) * (b - 1) + (a - 1)) (b - 1))
  have h3 : ‖(a - 1) * (b - 1) + (a - 1)‖ ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ := by bound
  have h4 : ‖a * b - 1‖ ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ + ‖b - 1‖ :=
    le_trans h2 (by simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right h3 ‖b - 1‖)
  have h5 : ‖a * b - 1‖ ≤ ‖a - 1‖ * ‖b - 1‖ + ‖a - 1‖ + ‖b - 1‖ := by
    simpa [norm_mul, add_comm, add_left_comm, add_assoc] using h4
  grind

lemma Finset.norm_prod_sub_one_le {f : ι → ℂ} {s : Finset ι} :
    ‖∏ i ∈ s, f i - 1‖ ≤ ∏ i ∈ s, (1 + ‖f i - 1‖) - 1 := by
  induction' s using Finset.induction with i s is h
  · simp only [prod_empty, sub_self, norm_zero, le_refl]
  · simp only [Finset.prod_insert is]
    exact le_trans norm_mul_sub_one_le (by bound)

/-- Bound a product in terms of bounds on the first few terms, and a geometric tail bound -/
lemma HasProd.norm_sub_one_le {f : ℕ → ℂ} {g : ℂ} (fg : HasProd f g)
    {n : ℕ} {b : Fin n → ℝ} (lo : ∀ k : Fin n, ‖f k - 1‖ ≤ b k)
    {c a : ℝ} (hi : ∀ k ≥ n, ‖f k - 1‖ ≤ c * a ^ k)
    (b0 : ∀ k, 0 ≤ b k) (c0 : 0 ≤ c) (a0 : 0 ≤ a) (a1 : a < 1) (ca : c * a ^ n / (1 - a) ≤ 1 / 2) :
    ‖g - 1‖ ≤ (∏ k, (1 + b k)) * (1 + 4 * c * a ^ n / (1 - a)) - 1 := by
  have le1 : ‖∏ i ∈ .range n, f i - 1‖ ≤ ∏ i, (1 + b i) - 1 := by
    refine le_trans Finset.norm_prod_sub_one_le ?_
    simp only [Finset.prod_fin_eq_prod_range]
    refine tsub_le_tsub_right (Finset.prod_le_prod (by bound) fun i m ↦ ?_) _
    specialize lo ⟨i, by simpa using m⟩
    grind
  rw [le_sub_iff_add_le, add_comm] at le1
  simp only [HasProd] at fg
  apply le_of_tendsto (Filter.Tendsto.comp continuous_norm.continuousAt (fg.sub_const 1))
  simp only [Function.comp_apply, SummationFilter.unconditional_filter, Filter.eventually_atTop]
  refine ⟨Finset.range n, fun s ns ↦ ?_⟩
  have le2 : ‖∏ i ∈ s \ .range n, f i - 1‖ ≤ 4 * c * a ^ n / (1 - a) := by
    simp only [mul_assoc, div_eq_mul_inv]
    set t := (s \ .range n).image fun k ↦ k - n
    have st : s \ .range n = t.image fun k ↦ k + n := by
      simp only [t, Finset.image_image, Function.comp_def]
      rw [Finset.image_congr (g := id), Finset.image_id]
      intro k m
      simp at m ⊢
      omega
    have inj : InjOn (fun k ↦ k + n) t := by intro  a _ b _; simp
    simp only [st, Finset.prod_image inj, ← mul_assoc c]
    refine dist_prod_one_le_abs_sum ?_ ca
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (partial_geometric_bound t a0 a1) (by bound))
    simp only [Finset.mul_sum, mul_assoc, ← pow_add, add_comm n]
    exact Finset.sum_le_sum fun i m ↦ hi _ (by omega)
  have d : Disjoint (Finset.range n) (s \ Finset.range n) := Finset.disjoint_sdiff
  have e : s = (Finset.range n).disjUnion (s \ Finset.range n) d := by simpa using ns
  rw [e, Finset.prod_disjUnion]
  exact le_trans norm_mul_sub_one_le (by bound)

end
end Ray_Ray_Analytic_Products


