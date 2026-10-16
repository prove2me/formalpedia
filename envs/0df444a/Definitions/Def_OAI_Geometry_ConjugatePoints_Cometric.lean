-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
-- name    : OAI_Geometry_ConjugatePoints_Cometric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:09:54.271927+00:00
-- url     : https://prove2.me/theorems/54c1d5f5-fc58-4564-892c-0084c36a7179
-- title:
--   Smooth radial profiles, bump functions and collar warping functions for the neck metrics
-- statement:
--   This file defines the one-variable profile functions from which the neck and collar metrics of the three-manifold construction are assembled, and records their elementary properties.
--
--   Throughout, $\psi : \mathbb{R} \to [0,1]$ is the standard smooth transition function: it is $C^\infty$ and nondecreasing, with $\psi = 0$ on $(-\infty, 0]$ and $\psi = 1$ on $[1, \infty)$. All other parameters ($L$, $K$, $\delta$, $r$, $t$, $u$, $y$) are real numbers.
--
--   1. **Radial profile.** Define
--   $$
--   \kappa(r) = \psi(4r - 1), \qquad \tau_L(r) = \bigl(1 - \kappa(r)\bigr)(r - L - 1) + \kappa(r)\,\frac{r - \log 2}{\log 4},
--   $$
--   $$
--   \sigma_L(r) = 1 - \kappa(r) + \frac{\kappa(r)}{\log 4} + \kappa'(r)\Bigl(\frac{r - \log 2}{\log 4} - (r - L - 1)\Bigr).
--   $$
--   Established: $\kappa = 0$ for $r \le 1/4$, $\kappa = 1$ for $r \ge 1/2$, $0 \le \kappa \le 1$, $\kappa$ is nondecreasing and $\kappa'$ vanishes outside $[1/4, 1/2]$; $\tau_L$ is $C^\infty$ with $\tau_L' = \sigma_L$; $\tau_L(r) = r - L - 1$ for $r \le 1/4$ and $\tau_L(r) = (r - \log 2)/\log 4$ for $r \ge 1/2$; if $L \ge 4$ then $\sigma_L(r) > 0$ for all $r$; $\tau_L(\log y) = (\log y - \log 2)/\log 4$ for $y \ge 2$; and for $y \in [2,8]$ and all $K, L$,
--   $$
--   \tau_K\Bigl(\log \frac{16}{y}\Bigr) = 1 - \tau_L(\log y).
--   $$
--   The numerical bounds $1/2 < \log 2 < 1 < \log 4 < 2$ are also recorded.
--
--   2. **Basic bumps.** Define
--   $$
--   a(u) = \begin{cases} e^{-1/(2/3 - u)}, & u < 2/3, \\ 0, & u \ge 2/3, \end{cases} \qquad A(u) = \int_0^u a(y)\,dy, \qquad \chi(t) = \psi\bigl(6(t - 5/12)\bigr).
--   $$
--   Established: $a$ is $C^\infty$ with $0 \le a < 1$ and $a = 0$ on $[2/3, \infty)$; $A$ is $C^\infty$ with $A' = a$, $A(0) = 0$, $A(u) \ge 0$ for $u \ge 0$, $A$ constant on $[2/3, \infty)$, $A(t) \ge t$ for $t \le 0$ and $A(t) \ge -1$ for $t \ge -1$; $\chi$ is $C^\infty$ with $\chi(t) = 0$ for $t \le 5/12$ and $\chi(t) = 1$ for $t \ge 7/12$ (and $\chi'$, $\chi''$ are $C^\infty$).
--
--   3. **Collar warping function.** With $\lambda(t) = \psi(2t + 3/2)$ (so $\lambda = 0$ for $t \le -3/4$ and $\lambda = 1$ for $t \ge -1/4$), define
--   $$
--   D_\delta(t) = 1 + \delta A(t), \quad \rho_\delta(t) = \frac{\delta\, a(t)}{2 D_\delta(t)}, \quad k_\delta(t) = 1 - \lambda(t) + \lambda(t)\rho_\delta(t), \quad \ell_\delta(t) = \exp\Bigl(-\int_0^t k_\delta(u)\,du\Bigr).
--   $$
--   Established for $\delta \in [0, 1/2]$: $D_\delta(t) \ge 1/2$ (hence $D_\delta(t) > 0$) for $t \ge -1$; $k_\delta = 1$ on $(-\infty, -3/4]$ and $k_\delta = \rho_\delta$ on $[-1/4, \infty)$; $k_\delta$ and $\ell_\delta$ are $C^\infty$; $\ell_\delta > 0$, $\ell_\delta(0) = 1$, $\ell_\delta' = -k_\delta \ell_\delta$; and
--   $$
--   \ell_\delta(t) = \bigl(1 + \delta A(t)\bigr)^{-1/2} \ \ (t > -1/4), \qquad \ell_\delta(t) = \ell_\delta(-1)\, e^{-(t+1)} \ \ (t \le -3/4).
--   $$
--
--   In the construction, $\tau_L$ converts the cusp height $\log y$ into a neck coordinate in which the collar gluing $y \mapsto 16/y$ becomes the reflection $t \mapsto 1 - t$; $\ell_\delta$ interpolates between an exponential (hyperbolic-cusp) profile and the profile $(1 + \delta A)^{-1/2}$ used in the neck; and $a$, $A$, $\chi$ are the building blocks of the neck cometric matrices.
--
--   **Formalization Note** $\psi$ is `Real.smoothTransition` and $a(u)$ is `expNegInvGlue (2/3 - u)`; integrals are interval integrals, and $\kappa'$ in $\sigma_L$ is `deriv cut`. Lean names: $\kappa$ = `RadialProfile.cut`, $\tau_L$ = `coordinate L`, $\sigma_L$ = `slope L`, $\lambda$ = `Collar.lam`, $D_\delta$ = `denom δ`, $\rho_\delta$ = `rate δ`, $k_\delta$ = `k δ`, $\ell_\delta$ = `ell δ`, and $a$, $A$, $\chi$ are `Cometric.a`, `Cometric.A`, `Cometric.χ`. The definition of $\rho_\delta$ involves a division, which Lean evaluates as $0$ where $D_\delta = 0$; the stated properties are only claimed under $\delta \in [0,1/2]$, where this does not occur on $[-1,\infty)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Cometric.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Cometric.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ConjugatePoints mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Radial profiles, cometrics, and collar estimates.
-/

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.RadialProfile

def cut (r : ℝ) : ℝ := Real.smoothTransition (4*r-1)
def coordinate (L r : ℝ) : ℝ :=
  (1-cut r)*(r-L-1) + cut r*((r-Real.log 2)/Real.log 4)
def slope (L r : ℝ) : ℝ :=
  1-cut r + cut r / Real.log 4 + deriv cut r *
    (((r-Real.log 2)/Real.log 4) - (r-L-1))
lemma cut_smooth : ContDiff ℝ ∞ cut :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
lemma cut_zero {r : ℝ} (h : r ≤ 1/4) : cut r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma cut_one {r : ℝ} (h : 1/2 ≤ r) : cut r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma cut_nonneg (r : ℝ) : 0 ≤ cut r := Real.smoothTransition.nonneg _
lemma cut_le_one (r : ℝ) : cut r ≤ 1 := Real.smoothTransition.le_one _
lemma cut_mono : Monotone cut :=
  Real.smoothTransition.monotone.comp (fun _ _ h => by linarith)
lemma cut_deriv_nonneg (r : ℝ) : 0 ≤ deriv cut r := cut_mono.deriv_nonneg
lemma cut_deriv_eq_zero {r : ℝ} (h : r ∉ Icc (1/4:ℝ) (1/2)) : deriv cut r = 0 := by
  rcases not_and_or.mp h with h|h
  · have hr : r < 1/4 := lt_of_not_ge h
    have he : cut =ᶠ[nhds r] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds hr] with x hx
      exact cut_zero hx.le
    exact he.deriv_eq.trans (deriv_const r 0)
  · have hr : 1/2 < r := lt_of_not_ge h
    have he : cut =ᶠ[nhds r] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact cut_one hx.le
    exact he.deriv_eq.trans (deriv_const r 1)
lemma log_bounds : 1/2 < Real.log 2 ∧ 1 < Real.log 4 ∧ Real.log 2 < 1 ∧ Real.log 4 < 2 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith
lemma coordinate_smooth (L : ℝ) : ContDiff ℝ ∞ (coordinate L) :=
  ((contDiff_const.sub cut_smooth).mul ((contDiff_id.sub contDiff_const).sub contDiff_const)).add
    (cut_smooth.mul ((contDiff_id.sub contDiff_const).div_const _))
lemma coordinate_deriv (L r : ℝ) : HasDerivAt (coordinate L) (slope L r) r := by
  have h := (((hasDerivAt_const r 1).sub (cut_smooth.differentiable (by simp) r).hasDerivAt).mul
    (((hasDerivAt_id r).sub_const L).sub_const 1)).add
    (((cut_smooth.differentiable (by simp) r).hasDerivAt).mul
      (((hasDerivAt_id r).sub_const (Real.log 2)).div_const (Real.log 4)))
  convert! h using 1
  simp only [slope, id_eq, Pi.sub_apply]
  ring
lemma coordinate_left {L r : ℝ} (h : r ≤ 1/4) : coordinate L r = r-L-1 := by
  simp [coordinate,cut_zero h]
lemma coordinate_right {L r : ℝ} (h : 1/2 ≤ r) :
    coordinate L r = (r-Real.log 2)/Real.log 4 := by
  simp [coordinate,cut_one h]
lemma transition_difference_pos {L r : ℝ} (hL : 4 ≤ L) (hr : r ∈ Icc (1/4:ℝ) (1/2)) :
    0 < (r-Real.log 2)/Real.log 4 - (r-L-1) := by
  have hb := log_bounds
  have hd : -(1:ℝ) < (r-Real.log 2)/Real.log 4 := by
    apply (lt_div_iff₀ (by linarith : 0 < Real.log 4)).mpr
    nlinarith [hr.1,hr.2]
  linarith [hr.2]
lemma slope_pos {L : ℝ} (hL : 4 ≤ L) (r : ℝ) : 0 < slope L r := by
  have hb := log_bounds
  have hbase : 0 < 1-cut r + cut r / Real.log 4 := by
    by_cases h : cut r = 0
    · simp [h]
    · have hp : 0 < cut r := lt_of_le_of_ne (cut_nonneg r) (Ne.symm h)
      exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr (cut_le_one r))
        (div_pos hp (by linarith))
  unfold slope
  by_cases h : r ∈ Icc (1/4:ℝ) (1/2)
  · exact add_pos_of_pos_of_nonneg hbase
      (mul_nonneg (cut_deriv_nonneg r) (transition_difference_pos hL h).le)
  · rw [cut_deriv_eq_zero h,zero_mul,add_zero]
    exact hbase
lemma coordinate_neck {L y : ℝ} (hy : 2 ≤ y) :
    coordinate L (Real.log y) = (Real.log y-Real.log 2)/Real.log 4 := by
  apply coordinate_right
  have hm : Real.log 2 ≤ Real.log y := Real.strictMonoOn_log.monotoneOn
    (by norm_num : (2:ℝ) ∈ Ioi 0) (show y ∈ Ioi (0:ℝ) by change 0 < y; linarith) hy
  linarith [log_bounds.1]
lemma coordinate_flip {L K y : ℝ} (hy : y ∈ Icc (2:ℝ) 8) :
    coordinate K (Real.log (16/y)) = 1-coordinate L (Real.log y) := by
  have hp : 0 < y := by linarith [hy.1]
  have hh : (2:ℝ) ≤ 16/y := (le_div_iff₀ hp).mpr (by linarith [hy.2])
  rw [coordinate_neck hh,coordinate_neck hy.1,Real.log_div (by norm_num) hp.ne']
  have h16 : Real.log 16 = 2*Real.log 4 := by
    rw [show (16:ℝ) = 4^2 by norm_num,Real.log_pow]; norm_num
  have h4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  rw [h16]
  field_simp
  linarith
end ThreeManifold.RadialProfile
end

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric

def a (u : ℝ) : ℝ := expNegInvGlue ((2 : ℝ) / 3 - u)

def A (u : ℝ) : ℝ := ∫ y in (0 : ℝ)..u, a y

def χ (t : ℝ) : ℝ := Real.smoothTransition (6 * (t - 5 / 12))

lemma a_formula (u : ℝ) :
    a u = if u < 2 / 3 then Real.exp (-1 / (2 / 3 - u)) else 0 := by
  unfold a expNegInvGlue
  split_ifs <;> (try congr 1) <;> (try simp_all only [not_lt, not_le]) <;>
    (first | linarith | simp [div_eq_mul_inv])

@[fun_prop] lemma a_smooth : ContDiff ℝ ∞ a :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)

lemma a_nonneg (u : ℝ) : 0 ≤ a u := expNegInvGlue.nonneg _

lemma a_eq_zero {u : ℝ} (hu : 2 / 3 ≤ u) : a u = 0 :=
  expNegInvGlue.zero_of_nonpos (by linarith)

lemma a_lt_one (u : ℝ) : a u < 1 := by
  rw [a_formula]
  split_ifs with hu
  · exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) (by linarith))
  · norm_num

lemma A_hasDerivAt (u : ℝ) : HasDerivAt A (a u) u :=
  a_smooth.continuous.integral_hasStrictDerivAt 0 u |>.hasDerivAt

lemma A_deriv : deriv A = a := funext fun u => (A_hasDerivAt u).deriv

@[fun_prop] lemma A_smooth : ContDiff ℝ ∞ A := by
  apply contDiff_infty_iff_deriv.mpr
  exact ⟨fun u => (A_hasDerivAt u).differentiableAt, A_deriv ▸ a_smooth⟩

lemma A_zero : A 0 = 0 := by simp [A]

lemma A_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ A u :=
  intervalIntegral.integral_nonneg hu (fun x _ => a_nonneg x)

lemma A_plateau {u v : ℝ} (hu : 2 / 3 ≤ u) (hv : 2 / 3 ≤ v) : A u = A v := by
  have hi : (∫ x in u..v, a x) = 0 := by
    calc
      (∫ x in u..v, a x) = ∫ _x in u..v, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact a_eq_zero (le_trans (le_min hu hv) hx.1)
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (a_smooth.continuous.intervalIntegrable 0 u)
    (a_smooth.continuous.intervalIntegrable u v)
  simpa [hi, A] using h

@[fun_prop] lemma χ_smooth : ContDiff ℝ ∞ χ :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

lemma χ_eq_zero {t : ℝ} (ht : t ≤ 5 / 12) : χ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma χ_eq_one {t : ℝ} (ht : 7 / 12 ≤ t) : χ t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma χ_deriv_smooth : ContDiff ℝ ∞ (deriv χ) :=
  (contDiff_infty_iff_deriv.mp χ_smooth).2

lemma χ_deriv2_smooth : ContDiff ℝ ∞ (deriv (deriv χ)) :=
  (contDiff_infty_iff_deriv.mp χ_deriv_smooth).2

end ThreeManifold.Cometric

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Collar
open Cometric

def lam (t : ℝ) : ℝ := Real.smoothTransition (2 * t + 3 / 2)
@[fun_prop] lemma lam_smooth : ContDiff ℝ ∞ lam := by unfold lam; fun_prop
lemma lam_zero {t : ℝ} (ht : t ≤ -3 / 4) : lam t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma lam_one {t : ℝ} (ht : -1 / 4 ≤ t) : lam t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma A_ge_self {t : ℝ} (ht : t ≤ 0) : t ≤ A t := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht
    (a_smooth.continuous.intervalIntegrable t 0)
    (continuous_const.intervalIntegrable t 0) (fun u _ => (a_lt_one u).le)
  simp only [intervalIntegral.integral_const, zero_sub, smul_eq_mul, mul_one] at h
  rw [A, intervalIntegral.integral_symm]
  linarith
lemma A_ge_neg_one {t : ℝ} (ht : -1 ≤ t) : -1 ≤ A t := by
  rcases le_total t 0 with h | h
  · exact ht.trans (A_ge_self h)
  · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (A_nonneg h)

def denom (δ t : ℝ) : ℝ := 1 + δ * A t
def rate (δ t : ℝ) : ℝ := δ * a t / (2 * denom δ t)
def k (δ t : ℝ) : ℝ := 1 - lam t + lam t * rate δ t
def ell (δ t : ℝ) : ℝ := Real.exp (-(∫ u in (0 : ℝ)..t, k δ u))

lemma denom_lower {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    1 / 2 ≤ denom δ t := by
  have h := mul_le_mul_of_nonneg_left (A_ge_neg_one ht) hδ.1
  dsimp [denom]; nlinarith [hδ.2]
lemma denom_pos {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    0 < denom δ t := lt_of_lt_of_le (by norm_num) (denom_lower hδ ht)
@[fun_prop] lemma denom_smooth (δ : ℝ) : ContDiff ℝ ∞ (denom δ) := by
  unfold denom; fun_prop
lemma denom_hasDerivAt (δ t : ℝ) : HasDerivAt (denom δ) (δ * a t) t :=
  ((A_hasDerivAt t).const_mul δ).const_add 1
lemma rate_contDiffAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    ContDiffAt ℝ ∞ (rate δ) t := by
  apply ContDiffAt.div (contDiffAt_const.mul a_smooth.contDiffAt)
    (contDiffAt_const.mul (denom_smooth δ).contDiffAt)
  exact mul_ne_zero (by norm_num) (ne_of_gt (denom_pos hδ ht))
lemma k_eq_one {δ t : ℝ} (ht : t ≤ -3 / 4) : k δ t = 1 := by
  simp [k, lam_zero ht]
lemma k_eq_rate {δ t : ℝ} (ht : -1 / 4 ≤ t) : k δ t = rate δ t := by
  simp [k, lam_one ht]
lemma k_smooth {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) : ContDiff ℝ ∞ (k δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t < -3 / 4
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact k_eq_one hu.le
  · have ht' : -1 ≤ t := by linarith
    exact (contDiffAt_const.sub lam_smooth.contDiffAt).add
      (lam_smooth.contDiffAt.mul (rate_contDiffAt hδ ht'))
lemma ell_pos (δ t : ℝ) : 0 < ell δ t := Real.exp_pos _
@[simp] lemma ell_zero (δ : ℝ) : ell δ 0 = 1 := by simp [ell]
lemma integral_k_smooth {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    ContDiff ℝ ∞ (fun t => ∫ u in (0 : ℝ)..t, k δ u) := by
  apply contDiff_infty_iff_deriv.mpr
  have hd (t : ℝ) := (k_smooth hδ).continuous.integral_hasStrictDerivAt 0 t |>.hasDerivAt
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  convert! k_smooth hδ using 1
  exact funext fun t => (hd t).deriv
lemma ell_smooth {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) : ContDiff ℝ ∞ (ell δ) :=
  (integral_k_smooth hδ).neg.exp
lemma ell_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    HasDerivAt (ell δ) (-k δ t * ell δ t) t := by
  have hd := (k_smooth hδ).continuous.integral_hasStrictDerivAt 0 t |>.hasDerivAt
  convert! hd.neg.exp using 1
  dsimp [ell]
  ring
lemma squared_end_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (ht : -1 / 4 ≤ t) :
    HasDerivAt (fun u => (ell δ u)^2 * denom δ u) 0 t := by
  have hD := ne_of_gt (denom_pos hδ (by linarith : -1 ≤ t))
  convert! ((ell_hasDerivAt hδ).pow 2).mul (denom_hasDerivAt δ t) using 1
  rw [k_eq_rate ht]
  dsimp [rate]
  field_simp; ring
lemma squared_end_constant {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (ht : -1 / 4 < t) : (ell δ t)^2 * denom δ t = 1 := by
  have hd (u : ℝ) (hu : u ∈ Ioi (-1 / 4)) := squared_end_hasDerivAt hδ hu.le
  have he := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hd u hu).deriv) ht (by norm_num : (0 : ℝ) ∈ Ioi (-1 / 4))
  simpa [denom, A_zero] using he

lemma ell_end_germ {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 / 4 < t) :
    ell δ t = (Real.sqrt (1 + δ * A t))⁻¹ := by
  have hD := denom_pos hδ (by linarith : -1 ≤ t)
  have hs := Real.sq_sqrt hD.le
  have he := squared_end_constant hδ ht
  have hp := ell_pos δ t
  have hspos := Real.sqrt_pos.mpr hD
  rw [inv_eq_one_div]
  apply (eq_div_iff hspos.ne').mpr
  change ell δ t * Real.sqrt (denom δ t) = 1
  nlinarith [mul_pos hp hspos, sq_nonneg (ell δ t * Real.sqrt (denom δ t) - 1)]

lemma ell_cusp_germ {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ≤ -3 / 4) :
    ell δ t = ell δ (-1) * Real.exp (-(t + 1)) := by
  have hi : (∫ u in (-1 : ℝ)..t, k δ u) = t + 1 := by
    calc
      _ = ∫ _ in (-1 : ℝ)..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact k_eq_one (hu.2.trans (max_le (by norm_num) ht))
      _ = t + 1 := by simp
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    ((k_smooth hδ).continuous.intervalIntegrable 0 (-1))
    ((k_smooth hδ).continuous.intervalIntegrable (-1) t)
  rw [hi] at he
  change Real.exp (-(∫ u in (0 : ℝ)..t, k δ u)) = _
  rw [← he, neg_add, Real.exp_add]
  rfl

end ThreeManifold.Collar

end

end OAI


