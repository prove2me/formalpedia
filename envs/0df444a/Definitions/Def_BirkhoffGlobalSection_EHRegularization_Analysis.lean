-- Prove2me | Definitions.Def_BirkhoffGlobalSection_EHRegularization_Analysis
-- name    : BirkhoffGlobalSection_EHRegularization_Analysis
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-02T10:13:04.170483+00:00
-- url     : https://prove2.me/theorems/49551886-e139-4bdb-b3a7-5d877e82ee0b
-- title:
--   Principal complex arsinh and real parts of complex hyperbolic functions
-- statement:
--   Generic complex-analysis layer for elliptic coordinates. `EHTrig`: for $\xi=x_1+ix_2$, $\cosh x_1\pm\cos x_2=2|\cosh(\xi/2)|^2,\ 2|\sinh(\xi/2)|^2$ and $\sinh 2x_1+i\sin 2x_2=2\sinh\xi\,\overline{\cosh\xi}$. `EHArsinh`: principal square root `csqrt` (via `cpow`) and $\operatorname{arsinh}w=\log(w+\sqrt{1+w^2})$ on $\{\mathrm{Re}(1+w^2)>0\}$, where $\mathrm{Re}\sqrt{1+w^2}>|\mathrm{Re}\,w|$; there $\sinh(\operatorname{arsinh}w)=w$, $\cosh(\operatorname{arsinh}w)=\sqrt{1+w^2}$, $|\mathrm{Im}\operatorname{arsinh}w|<\pi/2$, oddness, $\operatorname{arsinh}(\sinh u)=u$ for $|\mathrm{Im}\,u|<\pi/2$, holomorphy and the derivatives $1/\sqrt{1+w^2}$, $w/\sqrt{1+w^2}$ (implicit differentiation).
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS2 (elliptic-hyperbolic regularization, Section 9.2); explicit transport to the platform's Levi-Civita normalization constructed and verified here (momentum shift p -> p + (0, 1/2 - mu) between the barycentric rotating frame and the elliptic centre).

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Real-coordinate formulas for the complex hyperbolic functions (elliptic coordinates). -/

namespace EHTrig

open Complex

theorem sinh_eq_mk (ξ : ℂ) :
    sinh ξ = ⟨Real.sinh ξ.re * Real.cos ξ.im, Real.cosh ξ.re * Real.sin ξ.im⟩ := by
  conv_lhs => rw [← re_add_im ξ, sinh_add, sinh_mul_I, cosh_mul_I]
  apply Complex.ext <;>
    simp [← ofReal_sinh, ← ofReal_cosh, ← ofReal_sin, ← ofReal_cos, mul_re, mul_im]

theorem cosh_eq_mk (ξ : ℂ) :
    cosh ξ = ⟨Real.cosh ξ.re * Real.cos ξ.im, Real.sinh ξ.re * Real.sin ξ.im⟩ := by
  conv_lhs => rw [← re_add_im ξ, cosh_add, sinh_mul_I, cosh_mul_I]
  apply Complex.ext <;>
    simp [← ofReal_sinh, ← ofReal_cosh, ← ofReal_sin, ← ofReal_cos, mul_re, mul_im]

/-- `cosh x₁ + cos x₂ = 2 |cosh(ξ/2)|²`. -/
theorem cosh_add_cos (ξ : ℂ) :
    Real.cosh ξ.re + Real.cos ξ.im = 2 * normSq (cosh (ξ / 2)) := by
  rw [cosh_eq_mk, normSq_mk]
  have hx : ξ.re = 2 * (ξ / 2).re := by simp; ring
  have hy : ξ.im = 2 * (ξ / 2).im := by simp; ring
  rw [hx, hy, Real.cosh_two_mul, Real.cos_two_mul]
  have h1 := Real.cosh_sq_sub_sinh_sq (ξ / 2).re
  have h2 := Real.sin_sq_add_cos_sq (ξ / 2).im
  linear_combination (-(1 - 2 * Real.sin (ξ / 2).im ^ 2)) * h1 +
    (2 - 2 * Real.cosh (ξ / 2).re ^ 2) * h2

/-- `cosh x₁ − cos x₂ = 2 |sinh(ξ/2)|²`. -/
theorem cosh_sub_cos (ξ : ℂ) :
    Real.cosh ξ.re - Real.cos ξ.im = 2 * normSq (sinh (ξ / 2)) := by
  rw [sinh_eq_mk, normSq_mk]
  have hx : ξ.re = 2 * (ξ / 2).re := by simp; ring
  have hy : ξ.im = 2 * (ξ / 2).im := by simp; ring
  rw [hx, hy, Real.cosh_two_mul, Real.cos_two_mul]
  have h1 := Real.cosh_sq_sub_sinh_sq (ξ / 2).re
  have h2 := Real.sin_sq_add_cos_sq (ξ / 2).im
  linear_combination (-(1 - 2 * Real.cos (ξ / 2).im ^ 2)) * h1 -
    2 * Real.cosh (ξ / 2).re ^ 2 * h2

/-- `sinh 2x₁ = 2 Re(sinh ξ · conj(cosh ξ))`. -/
theorem sinh_two_re (ξ : ℂ) :
    Real.sinh (2 * ξ.re) = 2 * (sinh ξ * (starRingEnd ℂ) (cosh ξ)).re := by
  rw [sinh_eq_mk, cosh_eq_mk, Real.sinh_two_mul]
  simp only [mul_re, conj_re, conj_im]
  have h2 := Real.sin_sq_add_cos_sq ξ.im
  have h1 := Real.cosh_sq_sub_sinh_sq ξ.re
  linear_combination (-2 * Real.sinh ξ.re * Real.cosh ξ.re) * h2

/-- `sin 2x₂ = 2 Im(sinh ξ · conj(cosh ξ))`. -/
theorem sin_two_im (ξ : ℂ) :
    Real.sin (2 * ξ.im) = 2 * (sinh ξ * (starRingEnd ℂ) (cosh ξ)).im := by
  rw [sinh_eq_mk, cosh_eq_mk, Real.sin_two_mul]
  simp only [mul_im, conj_re, conj_im]
  have h1 := Real.cosh_sq_sub_sinh_sq ξ.re
  linear_combination (-2 * Real.sin ξ.im * Real.cos ξ.im) * h1

end EHTrig

/-! A principal complex `arsinh` on `{w | 0 < Re (1 + w²)}`. -/

namespace EHArsinh

open Complex

/-- Principal square root. -/
noncomputable def csqrt (u : ℂ) : ℂ := u ^ ((2 : ℂ)⁻¹)

theorem csqrt_sq (u : ℂ) : csqrt u ^ 2 = u := by
  simpa [csqrt] using Complex.cpow_nat_inv_pow u (n := 2) two_ne_zero

theorem re_csqrt_pos {u : ℂ} (hu : 0 < u.re) : 0 < (csqrt u).re := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have harg : |arg u| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hu)
  rw [csqrt, cpow_def_of_ne_zero hu0, exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have : (log u * (2 : ℂ)⁻¹).im = arg u / 2 := by
    rw [show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl, mul_comm, im_ofReal_mul,
      log_im]; ring
  rw [this]
  constructor <;> linarith [abs_lt.1 harg, Real.pi_pos]

/-- If `s² = 1 + w²` and `Re s > 0`, then `Re s > |Re w|`. -/
theorem re_gt_abs_re {w s : ℂ} (hs : s ^ 2 = 1 + w ^ 2) (hp : 0 < s.re) :
    |w.re| < s.re := by
  have hre := congrArg Complex.re hs
  have him := congrArg Complex.im hs
  simp only [sq, mul_re, mul_im, add_re, add_im, one_re, one_im] at hre him
  by_contra h
  push Not at h
  -- `s.re ≤ |w.re|` forces `|s.im| ≥ |w.im|`, contradicting the real part
  have hq : w.im ^ 2 ≤ s.im ^ 2 := by
    have h1 : s.re * s.im = w.re * w.im := by linarith
    have h2 : s.re ^ 2 ≤ w.re ^ 2 := by
      have := abs_nonneg w.re
      nlinarith [sq_abs w.re, abs_nonneg w.re]
    have h3 : (s.re * s.im) ^ 2 = (w.re * w.im) ^ 2 := by rw [h1]
    by_contra hlt
    push Not at hlt
    have : (s.re * s.im) ^ 2 < (w.re * w.im) ^ 2 ∨ w.re = 0 := by
      rcases eq_or_ne w.re 0 with h0 | h0
      · exact Or.inr h0
      · left
        have hsr2 : 0 < s.re ^ 2 := by positivity
        calc (s.re * s.im) ^ 2 = s.re ^ 2 * s.im ^ 2 := by ring
          _ < s.re ^ 2 * w.im ^ 2 := by exact mul_lt_mul_of_pos_left hlt hsr2
          _ ≤ w.re ^ 2 * w.im ^ 2 := by
              exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
          _ = (w.re * w.im) ^ 2 := by ring
    rcases this with h4 | h0
    · linarith
    · rw [h0] at h; simp at h; linarith
  have h2 : s.re ^ 2 ≤ w.re ^ 2 := by nlinarith [sq_abs w.re, abs_nonneg w.re]
  nlinarith

/-- The principal complex `arsinh`. -/
noncomputable def arsinhC (w : ℂ) : ℂ := log (w + csqrt (1 + w ^ 2))

section
variable {w : ℂ} (hw : 0 < (1 + w ^ 2).re)
include hw

theorem re_add_csqrt_pos : 0 < (w + csqrt (1 + w ^ 2)).re := by
  have hp := re_csqrt_pos hw
  have := re_gt_abs_re (csqrt_sq (1 + w ^ 2)) hp
  rw [add_re]; linarith [neg_abs_le w.re]

theorem add_csqrt_ne_zero : w + csqrt (1 + w ^ 2) ≠ 0 := fun h => by
  have := re_add_csqrt_pos hw; rw [h] at this; simp at this

theorem exp_arsinhC : exp (arsinhC w) = w + csqrt (1 + w ^ 2) :=
  exp_log (add_csqrt_ne_zero hw)

theorem exp_neg_arsinhC : exp (-arsinhC w) = csqrt (1 + w ^ 2) - w := by
  rw [exp_neg, exp_arsinhC hw]
  have h := add_csqrt_ne_zero hw
  field_simp
  linear_combination (-1 : ℂ) * csqrt_sq (1 + w ^ 2)

theorem sinh_arsinhC : sinh (arsinhC w) = w := by
  have h := two_sinh (arsinhC w)
  rw [exp_arsinhC hw, exp_neg_arsinhC hw] at h
  linear_combination h / 2

theorem cosh_arsinhC : cosh (arsinhC w) = csqrt (1 + w ^ 2) := by
  have h := two_cosh (arsinhC w)
  rw [exp_arsinhC hw, exp_neg_arsinhC hw] at h
  linear_combination h / 2

theorem abs_im_arsinhC_lt : |(arsinhC w).im| < Real.pi / 2 := by
  rw [arsinhC, log_im]
  exact Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (re_add_csqrt_pos hw))

end

/-- `csqrt (v²) = v` when `Re v > 0`. -/
theorem csqrt_sq_of_re_pos {v : ℂ} (hv : 0 < v.re) : csqrt (v ^ 2) = v := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  have harg : |arg v| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hv)
  have hexp : v ^ 2 = exp (2 * log v) := by rw [two_mul, exp_add, exp_log hv0]; ring
  have him : (2 * log v).im = 2 * arg v := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, im_ofReal_mul, log_im]
  have hlog : log (v ^ 2) = 2 * log v := by
    rw [hexp, log_exp] <;> rw [him] <;> linarith [abs_lt.1 harg, Real.pi_pos]
  rw [csqrt, cpow_def_of_ne_zero (pow_ne_zero 2 hv0), hlog]
  rw [show 2 * log v * (2 : ℂ)⁻¹ = log v by ring, exp_log hv0]

/-- `arsinhC (sinh u) = u` on the strip `|Im u| < π/2`. -/
theorem arsinhC_sinh {u : ℂ} (hu : |u.im| < Real.pi / 2) : arsinhC (sinh u) = u := by
  have hc : 0 < (cosh u).re := by
    have : (cosh u).re = Real.cosh u.re * Real.cos u.im := by
      conv_lhs => rw [← re_add_im u, cosh_add, sinh_mul_I, cosh_mul_I]
      simp [← ofReal_sinh, ← ofReal_cosh, ← ofReal_sin, ← ofReal_cos, mul_re]
    rw [this]
    exact mul_pos (Real.cosh_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_lt.1 hu],
      by linarith [abs_lt.1 hu]⟩)
  have h1 : 1 + sinh u ^ 2 = cosh u ^ 2 := by rw [← cosh_sq_sub_sinh_sq u]; ring
  rw [arsinhC, h1, csqrt_sq_of_re_pos hc, add_comm, cosh_add_sinh, log_exp]
  · linarith [abs_lt.1 hu, Real.pi_pos]
  · linarith [abs_lt.1 hu, Real.pi_pos]

/-- `arsinhC` is odd on `{0 < Re (1 + w²)}`. -/
theorem arsinhC_neg {w : ℂ} (hw : 0 < (1 + w ^ 2).re) : arsinhC (-w) = -arsinhC w := by
  have hpos := re_add_csqrt_pos hw
  have hne := add_csqrt_ne_zero hw
  have hprod : (-w + csqrt (1 + w ^ 2)) = (w + csqrt (1 + w ^ 2))⁻¹ := by
    field_simp
    linear_combination csqrt_sq (1 + w ^ 2)
  have harg : (w + csqrt (1 + w ^ 2)).arg ≠ Real.pi := by
    intro h
    have := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hpos)
    rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]
  rw [arsinhC, neg_sq, hprod, log_inv _ harg, arsinhC]

end EHArsinh

/-! Complex derivatives and analyticity of `csqrt` and `arsinhC`. -/

namespace EHArsinh

open Complex

/-- The open set where `arsinhC` is regular. -/
def arsinhDom : Set ℂ := {w | 0 < (1 + w ^ 2).re}

theorem isOpen_arsinhDom : IsOpen arsinhDom :=
  isOpen_lt continuous_const (Complex.continuous_re.comp (by fun_prop))

theorem slit_of_re_pos {u : ℂ} (hu : 0 < u.re) : u ∈ slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl hu)

theorem differentiableAt_csqrt {u : ℂ} (hu : u ∈ slitPlane) : DifferentiableAt ℂ csqrt u :=
  differentiableAt_id.cpow_const hu

theorem csqrt_ne_zero {u : ℂ} (hu : 0 < u.re) : csqrt u ≠ 0 := fun h => by
  have := re_csqrt_pos hu; rw [h] at this; simp at this

theorem hasDerivAt_csqrt {u : ℂ} (hu : 0 < u.re) :
    HasDerivAt csqrt (1 / (2 * csqrt u)) u := by
  have hd := (differentiableAt_csqrt (slit_of_re_pos hu)).hasDerivAt
  have h2 := hd.pow 2
  have hf : (csqrt ^ 2) = id := by funext v; simp [csqrt_sq]
  have h3 : HasDerivAt (csqrt ^ 2) 1 u := hf ▸ hasDerivAt_id u
  have hu' := csqrt_ne_zero hu
  have := h2.unique h3
  simp only [Nat.cast_ofNat] at this
  rw [show deriv csqrt u = 1 / (2 * csqrt u) by field_simp; linear_combination this] at hd
  exact hd

theorem differentiableAt_arsinhC {w : ℂ} (hw : w ∈ arsinhDom) :
    DifferentiableAt ℂ arsinhC w := by
  have h1 : DifferentiableAt ℂ (fun v : ℂ => v + csqrt (1 + v ^ 2)) w :=
    differentiableAt_id.add ((differentiableAt_csqrt (slit_of_re_pos hw)).comp w
      ((differentiableAt_const (1 : ℂ)).add (differentiableAt_pow 2)))
  exact h1.clog (slit_of_re_pos (re_add_csqrt_pos hw))

theorem differentiableOn_arsinhC : DifferentiableOn ℂ arsinhC arsinhDom :=
  fun _ hw => (differentiableAt_arsinhC hw).differentiableWithinAt

theorem hasDerivAt_arsinhC {w : ℂ} (hw : w ∈ arsinhDom) :
    HasDerivAt arsinhC (1 / csqrt (1 + w ^ 2)) w := by
  have hd := (differentiableAt_arsinhC hw).hasDerivAt
  have h2 : HasDerivAt (fun v => sinh (arsinhC v)) (cosh (arsinhC w) * deriv arsinhC w) w :=
    (Complex.hasDerivAt_sinh _).comp w hd
  have h3 : HasDerivAt (fun v => sinh (arsinhC v)) 1 w := by
    have hev : (fun v => sinh (arsinhC v)) =ᶠ[nhds w] id :=
      Filter.eventuallyEq_of_mem (isOpen_arsinhDom.mem_nhds hw) fun v hv => sinh_arsinhC hv
    exact (hasDerivAt_id w).congr_of_eventuallyEq hev
  have := h2.unique h3
  rw [cosh_arsinhC hw] at this
  have hne := csqrt_ne_zero hw
  rw [show deriv arsinhC w = 1 / csqrt (1 + w ^ 2) by field_simp; linear_combination this] at hd
  exact hd

theorem contDiffOn_arsinhC {n : WithTop ℕ∞} : ContDiffOn ℂ n arsinhC arsinhDom :=
  (differentiableOn_arsinhC.analyticOnNhd isOpen_arsinhDom).contDiffOn
    isOpen_arsinhDom.uniqueDiffOn

/-- `S(w) = csqrt (1 + w²)` is smooth on `arsinhDom`. -/
theorem contDiffOn_S {n : WithTop ℕ∞} :
    ContDiffOn ℂ n (fun w : ℂ => csqrt (1 + w ^ 2)) arsinhDom := by
  have hd : DifferentiableOn ℂ (fun w : ℂ => csqrt (1 + w ^ 2)) arsinhDom := fun w hw =>
    ((differentiableAt_csqrt (slit_of_re_pos hw)).comp w
      ((differentiableAt_const (1 : ℂ)).add (differentiableAt_pow 2))).differentiableWithinAt
  exact (hd.analyticOnNhd isOpen_arsinhDom).contDiffOn isOpen_arsinhDom.uniqueDiffOn

theorem hasDerivAt_S {w : ℂ} (hw : w ∈ arsinhDom) :
    HasDerivAt (fun v : ℂ => csqrt (1 + v ^ 2)) (w / csqrt (1 + w ^ 2)) w := by
  have h := (hasDerivAt_csqrt hw).comp w ((hasDerivAt_pow 2 w).const_add 1)
  have hne := csqrt_ne_zero hw
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
  field_simp

end EHArsinh


