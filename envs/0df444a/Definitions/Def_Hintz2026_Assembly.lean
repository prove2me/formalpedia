-- Prove2me | Definitions.Def_Hintz2026_Assembly
-- name    : Hintz2026_Assembly
-- status  : Definition
-- author  : @He Wang
-- created : 2026-10-19T13:17:10.409654+00:00
-- url     : https://prove2.me/theorems/f0fe0705-8985-45fc-92c5-fc234bba8931
-- title:
--   Hintz2026 — Derivatives of X entries and D⁻X = AX
-- statement:
--   Computes the slice derivatives $\partial_r X_{ij}$ and $\partial_\theta X_{ij}$ of all four entries of $X$, assembles them into the matrix integrating-factor equation $(\sqrt{\Delta}\partial_r - i\partial_\theta)X = AX$ (Hintz eq. 6) and its companion $(\sqrt{\Delta}\partial_r + i\partial_\theta)(X^*)^{-1} = -A(X^*)^{-1}$. This bundle contains the explicit derivative calculations and the two matrix integrating-factor theorems. The Leibniz rules and the negative-control operator are in `Hintz2026_AnalysisV2`; the residual and solution-correspondence results are separate theorem nodes built from that infrastructure.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6)

import Definitions.Def_Hintz2026_Core

/-!
# Hintz 2026 — Assembly: entry derivatives, D₋X = AX, D₊(X*)⁻¹ = -A(X*)⁻¹
-/

set_option maxHeartbeats 8000000

open Complex Matrix
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

-- ═══ From XDiagDeriv.lean ═══






private theorem hasDerivAt_ofReal_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun u => (↑(f u) : ℂ)) (↑f') x :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hf

/-! ### Numerator derivatives -/

private theorem hasDerivAt_Nplus_r (x : Fin 2 → ℝ) (hD : 0 < Del p (x 0)) :
    HasDerivAt (fun u => (↑p.Q : ℂ) * (↑(Real.sqrt (Del p u)) + ↑p.a * ↑(Real.sin (x 1))))
      (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) :=
  ((hasDerivAt_ofReal_comp (hasDerivAt_sqrtDel_r p hD)).add (hasDerivAt_const _ _)).const_mul _
    |>.congr_deriv (by push_cast; ring)

private theorem hasDerivAt_Nplus_th (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => (↑p.Q : ℂ) * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin u)))
      (↑p.Q * ↑p.a * ↑(Real.cos (x 1))) (x 1) :=
  ((hasDerivAt_const _ _).add ((hasDerivAt_ofReal_comp (Real.hasDerivAt_sin (x 1))).const_mul _)).const_mul _
    |>.congr_deriv (by push_cast; ring)

private theorem hasDerivAt_Nminus_r (x : Fin 2 → ℝ) (hD : 0 < Del p (x 0)) :
    HasDerivAt (fun u => (↑p.Q : ℂ) * (↑(Real.sqrt (Del p u)) - ↑p.a * ↑(Real.sin (x 1))))
      (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) := by
  exact ((hasDerivAt_ofReal_comp (hasDerivAt_sqrtDel_r p hD)).sub (hasDerivAt_const _ _)).const_mul _
    |>.congr_deriv (by push_cast; ring)

private theorem hasDerivAt_Nminus_th (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => (↑p.Q : ℂ) * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin u)))
      (-↑p.Q * ↑p.a * ↑(Real.cos (x 1))) (x 1) := by
  exact ((hasDerivAt_const _ (↑(Real.sqrt (Del p (x 0))) : ℂ)).sub
    ((hasDerivAt_ofReal_comp (Real.hasDerivAt_sin (x 1))).const_mul _)).const_mul _
    |>.congr_deriv (by push_cast; ring)

/-! ### X₀₀ HasDerivAt -/

theorem hasDerivAt_X00_r (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X00 p (Function.update x 0 u))
      ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1)))) /
        (rhoBar p x) ^ 2) (x 0) :=
  ((hasDerivAt_Nplus_r p x (Del_pos p hx.1)).div
    (hasDerivAt_rhoBar_r p x) (rhoBar_ne_zero p hx)).congr_of_eventuallyEq
    (by filter_upwards with u; exact (X00_r_eq p x u).symm)
    |>.congr_deriv (by simp [Function.update_eq_self])

theorem hasDerivAt_X00_th (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X00 p (Function.update x 1 u))
      ((↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) *
          (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ)) /
        (rhoBar p x) ^ 2) (x 1) :=
  ((hasDerivAt_Nplus_th p x).div
    (hasDerivAt_rhoBar_th p x) (rhoBar_ne_zero p hx)).congr_of_eventuallyEq
    (by filter_upwards with u; exact (X00_th_eq p x u).symm)
    |>.congr_deriv (by simp [Function.update_eq_self])

/-! ### X₁₁ HasDerivAt -/

theorem hasDerivAt_X11_r (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X11 p (Function.update x 0 u))
      ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))) /
        (rhoBarStar p x) ^ 2) (x 0) :=
  ((hasDerivAt_Nminus_r p x (Del_pos p hx.1)).div
    (hasDerivAt_rhoBarStar_r p x) (rhoBarStar_ne_zero p hx)).congr_of_eventuallyEq
    (by filter_upwards with u; exact (X11_r_eq p x u).symm)
    |>.congr_deriv (by simp [Function.update_eq_self])

theorem hasDerivAt_X11_th (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X11 p (Function.update x 1 u))
      ((-↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBarStar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) *
          (⟨0, p.a * Real.sin (x 1)⟩ : ℂ)) /
        (rhoBarStar p x) ^ 2) (x 1) :=
  ((hasDerivAt_Nminus_th p x).div
    (hasDerivAt_rhoBarStar_th p x) (rhoBarStar_ne_zero p hx)).congr_of_eventuallyEq
    (by filter_upwards with u; exact (X11_th_eq p x u).symm)
    |>.congr_deriv (by simp [Function.update_eq_self])

/-! ### cpd -/

theorem cpd_X00_r' {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (X00 p) x = (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1)))) / (rhoBar p x) ^ 2 :=
  (hasDerivAt_X00_r p x hx).deriv

theorem cpd_X00_th' {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (X00 p) x = (↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) *
        (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ)) / (rhoBar p x) ^ 2 :=
  (hasDerivAt_X00_th p x hx).deriv

theorem cpd_X11_r' {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (X11 p) x = (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))) / (rhoBarStar p x) ^ 2 :=
  (hasDerivAt_X11_r p x hx).deriv

theorem cpd_X11_th' {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (X11 p) x = (-↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBarStar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) *
        (⟨0, p.a * Real.sin (x 1)⟩ : ℂ)) / (rhoBarStar p x) ^ 2 :=
  (hasDerivAt_X11_th p x hx).deriv


private theorem cpd_X00_r_mul {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (X00 p) x * (rhoBar p x) ^ 2 =
    ↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) :=
  by rw [cpd_X00_r' p hx, div_mul_cancel₀ _ (pow_ne_zero 2 (rhoBar_ne_zero p hx))]

private theorem cpd_X00_th_mul {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (X00 p) x * (rhoBar p x) ^ 2 =
    ↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) *
        (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) :=
  by rw [cpd_X00_th' p hx, div_mul_cancel₀ _ (pow_ne_zero 2 (rhoBar_ne_zero p hx))]


private theorem cpd_X11_r_mul {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (X11 p) x * (rhoBarStar p x) ^ 2 =
    ↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) :=
  by rw [cpd_X11_r' p hx, div_mul_cancel₀ _ (pow_ne_zero 2 (rhoBarStar_ne_zero p hx))]

private theorem cpd_X11_th_mul {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (X11 p) x * (rhoBarStar p x) ^ 2 =
    -↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBarStar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) *
        (⟨0, p.a * Real.sin (x 1)⟩ : ℂ) :=
  by rw [cpd_X11_th' p hx, div_mul_cancel₀ _ (pow_ne_zero 2 (rhoBarStar_ne_zero p hx))]

/-! ### Dm -/

theorem Dm_X00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (X00 p) x =
    ↑p.Q * (↑p.M * rhoBarStar p x - ↑(p.Q ^ 2)) / (rhoBar p x) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 (rhoBar_ne_zero p hx))]
  unfold Dm
  rw [show (↑(Real.sqrt (Del p (x 0))) * cpd 0 (X00 p) x - I * cpd 1 (X00 p) x) *
    (rhoBar p x) ^ 2 =
    ↑(Real.sqrt (Del p (x 0))) * (cpd 0 (X00 p) x * (rhoBar p x) ^ 2) -
    I * (cpd 1 (X00 p) x * (rhoBar p x) ^ 2) from by ring]
  rw [cpd_X00_r_mul p hx, cpd_X00_th_mul p hx]
  have hcancel : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) =
    ↑(x 0 - p.M) := by
    rw [← ofReal_mul, mul_div_cancel₀ _ (Real.sqrt_ne_zero'.mpr (Del_pos p hx.1))]
  have hsqsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(Real.sqrt (Del p (x 0))) =
    ↑(Del p (x 0)) := by
    rw [← ofReal_mul, Real.mul_self_sqrt (le_of_lt (Del_pos p hx.1))]
  conv_lhs =>
    rw [show ↑(Real.sqrt (Del p (x 0))) *
      (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x -
       ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1)))) =
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) * rhoBar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) * ↑(Real.sqrt (Del p (x 0))) +
        ↑(Real.sqrt (Del p (x 0))) * (↑p.a * ↑(Real.sin (x 1)))) from by ring]
  rw [hcancel, hsqsq]
  simp only [rhoBar, rhoBarStar]
  have hDel : Del p (x 0) = x 0 ^ 2 - 2 * p.M * x 0 + p.a ^ 2 + p.Q ^ 2 := rfl
  have htrig : Real.sin (x 1) ^ 2 + Real.cos (x 1) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hre1 : (⟨x 0, p.a * Real.cos (x 1)⟩ : ℂ).re = x 0 := rfl
  have him1 : (⟨x 0, p.a * Real.cos (x 1)⟩ : ℂ).im = p.a * Real.cos (x 1) := rfl
  have hre2 : (⟨x 0, -(p.a * Real.cos (x 1))⟩ : ℂ).re = x 0 := rfl
  have him2 : (⟨x 0, -(p.a * Real.cos (x 1))⟩ : ℂ).im = -(p.a * Real.cos (x 1)) := rfl
  have hre3 : (⟨(0 : ℝ), -(p.a * Real.sin (x 1))⟩ : ℂ).re = 0 := rfl
  have him3 : (⟨(0 : ℝ), -(p.a * Real.sin (x 1))⟩ : ℂ).im = -(p.a * Real.sin (x 1)) := rfl
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      hre1, him1, hre2, him2, hre3, him3]
  · linear_combination -p.Q * hDel + p.Q * p.a ^ 2 * htrig
  · linear_combination (0 : ℝ)

theorem Dm_X11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (X11 p) x =
    ↑p.Q * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (rhoBarStar p x) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 (rhoBarStar_ne_zero p hx))]
  unfold Dm
  rw [show (↑(Real.sqrt (Del p (x 0))) * cpd 0 (X11 p) x - I * cpd 1 (X11 p) x) *
    (rhoBarStar p x) ^ 2 =
    ↑(Real.sqrt (Del p (x 0))) * (cpd 0 (X11 p) x * (rhoBarStar p x) ^ 2) -
    I * (cpd 1 (X11 p) x * (rhoBarStar p x) ^ 2) from by ring]
  rw [cpd_X11_r_mul p hx, cpd_X11_th_mul p hx]
  have hcancel : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) =
    ↑(x 0 - p.M) := by
    rw [← ofReal_mul, mul_div_cancel₀ _ (Real.sqrt_ne_zero'.mpr (Del_pos p hx.1))]
  have hsqsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(Real.sqrt (Del p (x 0))) =
    ↑(Del p (x 0)) := by
    rw [← ofReal_mul, Real.mul_self_sqrt (le_of_lt (Del_pos p hx.1))]
  conv_lhs =>
    rw [show ↑(Real.sqrt (Del p (x 0))) *
      (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x -
       ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))) =
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) * rhoBarStar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) * ↑(Real.sqrt (Del p (x 0))) -
        ↑(Real.sqrt (Del p (x 0))) * (↑p.a * ↑(Real.sin (x 1)))) from by ring]
  rw [hcancel, hsqsq]
  simp only [rhoBar, rhoBarStar]
  have hDel : Del p (x 0) = x 0 ^ 2 - 2 * p.M * x 0 + p.a ^ 2 + p.Q ^ 2 := rfl
  have htrig : Real.sin (x 1) ^ 2 + Real.cos (x 1) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hre1 : (⟨x 0, p.a * Real.cos (x 1)⟩ : ℂ).re = x 0 := rfl
  have him1 : (⟨x 0, p.a * Real.cos (x 1)⟩ : ℂ).im = p.a * Real.cos (x 1) := rfl
  have hre2 : (⟨x 0, -(p.a * Real.cos (x 1))⟩ : ℂ).re = x 0 := rfl
  have him2 : (⟨x 0, -(p.a * Real.cos (x 1))⟩ : ℂ).im = -(p.a * Real.cos (x 1)) := rfl
  have hre3 : (⟨(0 : ℝ), p.a * Real.sin (x 1)⟩ : ℂ).re = 0 := rfl
  have him3 : (⟨(0 : ℝ), p.a * Real.sin (x 1)⟩ : ℂ).im = p.a * Real.sin (x 1) := rfl
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      hre1, him1, hre2, him2, hre3, him3]
  · linear_combination -p.Q * hDel + p.Q * p.a ^ 2 * htrig
  · linear_combination (0 : ℝ)


-- ═══ From XDerivatives.lean ═══

/-!
# Hintz 2026 — Slice derivatives of X entries and D₋X = AX
-/





/-! ### X entry reductions -/

@[simp] theorem X_01_eq (z : Fin 2 → ℝ) :
    X p z 0 1 = -I * (↑p.M - ↑(p.Q ^ 2) / rhoBar p z) := by simp [X]

@[simp] theorem X_10_eq (z : Fin 2 → ℝ) :
    X p z 1 0 = I * (↑p.M - ↑(p.Q ^ 2) / rhoBarStar p z) := by simp [X]

/-! ### HasDerivAt for X₀₁ slices using congr_of_eventuallyEq -/

theorem hasDerivAt_X01_r (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X p (Function.update x 0 u) 0 1)
      (I * ↑(p.Q ^ 2) * (-1 / (rhoBar p x) ^ 2)) (x 0) := by
  -- Build HasDerivAt for the decomposed form
  have hc : HasDerivAt (fun _ : ℝ => -I * (↑p.M : ℂ)) 0 (x 0) := hasDerivAt_const _ _
  have hinv := (hasDerivAt_rhoBar_r p x).inv (rhoBar_ne_zero p hx)
  have hmul := hinv.const_mul (I * ↑(p.Q ^ 2))
  have hsum := hc.add hmul
  -- hsum is for the decomposed function; congr to match X form
  refine hsum.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    simp only [X_01_eq, Pi.add_apply, Pi.inv_apply]; ring
  · simp only [Function.update_eq_self]; ring

theorem hasDerivAt_X01_th (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X p (Function.update x 1 u) 0 1)
      (I * ↑(p.Q ^ 2) * (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) / (rhoBar p x) ^ 2)) (x 1) := by
  have hc : HasDerivAt (fun _ : ℝ => -I * (↑p.M : ℂ)) 0 (x 1) := hasDerivAt_const _ _
  have hinv := (hasDerivAt_rhoBar_th p x).inv (rhoBar_ne_zero p hx)
  have hmul := hinv.const_mul (I * ↑(p.Q ^ 2))
  refine (hc.add hmul).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    simp only [X_01_eq, Pi.add_apply, Pi.inv_apply]; ring
  · simp only [Function.update_eq_self]; ring

/-! ### cpd of X₀₁ -/

theorem cpd_X01_r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => X p z 0 1) x =
    I * ↑(p.Q ^ 2) * (-1 / (rhoBar p x) ^ 2) :=
  (hasDerivAt_X01_r p x hx).deriv

theorem cpd_X01_th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => X p z 0 1) x =
    I * ↑(p.Q ^ 2) * (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) / (rhoBar p x) ^ 2) :=
  (hasDerivAt_X01_th p x hx).deriv

/-! ### Dm of X₀₁ -/

-- ⟨0, y⟩ = ↑y * I
theorem mk_zero_eq_mul_I (y : ℝ) : (⟨0, y⟩ : ℂ) = ↑y * I := by
  apply Complex.ext <;> simp [mul_re, mul_im, I_re, I_im]

theorem Dm_X01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 0 1) x =
    -I * ↑(p.Q ^ 2) * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) /
      (rhoBar p x) ^ 2 := by
  unfold Dm
  rw [cpd_X01_r p hx, cpd_X01_th p hx, mk_zero_eq_mul_I]
  have : (I : ℂ) ^ 2 = -1 := I_sq
  ring_nf
  simp only [I_pow_three, I_sq, neg_mul, mul_neg, neg_neg]
  push_cast; ring

/-! ### HasDerivAt for X₁₀ slices -/

theorem hasDerivAt_X10_r (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X p (Function.update x 0 u) 1 0)
      (-I * ↑(p.Q ^ 2) * (-1 / (rhoBarStar p x) ^ 2)) (x 0) := by
  have hc : HasDerivAt (fun _ : ℝ => I * (↑p.M : ℂ)) 0 (x 0) := hasDerivAt_const _ _
  have hinv := (hasDerivAt_rhoBarStar_r p x).inv (rhoBarStar_ne_zero p hx)
  refine (hc.add (hinv.const_mul (-I * ↑(p.Q ^ 2)))).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    simp only [X_10_eq, Pi.add_apply, Pi.inv_apply]; ring
  · simp only [Function.update_eq_self]; ring

theorem hasDerivAt_X10_th (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X p (Function.update x 1 u) 1 0)
      (-I * ↑(p.Q ^ 2) * (-(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) / (rhoBarStar p x) ^ 2)) (x 1) := by
  have hc : HasDerivAt (fun _ : ℝ => I * (↑p.M : ℂ)) 0 (x 1) := hasDerivAt_const _ _
  have hinv := (hasDerivAt_rhoBarStar_th p x).inv (rhoBarStar_ne_zero p hx)
  refine (hc.add (hinv.const_mul (-I * ↑(p.Q ^ 2)))).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    simp only [X_10_eq, Pi.add_apply, Pi.inv_apply]; ring
  · simp only [Function.update_eq_self]; ring

theorem cpd_X10_r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => X p z 1 0) x =
    -I * ↑(p.Q ^ 2) * (-1 / (rhoBarStar p x) ^ 2) :=
  (hasDerivAt_X10_r p x hx).deriv

theorem cpd_X10_th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => X p z 1 0) x =
    -I * ↑(p.Q ^ 2) * (-(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) / (rhoBarStar p x) ^ 2) :=
  (hasDerivAt_X10_th p x hx).deriv

theorem Dm_X10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 1 0) x =
    I * ↑(p.Q ^ 2) * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) /
      (rhoBarStar p x) ^ 2 := by
  unfold Dm
  rw [cpd_X10_r p hx, cpd_X10_th p hx, mk_zero_eq_mul_I]
  ring_nf; simp only [I_pow_three, I_sq, neg_mul, mul_neg, neg_neg]; push_cast; ring


-- ═══ From Assembly.lean ═══

/-!
# Hintz 2026 — Assembly: D₋X = AX (eq. 6)

Assembles the entry-wise Dm_Xij identities into the matrix equation
  (of fun a b => D₋ (fun z => X z a b) x) = A x * X x.
-/





/-! ### Bridge: X p z i j = Xij p z -/

theorem X_entry_00 (z : Fin 2 → ℝ) : X p z 0 0 = X00 p z := by
  rw [← X'_eq_X]; exact X'_00 p z
theorem X_entry_01 (z : Fin 2 → ℝ) : X p z 0 1 = X01 p z := by
  rw [← X'_eq_X]; exact X'_01 p z
theorem X_entry_10 (z : Fin 2 → ℝ) : X p z 1 0 = X10 p z := by
  rw [← X'_eq_X]; exact X'_10 p z
theorem X_entry_11 (z : Fin 2 → ℝ) : X p z 1 1 = X11 p z := by
  rw [← X'_eq_X]; exact X'_11 p z

/-! ### A' entry access -/

@[simp] theorem A'_00 (x : Fin 2 → ℝ) : A' p x 0 0 = 0 := by simp [A']
@[simp] theorem A'_01 (x : Fin 2 → ℝ) : A' p x 0 1 = A01 p x := by simp [A']
@[simp] theorem A'_10 (x : Fin 2 → ℝ) : A' p x 1 0 = A10 p x := by simp [A']
@[simp] theorem A'_11 (x : Fin 2 → ℝ) : A' p x 1 1 = 0 := by simp [A']

/-! ### Dm of X-entry functions (fun form) -/

theorem Dm_X_entry_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 0 0) x =
    ↑p.Q * (↑p.M * rhoBarStar p x - ↑(p.Q ^ 2)) / (rhoBar p x) ^ 2 := by
  have hX : X00 p = (fun z => X p z 0 0) := by funext z; exact (X_entry_00 p z).symm
  rw [← hX]; exact Dm_X00 p hx

theorem Dm_X_entry_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 1 1) x =
    ↑p.Q * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (rhoBarStar p x) ^ 2 := by
  have hX : X11 p = (fun z => X p z 1 1) := by funext z; exact (X_entry_11 p z).symm
  rw [← hX]; exact Dm_X11 p hx

/-! ### AX entry computations: (A x * X x) i j -/

theorem AX_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (A p x * X p x) 0 0 =
    ↑p.Q * (↑p.M * rhoBarStar p x - ↑(p.Q ^ 2)) / (rhoBar p x) ^ 2 := by
  rw [← A'_eq_A, ← X'_eq_X]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, A'_00, A'_01, A'_10, A'_11,
    X'_00, X'_01, X'_10, X'_11, A01, X10]
  field_simp [rhoBar_ne_zero p hx, rhoBarStar_ne_zero p hx]
  try simp only [I_sq]
  ring

theorem AX_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (A p x * X p x) 0 1 =
    -I * ↑(p.Q ^ 2) * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) /
      (rhoBar p x) ^ 2 := by
  rw [← A'_eq_A, ← X'_eq_X]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, A'_00, A'_01, A'_10, A'_11,
    X'_00, X'_01, X'_10, X'_11, A01, X11]
  field_simp [rhoBar_ne_zero p hx, rhoBarStar_ne_zero p hx]
  push_cast
  ring

theorem AX_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (A p x * X p x) 1 0 =
    I * ↑(p.Q ^ 2) * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) /
      (rhoBarStar p x) ^ 2 := by
  rw [← A'_eq_A, ← X'_eq_X]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, A'_00, A'_01, A'_10, A'_11,
    X'_00, X'_01, X'_10, X'_11, A10, X00]
  field_simp [rhoBar_ne_zero p hx, rhoBarStar_ne_zero p hx]
  push_cast
  ring

theorem AX_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (A p x * X p x) 1 1 =
    ↑p.Q * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (rhoBarStar p x) ^ 2 := by
  rw [← A'_eq_A, ← X'_eq_X]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, A'_00, A'_01, A'_10, A'_11,
    X'_00, X'_01, X'_10, X'_11, A10, X01]
  field_simp [rhoBar_ne_zero p hx, rhoBarStar_ne_zero p hx]
  try simp only [I_sq]
  ring


/-! ### Main equation: D₋X = AX -/

theorem Dminus_X_eq_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (of fun a b => Dm p (fun z => X p z a b) x) = A p x * X p x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [of_apply]
  · -- i=0,j=0: goal has ⟨0,⋯⟩,⟨0,⋯⟩, show converts to numeral form
    show Dm p (fun z => X p z 0 0) x = (A p x * X p x) 0 0
    rw [Dm_X_entry_00 p hx, AX_00 p hx]
  · -- i=0,j=1
    show Dm p (fun z => X p z 0 1) x = (A p x * X p x) 0 1
    rw [Dm_X01 p hx, AX_01 p hx]
  · -- i=1,j=0
    show Dm p (fun z => X p z 1 0) x = (A p x * X p x) 1 0
    rw [Dm_X10 p hx, AX_10 p hx]
  · -- i=1,j=1
    show Dm p (fun z => X p z 1 1) x = (A p x * X p x) 1 1
    rw [Dm_X_entry_11 p hx, AX_11 p hx]

/-! ### Companion equation: D₊(Xᴴ)⁻¹ = −A·(Xᴴ)⁻¹ (eq. 6, conjugate) -/


theorem adj_X_00 (x : Fin 2 → ℝ) : adjugate (X p x) 0 0 = X p x 1 1 := by
  unfold X; rw [adjugate_fin_two_of]; simp
theorem adj_X_01 (x : Fin 2 → ℝ) : adjugate (X p x) 0 1 = -(X p x 0 1) := by
  unfold X; rw [adjugate_fin_two_of]; simp
theorem adj_X_10 (x : Fin 2 → ℝ) : adjugate (X p x) 1 0 = -(X p x 1 0) := by
  unfold X; rw [adjugate_fin_two_of]; simp
theorem adj_X_11 (x : Fin 2 → ℝ) : adjugate (X p x) 1 1 = X p x 0 0 := by
  unfold X; rw [adjugate_fin_two_of]; simp
theorem Xinv_eq_smul (x : Fin 2 → ℝ) :
    (X p x)⁻¹ = (X p x).det⁻¹ • adjugate (X p x) := by
  simp [Matrix.inv_def, Ring.inverse_eq_inv]
theorem Xinv_00 (x : Fin 2 → ℝ) :
    (X p x)⁻¹ 0 0 = (X p x).det⁻¹ * X p x 1 1 := by
  simp [Xinv_eq_smul p, adj_X_00 p]
theorem Xinv_01 (x : Fin 2 → ℝ) :
    (X p x)⁻¹ 0 1 = (X p x).det⁻¹ * -(X p x 0 1) := by
  simp [Xinv_eq_smul p, adj_X_01 p]
theorem Xinv_10 (x : Fin 2 → ℝ) :
    (X p x)⁻¹ 1 0 = (X p x).det⁻¹ * -(X p x 1 0) := by
  simp [Xinv_eq_smul p, adj_X_10 p]
theorem Xinv_11 (x : Fin 2 → ℝ) :
    (X p x)⁻¹ 1 1 = (X p x).det⁻¹ * X p x 0 0 := by
  simp [Xinv_eq_smul p, adj_X_11 p]

-- ═══ Reuse: U membership / det / slice / HasDerivAt / cpd (all from blk_all_cpd) ═══
theorem mem_U_r {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    Function.update x 0 u ∈ U p :=
  ⟨by simp [Function.update]; exact hu, hx.2⟩
theorem mem_U_th {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) : Function.update x 1 u ∈ U p := by
  constructor
  · simp [Function.update, show (0 : Fin 2) ≠ 1 from by decide]; exact hx.1
  · simp [Function.update]; exact ⟨h0, h1⟩
theorem det_r_const {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    (X p (Function.update x 0 u)).det = (X p x).det := by
  rw [det_X p (mem_U_r p hx u hu), det_X p hx]
theorem det_th_const {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) :
    (X p (Function.update x 1 u)).det = (X p x).det := by
  rw [det_X p (mem_U_th p hx u h0 h1), det_X p hx]

-- Slice helpers
theorem sl00r {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    (X p (Function.update x 0 u))⁻¹ 0 0 =
      (X p x).det⁻¹ * X11 p (Function.update x 0 u) := by
  rw [Xinv_00, det_r_const p hx u hu, ← X_entry_11]
theorem sl00th {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) :
    (X p (Function.update x 1 u))⁻¹ 0 0 =
      (X p x).det⁻¹ * X11 p (Function.update x 1 u) := by
  rw [Xinv_00, det_th_const p hx u h0 h1, ← X_entry_11]
theorem sl01r {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    (X p (Function.update x 0 u))⁻¹ 0 1 =
      (X p x).det⁻¹ * -(X p (Function.update x 0 u) 0 1) := by
  rw [Xinv_01, det_r_const p hx u hu]
theorem sl01th {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) :
    (X p (Function.update x 1 u))⁻¹ 0 1 =
      (X p x).det⁻¹ * -(X p (Function.update x 1 u) 0 1) := by
  rw [Xinv_01, det_th_const p hx u h0 h1]
theorem sl10r {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    (X p (Function.update x 0 u))⁻¹ 1 0 =
      (X p x).det⁻¹ * -(X p (Function.update x 0 u) 1 0) := by
  rw [Xinv_10, det_r_const p hx u hu]
theorem sl10th {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) :
    (X p (Function.update x 1 u))⁻¹ 1 0 =
      (X p x).det⁻¹ * -(X p (Function.update x 1 u) 1 0) := by
  rw [Xinv_10, det_th_const p hx u h0 h1]
theorem sl11r {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    (X p (Function.update x 0 u))⁻¹ 1 1 =
      (X p x).det⁻¹ * X00 p (Function.update x 0 u) := by
  rw [Xinv_11, det_r_const p hx u hu, ← X_entry_00]
theorem sl11th {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) :
    (X p (Function.update x 1 u))⁻¹ 1 1 =
      (X p x).det⁻¹ * X00 p (Function.update x 1 u) := by
  rw [Xinv_11, det_th_const p hx u h0 h1, ← X_entry_00]

-- HasDerivAt (same as blk_all_cpd)
theorem hd00r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 0 u))⁻¹ 0 0)
      ((X p x).det⁻¹ * ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))) /
        (rhoBarStar p x) ^ 2)) (x 0) := by
  apply ((hasDerivAt_X11_r p x hx).const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioi_mem_nhds hx.1)
  intro u hu; dsimp only; exact sl00r p hx u (Set.mem_Ioi.mp hu)
theorem hd00th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 1 u))⁻¹ 0 0)
      ((X p x).det⁻¹ * ((-↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBarStar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) *
          (⟨0, p.a * Real.sin (x 1)⟩ : ℂ)) / (rhoBarStar p x) ^ 2)) (x 1) := by
  apply ((hasDerivAt_X11_th p x hx).const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioo_mem_nhds hx.2.1 hx.2.2)
  intro u hu; dsimp only; obtain ⟨h0, h1⟩ := Set.mem_Ioo.mp hu; exact sl00th p hx u h0 h1
theorem hd01r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 0 u))⁻¹ 0 1)
      ((X p x).det⁻¹ * -(I * ↑(p.Q ^ 2) * (-1 / (rhoBar p x) ^ 2))) (x 0) := by
  have hneg : HasDerivAt (fun u => -(X p (Function.update x 0 u) 0 1))
      (-(I * ↑(p.Q ^ 2) * (-1 / (rhoBar p x) ^ 2))) (x 0) := (hasDerivAt_X01_r p x hx).neg
  apply (hneg.const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioi_mem_nhds hx.1)
  intro u hu; dsimp only; exact sl01r p hx u (Set.mem_Ioi.mp hu)
theorem hd01th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 1 u))⁻¹ 0 1)
      ((X p x).det⁻¹ * -(I * ↑(p.Q ^ 2) * (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) /
        (rhoBar p x) ^ 2))) (x 1) := by
  have hneg : HasDerivAt (fun u => -(X p (Function.update x 1 u) 0 1))
      (-(I * ↑(p.Q ^ 2) * (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) / (rhoBar p x) ^ 2))) (x 1) :=
    (hasDerivAt_X01_th p x hx).neg
  apply (hneg.const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioo_mem_nhds hx.2.1 hx.2.2)
  intro u hu; dsimp only; obtain ⟨h0, h1⟩ := Set.mem_Ioo.mp hu; exact sl01th p hx u h0 h1
theorem hd10r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 0 u))⁻¹ 1 0)
      ((X p x).det⁻¹ * -(-I * ↑(p.Q ^ 2) * (-1 / (rhoBarStar p x) ^ 2))) (x 0) := by
  have hneg : HasDerivAt (fun u => -(X p (Function.update x 0 u) 1 0))
      (-(-I * ↑(p.Q ^ 2) * (-1 / (rhoBarStar p x) ^ 2))) (x 0) := (hasDerivAt_X10_r p x hx).neg
  apply (hneg.const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioi_mem_nhds hx.1)
  intro u hu; dsimp only; exact sl10r p hx u (Set.mem_Ioi.mp hu)
theorem hd10th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 1 u))⁻¹ 1 0)
      ((X p x).det⁻¹ * -(-I * ↑(p.Q ^ 2) * (-(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) /
        (rhoBarStar p x) ^ 2))) (x 1) := by
  have hneg : HasDerivAt (fun u => -(X p (Function.update x 1 u) 1 0))
      (-(-I * ↑(p.Q ^ 2) * (-(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) / (rhoBarStar p x) ^ 2))) (x 1) :=
    (hasDerivAt_X10_th p x hx).neg
  apply (hneg.const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioo_mem_nhds hx.2.1 hx.2.2)
  intro u hu; dsimp only; obtain ⟨h0, h1⟩ := Set.mem_Ioo.mp hu; exact sl10th p hx u h0 h1
theorem hd11r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 0 u))⁻¹ 1 1)
      ((X p x).det⁻¹ * ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1)))) /
        (rhoBar p x) ^ 2)) (x 0) := by
  apply ((hasDerivAt_X00_r p x hx).const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioi_mem_nhds hx.1)
  intro u hu; dsimp only; exact sl11r p hx u (Set.mem_Ioi.mp hu)
theorem hd11th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 1 u))⁻¹ 1 1)
      ((X p x).det⁻¹ * ((↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) *
          (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ)) / (rhoBar p x) ^ 2)) (x 1) := by
  apply ((hasDerivAt_X00_th p x hx).const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioo_mem_nhds hx.2.1 hx.2.2)
  intro u hu; dsimp only; obtain ⟨h0, h1⟩ := Set.mem_Ioo.mp hu; exact sl11th p hx u h0 h1

-- cpd extraction
theorem cpd0_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (X p z)⁻¹ 0 0) x = (X p x).det⁻¹ * ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x - ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))) / (rhoBarStar p x) ^ 2) := (hd00r p hx).deriv
theorem cpd1_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (X p z)⁻¹ 0 0) x = (X p x).det⁻¹ * ((-↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBarStar p x - ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) * (⟨0, p.a * Real.sin (x 1)⟩ : ℂ)) / (rhoBarStar p x) ^ 2) := (hd00th p hx).deriv
theorem cpd0_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (X p z)⁻¹ 0 1) x = (X p x).det⁻¹ * -(I * ↑(p.Q ^ 2) * (-1 / (rhoBar p x) ^ 2)) := (hd01r p hx).deriv
theorem cpd1_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (X p z)⁻¹ 0 1) x = (X p x).det⁻¹ * -(I * ↑(p.Q ^ 2) * (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) / (rhoBar p x) ^ 2)) := (hd01th p hx).deriv
theorem cpd0_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (X p z)⁻¹ 1 0) x = (X p x).det⁻¹ * -(-I * ↑(p.Q ^ 2) * (-1 / (rhoBarStar p x) ^ 2)) := (hd10r p hx).deriv
theorem cpd1_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (X p z)⁻¹ 1 0) x = (X p x).det⁻¹ * -(-I * ↑(p.Q ^ 2) * (-(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) / (rhoBarStar p x) ^ 2)) := (hd10th p hx).deriv
theorem cpd0_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (X p z)⁻¹ 1 1) x = (X p x).det⁻¹ * ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x - ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1)))) / (rhoBar p x) ^ 2) := (hd11r p hx).deriv
theorem cpd1_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (X p z)⁻¹ 1 1) x = (X p x).det⁻¹ * ((↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBar p x - ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) * (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ)) / (rhoBar p x) ^ 2) := (hd11th p hx).deriv

/-! ═══ Dm factoring: Dm(X⁻¹_{ij}) = ±det⁻¹ * Dm(X_{kl}) ═══ -/

-- Dm(X⁻¹)₀₀ = det⁻¹ * Dm(X11)
theorem Dm_fac_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 0 0) x = (X p x).det⁻¹ * Dm p (X11 p) x := by
  simp only [Dm, cpd0_00 p hx, cpd1_00 p hx, cpd_X11_r' p hx, cpd_X11_th' p hx]; ring

-- Dm(X⁻¹)₀₁ = -det⁻¹ * Dm(fun z => X p z 0 1)
theorem Dm_fac_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 0 1) x = -(X p x).det⁻¹ * Dm p (fun z => X p z 0 1) x := by
  simp only [Dm, cpd0_01 p hx, cpd1_01 p hx, cpd_X01_r p hx, cpd_X01_th p hx]; ring

-- Dm(X⁻¹)₁₀ = -det⁻¹ * Dm(fun z => X p z 1 0)
theorem Dm_fac_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 1 0) x = -(X p x).det⁻¹ * Dm p (fun z => X p z 1 0) x := by
  simp only [Dm, cpd0_10 p hx, cpd1_10 p hx, cpd_X10_r p hx, cpd_X10_th p hx]; ring

-- Dm(X⁻¹)₁₁ = det⁻¹ * Dm(X00)
theorem Dm_fac_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 1 1) x = (X p x).det⁻¹ * Dm p (X00 p) x := by
  simp only [Dm, cpd0_11 p hx, cpd1_11 p hx, cpd_X00_r' p hx, cpd_X00_th' p hx]; ring

/-! ═══ Dm(X entries) = (AX) entries ═══ -/

theorem dm_X11_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (X11 p) x = (A p x * X p x) 1 1 := by
  have := congr_fun (congr_fun (Dminus_X_eq_AX p hx) 1) 1
  simp only [of_apply, ← X_entry_11] at this; exact this

theorem dm_X01_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 0 1) x = (A p x * X p x) 0 1 := by
  have := congr_fun (congr_fun (Dminus_X_eq_AX p hx) 0) 1
  simp only [of_apply] at this; exact this

theorem dm_X10_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 1 0) x = (A p x * X p x) 1 0 := by
  have := congr_fun (congr_fun (Dminus_X_eq_AX p hx) 1) 0
  simp only [of_apply] at this; exact this

theorem dm_X00_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (X00 p) x = (A p x * X p x) 0 0 := by
  have := congr_fun (congr_fun (Dminus_X_eq_AX p hx) 0) 0
  simp only [of_apply, ← X_entry_00] at this; exact this

/-! ═══ Algebraic: -(X⁻¹*A)_{ij} = det⁻¹ * (±(AX)_{kl}) ═══ -/

theorem neg_XinvA_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    -((X p x)⁻¹ * A p x) 0 0 = (X p x).det⁻¹ * (A p x * X p x) 1 1 := by
  have hL : ((X p x)⁻¹ * A p x) 0 0 =
      (X p x).det⁻¹ * X p x 1 1 * A p x 0 0 + (X p x).det⁻¹ * -(X p x 0 1) * A p x 1 0 := by
    rw [mul_apply, Fin.sum_univ_two, Xinv_00, Xinv_01]
  have hR : (A p x * X p x) 1 1 = A p x 1 0 * X p x 0 1 + A p x 1 1 * X p x 1 1 := by
    rw [mul_apply, Fin.sum_univ_two]
  have hA00 : A p x 0 0 = 0 := by rw [← A'_eq_A p, A'_00]
  have hA11 : A p x 1 1 = 0 := by rw [← A'_eq_A p, A'_11]
  rw [hL, hA00, hR, hA11]; ring

theorem neg_XinvA_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    -((X p x)⁻¹ * A p x) 0 1 = -(X p x).det⁻¹ * (A p x * X p x) 0 1 := by
  have hL : ((X p x)⁻¹ * A p x) 0 1 =
      (X p x).det⁻¹ * X p x 1 1 * A p x 0 1 + (X p x).det⁻¹ * -(X p x 0 1) * A p x 1 1 := by
    rw [mul_apply, Fin.sum_univ_two, Xinv_00, Xinv_01]
  have hR : (A p x * X p x) 0 1 = A p x 0 0 * X p x 0 1 + A p x 0 1 * X p x 1 1 := by
    rw [mul_apply, Fin.sum_univ_two]
  have hA00 : A p x 0 0 = 0 := by rw [← A'_eq_A p, A'_00]
  have hA11 : A p x 1 1 = 0 := by rw [← A'_eq_A p, A'_11]
  rw [hL, hA11, hR, hA00]; ring

theorem neg_XinvA_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    -((X p x)⁻¹ * A p x) 1 0 = -(X p x).det⁻¹ * (A p x * X p x) 1 0 := by
  have hL : ((X p x)⁻¹ * A p x) 1 0 =
      (X p x).det⁻¹ * -(X p x 1 0) * A p x 0 0 + (X p x).det⁻¹ * X p x 0 0 * A p x 1 0 := by
    rw [mul_apply, Fin.sum_univ_two, Xinv_10, Xinv_11]
  have hR : (A p x * X p x) 1 0 = A p x 1 0 * X p x 0 0 + A p x 1 1 * X p x 1 0 := by
    rw [mul_apply, Fin.sum_univ_two]
  have hA00 : A p x 0 0 = 0 := by rw [← A'_eq_A p, A'_00]
  have hA11 : A p x 1 1 = 0 := by rw [← A'_eq_A p, A'_11]
  rw [hL, hA00, hR, hA11]; ring

theorem neg_XinvA_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    -((X p x)⁻¹ * A p x) 1 1 = (X p x).det⁻¹ * (A p x * X p x) 0 0 := by
  have hL : ((X p x)⁻¹ * A p x) 1 1 =
      (X p x).det⁻¹ * -(X p x 1 0) * A p x 0 1 + (X p x).det⁻¹ * X p x 0 0 * A p x 1 1 := by
    rw [mul_apply, Fin.sum_univ_two, Xinv_10, Xinv_11]
  have hR : (A p x * X p x) 0 0 = A p x 0 0 * X p x 0 0 + A p x 0 1 * X p x 1 0 := by
    rw [mul_apply, Fin.sum_univ_two]
  have hA00 : A p x 0 0 = 0 := by rw [← A'_eq_A p, A'_00]
  have hA11 : A p x 1 1 = 0 := by rw [← A'_eq_A p, A'_11]
  rw [hL, hA11, hR, hA00]; ring

/-! ═══ Chain: Dm(X⁻¹)_{ij} = -(X⁻¹*A)_{ij} ═══ -/

theorem Dm_Xinv_neg_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 0 0) x = -((X p x)⁻¹ * A p x) 0 0 := by
  rw [Dm_fac_00 p hx, dm_X11_AX p hx, neg_XinvA_00 p hx]

theorem Dm_Xinv_neg_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 0 1) x = -((X p x)⁻¹ * A p x) 0 1 := by
  rw [Dm_fac_01 p hx, dm_X01_AX p hx, neg_XinvA_01 p hx]

theorem Dm_Xinv_neg_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 1 0) x = -((X p x)⁻¹ * A p x) 1 0 := by
  rw [Dm_fac_10 p hx, dm_X10_AX p hx, neg_XinvA_10 p hx]

theorem Dm_Xinv_neg_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 1 1) x = -((X p x)⁻¹ * A p x) 1 1 := by
  rw [Dm_fac_11 p hx, dm_X00_AX p hx, neg_XinvA_11 p hx]

/-! ═══ Matrix assembly: Dm(X⁻¹) = -(X⁻¹*A) ═══ -/

theorem Dm_Xinv_matrix {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (of fun a b => Dm p (fun z => (X p z)⁻¹ a b) x) = -(X p x)⁻¹ * A p x := by
  ext i j; simp only [of_apply, neg_mul, Matrix.neg_apply]
  fin_cases i <;> fin_cases j
  · exact Dm_Xinv_neg_00 p hx
  · exact Dm_Xinv_neg_01 p hx
  · exact Dm_Xinv_neg_10 p hx
  · exact Dm_Xinv_neg_11 p hx

/-! ═══ D₊ / star helpers ═══ -/

theorem cpd_star_eq (i : Fin 2) (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    cpd i (fun z => star (f z)) x = star (cpd i f x) := deriv.star

theorem Dp_eq_star_Dm_star (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    Dp p f x = star (Dm p (fun z => star (f z)) x) := by
  unfold Dp Dm
  rw [cpd_star_eq, cpd_star_eq]
  have hI : star (I : ℂ) = -I := by rw [star_def]; exact conj_I
  have hR : star (↑(Real.sqrt (Del p (x 0))) : ℂ) = ↑(Real.sqrt (Del p (x 0))) := by
    rw [star_def]; exact conj_ofReal _
  rw [star_sub, star_mul, star_mul, star_star, star_star, hI, hR]; ring

theorem Dp_Xstarinv_entry {x : Fin 2 → ℝ} (hx : x ∈ U p) (i j : Fin 2) :
    Dp p (fun z => ((X p z)ᴴ)⁻¹ i j) x = star (Dm p (fun z => (X p z)⁻¹ j i) x) := by
  have key : ∀ z, ((X p z)ᴴ)⁻¹ i j = star ((X p z)⁻¹ j i) := fun z => by
    rw [← conjTranspose_nonsing_inv, conjTranspose_apply]
  simp_rw [key, Dp_eq_star_Dm_star]; simp [star_star]

/-! ═══ Main theorem ═══ -/

theorem Dplus_XstarInv_eq' {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (of fun a b => Dp p (fun z => ((X p z)ᴴ)⁻¹ a b) x) = -A p x * ((X p x)ᴴ)⁻¹ := by
  ext i j
  simp only [of_apply, Dp_Xstarinv_entry p hx]
  have hDm : Dm p (fun z => (X p z)⁻¹ j i) x = -((X p x)⁻¹ * A p x) j i := by
    have h := congr_fun (congr_fun (Dm_Xinv_matrix p hx) j) i
    simp only [of_apply, neg_mul, Matrix.neg_apply] at h; exact h
  rw [hDm, star_neg]
  simp only [neg_mul, Matrix.neg_apply]
  congr 1
  have hmat : A p x * (X p x)ᴴ⁻¹ = ((X p x)⁻¹ * A p x)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, A_conjTranspose p hx]
  rw [hmat, conjTranspose_apply]

theorem Dplus_XstarInv_eq {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (of fun a b => Dp p (fun z => ((X p z)ᴴ)⁻¹ a b) x) =
    -A p x * ((X p x)ᴴ)⁻¹ := by
  ext i j
  simp only [of_apply, Dp_Xstarinv_entry p hx]
  have hDm : Dm p (fun z => (X p z)⁻¹ j i) x = -((X p x)⁻¹ * A p x) j i := by
    have h := congr_fun (congr_fun (Dm_Xinv_matrix p hx) j) i
    simp only [of_apply, neg_mul, Matrix.neg_apply] at h; exact h
  rw [hDm, star_neg]
  simp only [neg_mul, Matrix.neg_apply]
  congr 1
  have hmat : A p x * (X p x)ᴴ⁻¹ = ((X p x)⁻¹ * A p x)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, A_conjTranspose p hx]
  rw [hmat, conjTranspose_apply]



end Hintz2026

end


