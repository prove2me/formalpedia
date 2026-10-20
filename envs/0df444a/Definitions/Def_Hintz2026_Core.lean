-- Prove2me | Definitions.Def_Hintz2026_Core
-- name    : Hintz2026_Core
-- status  : Definition
-- author  : @He Wang
-- created : 2026-10-19T13:16:15.681024+00:00
-- url     : https://prove2.me/theorems/7bbb36f9-2430-4232-b0bf-6cbcb8911a81
-- title:
--   Hintz2026 — Integrating factor X, connection A, operators D±
-- statement:
--   Defines the $2\times 2$ complex matrix integrating factor $X(r,\theta) = \begin{pmatrix} Q(\sqrt{\Delta}+a\sin\theta)/\bar{\rho} & -i(M - Q^2/\bar{\rho}) \\ i(M - Q^2/\bar{\rho}^*) & Q(\sqrt{\Delta}-a\sin\theta)/\bar{\rho}^* \end{pmatrix}$ from Hintz eq. (5), the coefficient matrix $A = \begin{pmatrix} 0 & -iQ\bar{\rho}^*/\bar{\rho}^2 \\ iQ\bar{\rho}/\bar{\rho}^{*2} & 0 \end{pmatrix}$ from eq. (4), and the first-order operators $D^- f = \sqrt{\Delta}\,\partial_r f-i\,\partial_\theta f,\quad D^+ f = \sqrt{\Delta}\,\partial_r f+i\,\partial_\theta f$ as coordinate-slice derivatives. Proves $\det X = Q^2 - M^2$ (constant), invertibility of $X$ and $X^*$, and $A^* = A$. Also provides slice derivatives of $\bar{\rho}$, $\bar{\rho}^*$, $\sqrt{\Delta}$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6)

import Definitions.Def_Hintz2026_Domain

/-!
# Hintz 2026 — Core definitions and building blocks

Integrating factor X, connection A, operators D±, entry decompositions,
slice derivatives of ρ̄/ρ̄*, and basic Dm/Dp rules.
-/

open Complex Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

-- ═══ From IntegratingFactor.lean ═══

/-!
# Hintz 2026 — Matrix integrating factor X and connection A

Source: Hintz, arXiv:2609.33661v1, equations (4)–(6).
-/





def X (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) / rhoBar p x,
     -I * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x);
     I * (↑p.M - ↑(p.Q ^ 2) / rhoBarStar p x),
     ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) / rhoBarStar p x]

def A (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I * ↑p.Q * rhoBarStar p x / rhoBar p x ^ 2;
     I * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2, 0]

def XN (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))),
     -I * (↑p.M * rhoBar p x - ↑(p.Q ^ 2));
     I * (↑p.M * rhoBarStar p x - ↑(p.Q ^ 2)),
     ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))]

/-! ### Conjugation helpers -/

theorem conj_rhoBar_eq (x : Fin 2 → ℝ) :
    conj (rhoBar p x) = rhoBarStar p x := (rhoBarStar_eq_conj p x).symm

theorem conj_rhoBarStar_eq (x : Fin 2 → ℝ) :
    conj (rhoBarStar p x) = rhoBar p x := by
  rw [rhoBarStar_eq_conj, starRingEnd_self_apply]

/-! ### det X · ρ·ρ* = det XN -/

theorem det_X_mul_eq_det_XN {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (X p x).det * (rhoBar p x * rhoBarStar p x) = (XN p x).det := by
  simp only [X, XN, det_fin_two_of]
  field_simp [rhoBar_ne_zero p hx, rhoBarStar_ne_zero p hx]

/-! ### det XN = (Q²-M²)·ρ·ρ* -/

theorem det_XN (x : Fin 2 → ℝ) (hDel : 0 < Del p (x 0)) :
    (XN p x).det = ↑(p.Q ^ 2 - p.M ^ 2) * (rhoBar p x * rhoBarStar p x) := by
  simp only [XN, det_fin_two_of, rhoBar, rhoBarStar]
  set r := x 0; set c := Real.cos (x 1); set sn := Real.sin (x 1)
  set ac := p.a * c; set sqD := Real.sqrt (Del p r)
  have hsq : sqD ^ 2 = r ^ 2 - 2 * p.M * r + p.a ^ 2 + p.Q ^ 2 :=
    (Real.sq_sqrt (le_of_lt hDel)).trans rfl
  have htrig : sn ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · linear_combination p.Q ^ 2 * hsq - p.Q ^ 2 * p.a ^ 2 * htrig
  · linear_combination (0 : ℝ)

/-! ### det X = Q² - M² -/

theorem det_X {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (X p x).det = ↑(p.Q ^ 2 - p.M ^ 2) :=
  mul_right_cancel₀ (mul_ne_zero (rhoBar_ne_zero p hx) (rhoBarStar_ne_zero p hx))
    ((det_X_mul_eq_det_XN p hx).trans (det_XN p x (Del_pos p hx.1)))

theorem X_det_isUnit {x : Fin 2 → ℝ} (hx : x ∈ U p) : IsUnit (X p x).det := by
  rw [det_X p hx, isUnit_iff_ne_zero]; exact_mod_cast Q_sq_sub_M_sq_ne_zero p

/-! ### Hermitian A -/

theorem A_conjTranspose {x : Fin 2 → ℝ} (_hx : x ∈ U p) :
    (A p x)ᴴ = A p x := by
  ext i j; simp only [conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [A, star_def, conj_rhoBar_eq p, conj_rhoBarStar_eq p]

/-! ### Invertibility -/

theorem X_mul_inv {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    X p x * (X p x)⁻¹ = 1 := mul_nonsing_inv _ (X_det_isUnit p hx)

theorem inv_mul_X {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (X p x)⁻¹ * X p x = 1 := nonsing_inv_mul _ (X_det_isUnit p hx)

theorem Xstar_det_isUnit {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    IsUnit (X p x)ᴴ.det := by
  rw [det_conjTranspose]; exact IsUnit.map (starRingEnd ℂ) (X_det_isUnit p hx)

theorem Xstar_mul_inv {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (X p x)ᴴ * ((X p x)ᴴ)⁻¹ = 1 := mul_nonsing_inv _ (Xstar_det_isUnit p hx)

theorem inv_mul_Xstar {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    ((X p x)ᴴ)⁻¹ * (X p x)ᴴ = 1 := nonsing_inv_mul _ (Xstar_det_isUnit p hx)


-- ═══ From Derivatives.lean ═══

/-!
# Hintz 2026 — Slice derivatives of building blocks
-/





/-! ### ∂_r Δ and ∂_r √Δ -/

theorem hasDerivAt_Del_r (r : ℝ) :
    HasDerivAt (Del p) (2 * r - 2 * p.M) r := by
  have : Del p = fun r => r ^ 2 + (-2 * p.M) * r + (p.a ^ 2 + p.Q ^ 2) := by
    ext r; unfold Del; ring
  rw [this]
  exact ((hasDerivAt_pow 2 r).add ((hasDerivAt_id r).const_mul _)).add
    (hasDerivAt_const _ _) |>.congr_deriv (by ring)

theorem hasDerivAt_sqrtDel_r {r : ℝ} (hD : 0 < Del p r) :
    HasDerivAt (fun r => Real.sqrt (Del p r))
      ((r - p.M) / Real.sqrt (Del p r)) r :=
  ((Real.hasDerivAt_sqrt (ne_of_gt hD)).comp r (hasDerivAt_Del_r p r)).congr_deriv
    (by field_simp)

/-! ### Key helper: HasDerivAt for ℂ.mk from real components -/

/-- If `f, g : ℝ → ℝ` have derivatives `f', g'` at `x`, then
`u ↦ ⟨f u, g u⟩ : ℝ → ℂ` has derivative `⟨f', g'⟩` at `x`. -/
theorem hasDerivAt_complex_mk {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun u => (⟨f u, g u⟩ : ℂ)) ⟨f', g'⟩ x := by
  -- ↑(f u) has derivative ↑f'
  have hfc : HasDerivAt (fun u => (↑(f u) : ℂ)) (↑f') x :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hf
  -- ↑(g u) has derivative ↑g'
  have hgc : HasDerivAt (fun u => (↑(g u) : ℂ)) (↑g') x :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hg
  -- ↑(g u) * I has derivative ↑g' * I
  have hgI : HasDerivAt (fun u => (↑(g u) : ℂ) * I) (↑g' * I) x := hgc.mul_const I
  -- Sum
  have hsum := hfc.add hgI
  -- ↑(f u) + ↑(g u) * I = ⟨f u, g u⟩
  refine hsum.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    apply Complex.ext <;> simp [mul_re, mul_im, I_re, I_im]
  · apply Complex.ext <;> simp [mul_re, mul_im, I_re, I_im]

/-! ### ρ̄ derivatives -/

-- ∂_r ρ̄ = 1
theorem hasDerivAt_rhoBar_r (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => rhoBar p (Function.update x 0 u)) 1 (x 0) := by
  have h := hasDerivAt_complex_mk (hasDerivAt_id (x 0))
    (hasDerivAt_const (x 0) (p.a * Real.cos (x 1)))
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    unfold rhoBar; congr 1 <;> simp [show (0 : Fin 2) ≠ 1 from by decide]
  · apply Complex.ext <;> simp

-- ∂_r ρ̄* = 1
theorem hasDerivAt_rhoBarStar_r (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => rhoBarStar p (Function.update x 0 u)) 1 (x 0) := by
  have h := hasDerivAt_complex_mk (hasDerivAt_id (x 0))
    (hasDerivAt_const (x 0) (-(p.a * Real.cos (x 1))))
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    unfold rhoBarStar; congr 1 <;> simp [show (0 : Fin 2) ≠ 1 from by decide]
  · apply Complex.ext <;> simp

-- ∂_θ ρ̄ = ⟨0, -a sinθ⟩
theorem hasDerivAt_rhoBar_th (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => rhoBar p (Function.update x 1 u))
      (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) (x 1) := by
  have hcos : HasDerivAt (fun u => p.a * Real.cos u) (-(p.a * Real.sin (x 1))) (x 1) :=
    ((Real.hasDerivAt_cos (x 1)).const_mul p.a).congr_deriv (by ring)
  have h := hasDerivAt_complex_mk (hasDerivAt_const (x 1) (x 0)) hcos
  refine h.congr_of_eventuallyEq ?_
  · filter_upwards with u
    unfold rhoBar; congr 1 <;> simp [show (1 : Fin 2) ≠ 0 from by decide]

-- ∂_θ ρ̄* = ⟨0, a sinθ⟩
theorem hasDerivAt_rhoBarStar_th (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => rhoBarStar p (Function.update x 1 u))
      (⟨0, p.a * Real.sin (x 1)⟩ : ℂ) (x 1) := by
  have hcos : HasDerivAt (fun u => -(p.a * Real.cos u)) (p.a * Real.sin (x 1)) (x 1) :=
    (((Real.hasDerivAt_cos (x 1)).const_mul p.a).neg).congr_deriv (by ring)
  have h := hasDerivAt_complex_mk (hasDerivAt_const (x 1) (x 0)) hcos
  refine h.congr_of_eventuallyEq ?_
  · filter_upwards with u
    unfold rhoBarStar; congr 1 <;> simp [show (1 : Fin 2) ≠ 0 from by decide]


-- ═══ From XEntries.lean ═══

/-!
# Hintz 2026 — Individual X and A matrix entries

Standalone definitions for each entry of X(r,θ) and A(r,θ),
avoiding the !![] elaboration bottleneck.
-/





/-! ### X entries (Hintz eq. 5) -/

def X00 (x : Fin 2 → ℝ) : ℂ :=
  ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) / rhoBar p x

def X01 (x : Fin 2 → ℝ) : ℂ :=
  -I * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x)

def X10 (x : Fin 2 → ℝ) : ℂ :=
  I * (↑p.M - ↑(p.Q ^ 2) / rhoBarStar p x)

def X11 (x : Fin 2 → ℝ) : ℂ :=
  ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) / rhoBarStar p x

/-! ### A entries (Hintz eq. 4) -/

def A01 (x : Fin 2 → ℝ) : ℂ :=
  -I * ↑p.Q * rhoBarStar p x / rhoBar p x ^ 2

def A10 (x : Fin 2 → ℝ) : ℂ :=
  I * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2

/-! ### X and A as matrices, built from entries -/

def X' (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![X00 p x, X01 p x; X10 p x, X11 p x]

def A' (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, A01 p x; A10 p x, 0]

/-! ### X' = X, A' = A -/

theorem X'_eq_X (x : Fin 2 → ℝ) : X' p x = X p x := by
  simp [X', X, X00, X01, X10, X11]

theorem A'_eq_A (x : Fin 2 → ℝ) : A' p x = A p x := by
  simp [A', A, A01, A10]

/-! ### Entry access from X' is definitional -/

@[simp] theorem X'_00 (x : Fin 2 → ℝ) : X' p x 0 0 = X00 p x := by simp [X']
@[simp] theorem X'_01 (x : Fin 2 → ℝ) : X' p x 0 1 = X01 p x := by simp [X']
@[simp] theorem X'_10 (x : Fin 2 → ℝ) : X' p x 1 0 = X10 p x := by simp [X']
@[simp] theorem X'_11 (x : Fin 2 → ℝ) : X' p x 1 1 = X11 p x := by simp [X']

/-! ### Slice functions for X entries are lightweight -/

-- X₀₀ along r: only √Δ and ρ̄ depend on r
theorem X00_r_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X00 p (Function.update x 0 u) =
    ↑p.Q * (↑(Real.sqrt (Del p u)) + ↑p.a * ↑(Real.sin (x 1))) /
      rhoBar p (Function.update x 0 u) := by
  simp [X00]

-- X₀₀ along θ: only sinθ and ρ̄ depend on θ
theorem X00_th_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X00 p (Function.update x 1 u) =
    ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin u)) /
      rhoBar p (Function.update x 1 u) := by
  simp [X00]

-- X₁₁ along r
theorem X11_r_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X11 p (Function.update x 0 u) =
    ↑p.Q * (↑(Real.sqrt (Del p u)) - ↑p.a * ↑(Real.sin (x 1))) /
      rhoBarStar p (Function.update x 0 u) := by
  simp [X11]

-- X₁₁ along θ
theorem X11_th_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X11 p (Function.update x 1 u) =
    ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin u)) /
      rhoBarStar p (Function.update x 1 u) := by
  simp [X11]

-- X₀₁ along r
theorem X01_r_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X01 p (Function.update x 0 u) =
    -I * ↑p.M + I * ↑(p.Q ^ 2) * (rhoBar p (Function.update x 0 u))⁻¹ := by
  simp [X01]; ring

-- X₀₁ along θ
theorem X01_th_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X01 p (Function.update x 1 u) =
    -I * ↑p.M + I * ↑(p.Q ^ 2) * (rhoBar p (Function.update x 1 u))⁻¹ := by
  simp [X01]; ring

-- X₁₀ along r
theorem X10_r_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X10 p (Function.update x 0 u) =
    I * ↑p.M - I * ↑(p.Q ^ 2) * (rhoBarStar p (Function.update x 0 u))⁻¹ := by
  simp [X10]; ring

-- X₁₀ along θ
theorem X10_th_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X10 p (Function.update x 1 u) =
    I * ↑p.M - I * ↑(p.Q ^ 2) * (rhoBarStar p (Function.update x 1 u))⁻¹ := by
  simp [X10]; ring


-- ═══ From Eq6.lean ═══

/-!
# Hintz 2026 — Integrating factor equations (eq. 6)
-/





def cpd (i : Fin 2) (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  deriv (fun u => f (Function.update x i u)) (x i)

def Dm (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  ↑(Real.sqrt (Del p (x 0))) * cpd 0 f x - I * cpd 1 f x

def Dp (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  ↑(Real.sqrt (Del p (x 0))) * cpd 0 f x + I * cpd 1 f x

/-! ### cpd of ρ̄, ρ̄* -/

theorem cpd_rhoBar_r (x : Fin 2 → ℝ) : cpd 0 (rhoBar p) x = 1 :=
  (hasDerivAt_rhoBar_r p x).deriv

theorem cpd_rhoBar_th (x : Fin 2 → ℝ) :
    cpd 1 (rhoBar p) x = ⟨0, -(p.a * Real.sin (x 1))⟩ :=
  (hasDerivAt_rhoBar_th p x).deriv

theorem cpd_rhoBarStar_r (x : Fin 2 → ℝ) : cpd 0 (rhoBarStar p) x = 1 :=
  (hasDerivAt_rhoBarStar_r p x).deriv

theorem cpd_rhoBarStar_th (x : Fin 2 → ℝ) :
    cpd 1 (rhoBarStar p) x = ⟨0, p.a * Real.sin (x 1)⟩ :=
  (hasDerivAt_rhoBarStar_th p x).deriv

/-! ### D₋ ρ̄, D₋ ρ̄*

D₋ ρ̄ = √Δ · 1 - I · ⟨0, -a sinθ⟩ = √Δ - ⟨a sinθ, 0⟩ = ↑(√Δ - a sinθ)
D₋ ρ̄* = √Δ · 1 - I · ⟨0, a sinθ⟩ = √Δ + ⟨a sinθ, 0⟩ = ↑(√Δ + a sinθ)
-/

theorem I_mul_mk_zero_left (y : ℝ) : I * (⟨0, y⟩ : ℂ) = ↑(-y) := by
  apply Complex.ext
  · simp [mul_re, I_re, I_im]
  · simp [mul_im, I_re, I_im]

theorem Dm_rhoBar (x : Fin 2 → ℝ) :
    Dm p (rhoBar p) x = ↑(Real.sqrt (Del p (x 0)) - p.a * Real.sin (x 1)) := by
  unfold Dm; rw [cpd_rhoBar_r, cpd_rhoBar_th, I_mul_mk_zero_left]; push_cast; ring

theorem Dm_rhoBarStar (x : Fin 2 → ℝ) :
    Dm p (rhoBarStar p) x = ↑(Real.sqrt (Del p (x 0)) + p.a * Real.sin (x 1)) := by
  unfold Dm; rw [cpd_rhoBarStar_r, cpd_rhoBarStar_th, I_mul_mk_zero_left]; push_cast; ring

/-! ### cpd of 1/ρ̄, 1/ρ̄* -/

-- Use exact h.deriv (definitional equality handles the beta-reduction)
theorem cpd_inv_rhoBar_r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun x => (rhoBar p x)⁻¹) x =
    -1 / (rhoBar p x) ^ 2 := by
  exact ((hasDerivAt_rhoBar_r p x).inv (rhoBar_ne_zero p hx)).deriv

theorem cpd_inv_rhoBar_th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun x => (rhoBar p x)⁻¹) x =
    -(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) / (rhoBar p x) ^ 2 := by
  exact ((hasDerivAt_rhoBar_th p x).inv (rhoBar_ne_zero p hx)).deriv

theorem cpd_inv_rhoBarStar_r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun x => (rhoBarStar p x)⁻¹) x =
    -1 / (rhoBarStar p x) ^ 2 := by
  exact ((hasDerivAt_rhoBarStar_r p x).inv (rhoBarStar_ne_zero p hx)).deriv

theorem cpd_inv_rhoBarStar_th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun x => (rhoBarStar p x)⁻¹) x =
    -(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) / (rhoBarStar p x) ^ 2 := by
  exact ((hasDerivAt_rhoBarStar_th p x).inv (rhoBarStar_ne_zero p hx)).deriv




end Hintz2026

end


