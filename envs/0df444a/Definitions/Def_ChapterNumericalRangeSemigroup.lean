-- Prove2me | Definitions.Def_ChapterNumericalRangeSemigroup
-- name    : ChapterNumericalRangeSemigroup
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:35:11.650248+00:00
-- url     : https://prove2.me/theorems/36e8315f-c7bd-4b41-b9b7-2ff2f69f7d4a
-- title:
--   Chapter NumericalRangeSemigroup
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNumericalRangeSemigroup.lean`): generated def bundle for ChapterNumericalRangeSemigroup. See BookProof/ChapterNumericalRangeSemigroup.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNumericalRangeSemigroup.lean

import Definitions.Def_ChapterH9
import Mathlib


/-!
# Crouzeix's inequality on a half-plane: the exponential of an operator whose numerical
range has bounded real part

`BookProof.ChapterCrouzeixSelfAdjoint` proves Crouzeix's inequality with constant `1` for
*normal* operators, and `BookProof.ChapterNumericalRangeCrouzeix` proves a Crouzeix-type
inequality for a general non-normal operator whose numerical range lies in a **disc**, with
an explicit (larger) constant.  The general theorem — an arbitrary convex spectral set
containing the numerical range — is still open here.  This file settles another convex
domain, the **half-plane**, for the functions the project actually applies to a generator,
namely the exponentials `f_t(z) = e^{t z}`, and with the optimal constant `1`.

## Results

* `NumReLE A ω` — the numerical range of `A` lies in the half-plane `{Re z ≤ ω}`, written as
  the form inequality `Re ⟪x, A x⟫ ≤ ω ‖x‖²`; `numReLE_iff_numRange_subset` identifies the
  two formulations.
* `hasDerivAt_expApply` — `t ↦ e^{tA} x` is differentiable with derivative `A e^{tA} x`, and
  `hasDerivAt_normSq` — the derivative of `t ↦ ‖e^{tA}x‖²` is `2 Re ⟪e^{tA}x, A e^{tA}x⟫`.
* **`norm_exp_apply_le`** and **`norm_exp_le`** — if `Re ⟪x, A x⟫ ≤ ω ‖x‖²` for all `x`, then
  for every `t ≥ 0` one has `‖e^{tA} x‖ ≤ e^{ωt} ‖x‖`, hence `‖e^{tA}‖ ≤ e^{ωt}`.  The proof
  is the differential inequality: `t ↦ ‖e^{tA}x‖² e^{-2ωt}` has nonpositive derivative.
* `norm_exp_le_one` — the contraction case `ω = 0`: an operator whose numerical range lies in
  the closed left half-plane generates a **contraction semigroup**.
* `norm_cexp_le_of_re_le` — on the half-plane `{Re z ≤ ω}` the supremum of `|e^{tz}|` is
  exactly `e^{ωt}`, so `norm_exp_le` *is* Crouzeix's inequality for these functions and this
  convex domain, with constant `1`.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace

namespace BookProof.ChapterNumericalRangeSemigroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## The numerical range in a half-plane -/

/-- The numerical range of `A` lies in the half-plane `{Re z ≤ ω}`. -/
def NumReLE (A : E →L[ℂ] E) (ω : ℝ) : Prop :=
  ∀ x : E, (inner ℂ x (A x) : ℂ).re ≤ ω * ‖x‖ ^ 2



/-! ## Differentiating the exponential -/





/-! ## The growth bound -/









/-! ## The resolvent bound -/

omit [CompleteSpace E] in
/-- A form lower bound `Re ⟪x, S x⟫ ≥ c‖x‖²` bounds `S` below: `c‖x‖ ≤ ‖S x‖`. -/
theorem norm_ge_of_re_inner_ge {S : E →L[ℂ] E} {c : ℝ}
    (h : ∀ x : E, c * ‖x‖ ^ 2 ≤ (inner ℂ x (S x) : ℂ).re) (x : E) : c * ‖x‖ ≤ ‖S x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 : c * ‖x‖ ^ 2 ≤ ‖x‖ * ‖S x‖ := le_trans (h x) (by
      simpa using re_inner_le_norm (𝕜 := ℂ) x (S x))
    nlinarith [h1, hpos]

omit [CompleteSpace E] in
/-- Shifting by `z` moves the form bound: `Re ⟪x, (z - A) x⟫ ≥ (Re z - ω)‖x‖²`. -/
theorem re_inner_shift {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) (z : ℂ) (x : E) :
    (z.re - ω) * ‖x‖ ^ 2 ≤ (inner ℂ x ((z • (1 : E →L[ℂ] E) - A) x) : ℂ).re := by
  have hinner : (inner ℂ x ((z • (1 : E →L[ℂ] E) - A) x) : ℂ)
      = z * (inner ℂ x x : ℂ) - (inner ℂ x (A x) : ℂ) := by
    simp
  have hxx : (inner ℂ x x : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    simp [← Complex.ofReal_pow]
  rw [hinner, hxx]
  have hre : (z * ((‖x‖ ^ 2 : ℝ) : ℂ) - (inner ℂ x (A x) : ℂ)).re
      = z.re * ‖x‖ ^ 2 - (inner ℂ x (A x) : ℂ).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  rw [hre]
  have := h x
  linarith

/-- The same bound for the adjoint, because the real part of the form is conjugation
invariant. -/
theorem re_inner_shift_adjoint {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) (z : ℂ) (x : E) :
    (z.re - ω) * ‖x‖ ^ 2
      ≤ (inner ℂ x (ContinuousLinearMap.adjoint (z • (1 : E →L[ℂ] E) - A) x) : ℂ).re := by
  have hadj : (inner ℂ x (ContinuousLinearMap.adjoint (z • (1 : E →L[ℂ] E) - A) x) : ℂ)
      = (inner ℂ ((z • (1 : E →L[ℂ] E) - A) x) x : ℂ) :=
    ContinuousLinearMap.adjoint_inner_right _ x x
  have hconj := inner_conj_symm (𝕜 := ℂ) x ((z • (1 : E →L[ℂ] E) - A) x)
  have hre : (inner ℂ ((z • (1 : E →L[ℂ] E) - A) x) x : ℂ).re
      = (inner ℂ x ((z • (1 : E →L[ℂ] E) - A) x) : ℂ).re := by
    rw [← hconj, Complex.conj_re]
  rw [hadj, hre]
  exact re_inner_shift h z x

omit [CompleteSpace E] in
/-- To the right of the half-plane the shift is injective. -/
theorem shift_ker_eq_bot {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re) :
    ((z • (1 : E →L[ℂ] E) - A) : E →ₗ[ℂ] E).ker = ⊥ := by
  have hlow : ∀ x : E, (z.re - ω) * ‖x‖ ≤ ‖(z • (1 : E →L[ℂ] E) - A) x‖ :=
    norm_ge_of_re_inner_ge (fun x => re_inner_shift h z x)
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hb := hlow x
  rw [show (z • (1 : E →L[ℂ] E) - A) x = 0 from hx, norm_zero] at hb
  have hx0 : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp (le_antisymm hx0 (norm_nonneg x))

/-- To the right of the half-plane the shift is surjective: its range is closed (the shift is
bounded below) and dense (the adjoint is injective). -/
theorem shift_range_eq_top {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re) :
    ((z • (1 : E →L[ℂ] E) - A) : E →ₗ[ℂ] E).range = ⊤ := by
  set T : E →L[ℂ] E := z • (1 : E →L[ℂ] E) - A with hT
  have hc : 0 < z.re - ω := by linarith
  have hlow : ∀ x : E, (z.re - ω) * ‖x‖ ≤ ‖T x‖ :=
    norm_ge_of_re_inner_ge (fun x => re_inner_shift h z x)
  have hlowadj : ∀ x : E, (z.re - ω) * ‖x‖ ≤ ‖ContinuousLinearMap.adjoint T x‖ :=
    norm_ge_of_re_inner_ge (fun x => re_inner_shift_adjoint h z x)
  have hkeradj : ((ContinuousLinearMap.adjoint T : E →L[ℂ] E) : E →ₗ[ℂ] E).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hb := hlowadj x
    rw [show ContinuousLinearMap.adjoint T x = 0 from hx, norm_zero] at hb
    have hx0 : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp (le_antisymm hx0 (norm_nonneg x))
  have hanti : AntilipschitzWith ((z.re - ω)⁻¹).toNNReal (T : E → E) := by
    refine AddMonoidHomClass.antilipschitz_of_bound T ?_
    intro x
    have hb := hlow x
    rw [Real.coe_toNNReal _ (by positivity), inv_mul_eq_div, le_div_iff₀ hc]
    linarith [hb]
  have hclosed : IsClosed (Set.range (T : E → E)) :=
    hanti.isClosed_range T.uniformContinuous
  have hcl : IsClosed (((T : E →ₗ[ℂ] E).range : Submodule ℂ E) : Set E) := hclosed
  haveI : CompleteSpace ((T : E →ₗ[ℂ] E).range : Submodule ℂ E) := hcl.completeSpace_coe
  have hperp : ((T : E →ₗ[ℂ] E).range : Submodule ℂ E)ᗮ = ⊥ := by
    rw [T.orthogonal_range]
    exact hkeradj
  have hdd := Submodule.orthogonal_orthogonal ((T : E →ₗ[ℂ] E).range)
  rw [hperp] at hdd
  convert hdd.symm using 1 <;> (first | rfl | simp [hT])

/-- The resolvent of `A` at a point to the right of the half-plane, as a continuous linear
equivalence. -/
noncomputable def shiftEquiv {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ}
    (hz : ω < z.re) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.ofBijective (z • (1 : E →L[ℂ] E) - A)
    (shift_ker_eq_bot h hz) (shift_range_eq_top h hz)







end BookProof.ChapterNumericalRangeSemigroup


