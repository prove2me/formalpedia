-- Prove2me | Definitions.Def_NonvacuityItoLevy_F001
-- name    : NonvacuityItoLevy_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:37:38.525306+00:00
-- url     : https://prove2.me/theorems/128c52bf-482d-4a3d-88aa-a457113dcd18
-- title:
--   Source declarations: NonvacuityItoLevy
-- statement:
--   Source-preserving extracted declarations from NonvacuityItoLevy. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityItoLevy_F000
import Definitions.Def_SourceProof_1cfc3aa11ae6a425fc4b5453

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A jump diffusion satisfying the hypotheses of the Itô–Lévy formula

The scalar jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)` with `X_0 = 0`, driven by a
one-dimensional Brownian motion and a Poisson random measure of intensity `dt ⊗ δ_1` on
`[0, ∞) × ℝ`, together with the state function `u(t, x) = x₀²` on the horizon `[0, 1]`.

The coefficients `μ = 0`, `σ = 1`, `γ(s, x, e) = e` are regular and Lipschitz with constant
`0`, so the SDE has a solution, and `u` is `C²` with gradient `∇u(s, x) = 2x₀`, diffusion
integrand `(∇u)ᵀσ = 2x₀`, jump increment `u(x + e) − u(x) = 2ex₀ + e²` and compensator drift
`u(x + e) − u(x) − e∇u(x) = e²`. The derived energies are finite because the solution has a
finite `S²` norm on every window, and the compensator drift is the constant `1`.

The gradient of `u` is unbounded, so `u` lies outside the range of the Itô–Lévy formula for a
state function with bounded first and second derivatives.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpFormula

/-! ### The model -/

/-! ### Regularity of the coefficients -/

/-- The coefficients are Lipschitz in the state variable with constant `0`. -/
theorem coeffs_isLipschitz : coeffs.IsLipschitz jumpIntensity 0 := by
  refine ⟨le_rfl, ?_, ?_, ?_⟩
  · intro s x₁ x₂
    simp [coeffs]
  · intro s x₁ x₂
    simp [coeffs]
  · intro s x₁ x₂
    simp [coeffs]
/-! ### The derivatives of `u(t, x) = x₀²` -/

theorem contDiff_uSq : ContDiff ℝ 2 (Function.uncurry uSq) := by
  have h : ContDiff ℝ 2 fun p : ℝ × (Fin 1 → ℝ) => p.2 0 :=
    contDiff_pi.mp (contDiff_snd : ContDiff ℝ 2 fun p : ℝ × (Fin 1 → ℝ) => p.2) 0
  exact h.pow 2
theorem hasFDerivAt_uSq (x : Fin 1 → ℝ) :
    HasFDerivAt (fun y : Fin 1 → ℝ => (y 0) ^ 2)
      ((2 * x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
    (x := x)).pow 2
  simpa using h
/-- The gradient of `u(t, x) = x₀²` is `2x₀`. -/
theorem gradient_uSq (s : ℝ) (x : Fin 1 → ℝ) (i : Fin 1) :
    gradient uSq s x i = 2 * x 0 := by
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  change fderiv ℝ (uSq s) x (Pi.single 0 1) = 2 * x 0
  have huf : uSq s = fun y : Fin 1 → ℝ => (y 0) ^ 2 := rfl
  rw [huf, (hasFDerivAt_uSq x).fderiv]
  simp
/-- The diffusion integrand `(∇u)ᵀσ` of `u(t, x) = x₀²` is `2x₀`. -/
theorem diffusionIntegrand_uSq (s : ℝ) (x : Fin 1 → ℝ) (j : Fin 1) :
    diffusionIntegrand uSq coeffs.σ s x j = 2 * x 0 := by
  change ∑ i : Fin 1, gradient uSq s x i * coeffs.σ s x i j = 2 * x 0
  simp [gradient_uSq, coeffs]
/-- The jump increment of `u(t, x) = x₀²` at a mark `e` is `2ex₀ + e²`. -/
theorem jumpIncrement_uSq (s : ℝ) (x : Fin 1 → ℝ) (e : ℝ) :
    uSq s (x + coeffs.γ s x e) - uSq s x = 2 * e * x 0 + e ^ 2 := by
  simp only [uSq, coeffs, Pi.add_apply]
  ring
/-- The compensator-drift integrand of `u(t, x) = x₀²` at a mark `e` is `e²`. -/
theorem compensatorDriftIntegrand_uSq (s : ℝ) (x : Fin 1 → ℝ) (e : ℝ) :
    compensatorDriftIntegrand uSq coeffs.γ s x e = e ^ 2 := by
  change uSq s (x + coeffs.γ s x e) - uSq s x
      - ∑ i : Fin 1, coeffs.γ s x e i * gradient uSq s x i = e ^ 2
  rw [jumpIncrement_uSq]
  simp only [coeffs, gradient_uSq, Fin.sum_univ_one]
  ring
/-- The gradient of `u(t, x) = x₀²` is unbounded. -/
theorem not_bddAbove_gradient_uSq :
    ¬ ∃ K : ℝ, ∀ (s : ℝ) (x : Fin 1 → ℝ) (i : Fin 1), |gradient uSq s x i| ≤ K := by
  rintro ⟨K, hK⟩
  have h := hK 0 (fun _ => |K| + 1) 0
  rw [gradient_uSq] at h
  have h1 : |K| + 1 ≤ |2 * (|K| + 1)| := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (|K| + 1))]
    linarith [abs_nonneg K]
  have h2 : K ≤ |K| := le_abs_self K
  linarith
/-! ### Finite energy along an `S²`-bounded path -/

section Energy

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A scalar function of at most quadratic growth, evaluated along a scalar path with a finite
`S²` norm on every window, has finite time-integrated `L²` energy on every window. -/
theorem lintegral_sq_comp_lt_top {Z : ℝ → Ω → (Fin 1 → ℝ)}
    (hS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (g : ℝ → ℝ) (A B : ℝ≥0) (hg : ∀ y : ℝ, ‖g y‖₊ ^ 2 ≤ A * ‖y‖₊ ^ 2 + B) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖g (Z s ω 0)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hen : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Z s ω 0‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    simpa only [Fin.sum_univ_one] using
      _root_.Prove2MeSourceProof.h_1cfc3aa11ae6a425fc4b5453 hS T'
  have hbound : ∀ (ω : Ω) (s : ℝ), (‖g (Z s ω 0)‖₊ : ℝ≥0∞) ^ 2
      ≤ (A : ℝ≥0∞) * (‖Z s ω 0‖₊ : ℝ≥0∞) ^ 2 + (B : ℝ≥0∞) := by
    intro ω s
    exact_mod_cast ENNReal.coe_le_coe.mpr (hg (Z s ω 0))
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      ((A : ℝ≥0∞) * (‖Z s ω 0‖₊ : ℝ≥0∞) ^ 2 + (B : ℝ≥0∞)) ∂volume
      = (A : ℝ≥0∞) * (∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z s ω 0‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + (B : ℝ≥0∞) * volume (Set.Icc (0 : ℝ) T') := by
    intro ω
    rw [lintegral_add_right' _ aemeasurable_const, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
      setLIntegral_const]
  have houter : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      ((A : ℝ≥0∞) * (‖Z s ω 0‖₊ : ℝ≥0∞) ^ 2 + (B : ℝ≥0∞)) ∂volume ∂P
      = (A : ℝ≥0∞) * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖Z s ω 0‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + (B : ℝ≥0∞) * volume (Set.Icc (0 : ℝ) T') := by
    simp_rw [hinner]
    rw [lintegral_add_right' _ aemeasurable_const, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
      lintegral_const, measure_univ, mul_one]
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => hbound ω s) ?_
  rw [houter]
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top hen, ?_⟩
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
end Energy

/-- `y ↦ 2y` has at most quadratic growth. -/
theorem nnnorm_two_mul_sq_le (y : ℝ) : ‖2 * y‖₊ ^ 2 ≤ 4 * ‖y‖₊ ^ 2 + 0 := by
  rw [← NNReal.coe_le_coe]
  push_cast
  have h1 : ‖2 * y‖ ^ 2 = 4 * y ^ 2 := by rw [Real.norm_eq_abs, sq_abs]; ring
  have h2 : ‖y‖ ^ 2 = y ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [h1, h2]
  norm_num
/-- `y ↦ 2y + 1` has at most quadratic growth. -/
theorem nnnorm_two_mul_add_one_sq_le (y : ℝ) : ‖2 * y + 1‖₊ ^ 2 ≤ 8 * ‖y‖₊ ^ 2 + 2 := by
  rw [← NNReal.coe_le_coe]
  push_cast
  have h1 : ‖2 * y + 1‖ ^ 2 = (2 * y + 1) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖y‖ ^ 2 = y ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [h1, h2]
  nlinarith [sq_nonneg (2 * y - 1)]
/-! ### The witness -/

open LevyStochCalc.Brownian.Multidim (MultidimBrownianMotion)
open LevyStochCalc.Poisson (PoissonRandomMeasure)
open LevyStochCalc.Ito.BigJump (SdeData)

end LevyStochCalc.Examples.Nonvacuity

-- P2M_SOURCE_AUDIT_ONLY: #print axioms LevyStochCalc.Examples.Nonvacuity.itoLevyFormula_general_nonvacuous


