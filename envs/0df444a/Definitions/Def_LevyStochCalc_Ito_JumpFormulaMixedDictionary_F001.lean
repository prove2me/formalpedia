-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixedDictionary_F001
-- name    : LevyStochCalc_Ito_JumpFormulaMixedDictionary_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:40:58.100851+00:00
-- url     : https://prove2.me/theorems/b524526e-4c7f-4500-bcbf-7d20303d30be
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaMixedDictionary
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaMixedDictionary. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixedDictionary_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The split-drift dictionary for the mixed integrands

Splitting a finite-activity jump diffusion into a continuous Itô part and a pathwise jump sum
replaces the drift `μ` by `μ` minus the compensator `∫_A γ dν` of the jumps, while the pathwise
jump sum contributes the intensity integral of the jump increment. Read with the derivatives of
the state function at a state `y` and the coefficients at a state `x`, the two presentations of
the drift differ by the first-order term `∑ᵢ ∂ᵢu(s, y) ∫_A γᵢ(s, x) dν`, which the compensator
subtracted from the drift supplies exactly.

The statements below are the mixed forms of the drift reconciliation, of the split-drift
dictionary in the coordinates with a time coordinate prepended, and of the Itô–Lévy identity
assembled from them; the assembled identity carries the compensator-drift term over the mark set
carrying the jump coefficient. At `y = x` they are the statements of
`LevyStochCalc.Ito.JumpFormulaFiniteActivity`.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedFirstOrder_eq`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedCompensatorDriftIntegrand_eq_sub` — the mark
  integral of the mixed compensator-drift integrand as the mark integral of the mixed jump
  increment minus the first-order term.
* `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedCompensatorDrift_eq_sub`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_firstOrder_add_mixedCompensatorDrift` — the drift
  reconciliation over a time window for the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.mixedDriftIntegrand_dictionary`,
  `LevyStochCalc.Ito.JumpFormula.splitDriftIntegrand_dictionary_mixed` — the non-stochastic
  integrands of Itô's formula in the prepended coordinates, with the derivatives at one state
  and the coefficients at another, as the mixed drift integrand and as the mixed drift integrand
  minus the first-order term.
* `LevyStochCalc.Ito.JumpFormula.splitDrift_pointwise_mixed`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_splitDrift_dictionary_mixed` — the same taken
  against a unit time drift, the drift with the jump compensator subtracted and a diffusion
  matrix whose time row vanishes, pointwise and integrated over a window.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed`,
  `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_of_support` — the
  Itô–Lévy identity for the mixed integrands from the split-drift identity and the jump-sum
  identity, with the compensator-drift term over the mark set and, for a jump coefficient
  carried by that set, over the whole mark space.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe v

section MixedDriftReconciliation

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

end MixedDriftReconciliation

section MixedSplitDrift

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

end MixedSplitDrift

section MixedAssembly

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E}

/-- **The Itô–Lévy formula for the mixed integrands from the split-drift form.** If along a pair
of paths the increment of `u` splits into the mixed drift integral taken against the drift with
the jump compensator subtracted, a diffusion term `Dm` and a jump term `Js`, and if the jump term
is a compensated term `Cm` plus the intensity integral of the mixed jump increment over a mark
set, then the increment of `u` is the mixed drift integral, `Dm`, `Cm` and the integral of the
mixed compensator-drift integrand over that mark set. -/
theorem itoLevy_of_splitDrift_and_jumpSum_mixed {A : Set E} {y x : ℝ → Fin n → ℝ} {T : ℝ}
    {Dm Cm Js : ℝ}
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n,
      IntegrableOn (fun e => coeffs.γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => mixedJumpIncrement u coeffs.γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn
      (fun s => ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume)
    (hdt : IntegrableOn (fun s => mixedDriftIntegrand u coeffs s (y s) (x s))
      (Set.Icc (0 : ℝ) T) volume)
    (hsplit : u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s) (x s)
            - ∑ i : Fin n, gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
        + Dm + Js)
    (hjump : Js = Cm + ∫ s in Set.Icc (0 : ℝ) T,
      ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν) :
    u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s) (x s)) + Dm + Cm
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e in A, mixedCompensatorDriftIntegrand u coeffs.γ s (y s) (x s) e ∂ν := by
  have hcancel := setIntegral_firstOrder_add_mixedCompensatorDrift (u := u) (γ := coeffs.γ)
    A y x T hγ hΔ hΔt hgt
  have hdsplit : (∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s) (x s)
        - ∑ i : Fin n, gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
      = (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s) (x s))
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν :=
    integral_sub hdt hgt
  rw [hdsplit] at hsplit
  rw [hjump] at hsplit
  linarith
/-- The Itô–Lévy formula for the mixed integrands with the compensator-drift term over the whole
mark space, for a jump coefficient carried by the mark set of the jump term. -/
theorem itoLevy_of_splitDrift_and_jumpSum_mixed_of_support {A : Set E} {y x : ℝ → Fin n → ℝ}
    {T : ℝ} {Dm Cm Js : ℝ}
    (hsupp : ∀ (s : ℝ) (z : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s z e = 0)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n,
      IntegrableOn (fun e => coeffs.γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => mixedJumpIncrement u coeffs.γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn
      (fun s => ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume)
    (hdt : IntegrableOn (fun s => mixedDriftIntegrand u coeffs s (y s) (x s))
      (Set.Icc (0 : ℝ) T) volume)
    (hsplit : u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s) (x s)
            - ∑ i : Fin n, gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
        + Dm + Js)
    (hjump : Js = Cm + ∫ s in Set.Icc (0 : ℝ) T,
      ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν) :
    u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s) (x s)) + Dm + Cm
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e, mixedCompensatorDriftIntegrand u coeffs.γ s (y s) (x s) e ∂ν := by
  have hE : (∫ s in Set.Icc (0 : ℝ) T,
        ∫ e, mixedCompensatorDriftIntegrand u coeffs.γ s (y s) (x s) e ∂ν)
      = ∫ s in Set.Icc (0 : ℝ) T,
          ∫ e in A, mixedCompensatorDriftIntegrand u coeffs.γ s (y s) (x s) e ∂ν :=
    setIntegral_congr_fun measurableSet_Icc fun s _ =>
      integral_mixedCompensatorDriftIntegrand_eq_setIntegral hsupp s (y s) (x s)
  rw [hE]
  exact itoLevy_of_splitDrift_and_jumpSum_mixed hγ hΔ hΔt hgt hdt hsplit hjump
end MixedAssembly

end LevyStochCalc.Ito.JumpFormula


