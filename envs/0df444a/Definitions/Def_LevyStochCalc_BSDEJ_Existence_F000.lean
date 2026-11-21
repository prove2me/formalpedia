-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_Existence_F000
-- name    : LevyStochCalc_BSDEJ_Existence_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:28.536175+00:00
-- url     : https://prove2.me/theorems/ce15efae-d293-4c0e-a1f8-6ff0a49f82e7
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.Existence
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.Existence. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_MartingaleRepresentation_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Lipschitz condition on the generator of a BSDEJ

`Lipschitz` is the Lipschitz condition on the generator of a backward SDE with jumps (Tang & Li
1994; Becherer 2006), stated in `ℝ≥0∞`, and `abs_sub_le_of_lipschitz` is its real form.

Existence and uniqueness of the solution are not stated here. The formulation
`continuousBSDEJ_exists_unique`, quantifying over an arbitrary measurable forward process `X`
and asking for a solution in the class `IsBSDEJSolution` whose integrands are adapted to the
natural filtration of a single driver, is refutable: a terminal condition `g(X_T)` independent
of `(W, N)` has no adapted solution, and `ξ = W_T · Ñ_T` none in that class
(`tools/cited_axioms.md`, `Retired #9`). The statement over the augmented joint filtration of a
Lévy driver is `BSDEJ.Solves.exists_unique_solvesBSDEJ` (`BSDEJ/ExistenceUniqueness.lean`), with
the solution class `BSDEJ.Solves.SolvesBSDEJ` (`BSDEJ/Solves.lean`) and the Picard scheme of
`BSDEJ/PicardStep.lean`, `BSDEJ/PicardIterates.lean` and `BSDEJ/PicardLimit.lean`.

## Source

* Tang & Li, "Necessary conditions for optimal control of stochastic
  systems with random jumps", SICON 32(5), 1994.
* Becherer, "Bounded solutions to backward SDEs with jumps for utility
  optimization and indifference hedging", AAP 16(4), 2006.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Existence

universe u v

section Lipschitz
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Lipschitz condition on the BSDEJ generator `f`: uniformly in `(s, x)`, the increment of `f`
is bounded by `L` times the sum of `|y₁ - y₂|`, the supremum norm `‖z₁ - z₂‖` on `Fin d → ℝ`
and the `L²(ν)` distance `(∫ ‖u₁ - u₂‖² dν)^{1/2}` of the jump variables.

The inequality is stated in `ℝ≥0∞`, so it also constrains pairs `u₁, u₂` whose difference is not
square integrable for `ν`; the real-valued form is `abs_sub_le_of_lipschitz`. -/
def Lipschitz {n d : ℕ}
    (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (ν : Measure E) (L : ℝ) : Prop :=
  ∀ s : ℝ, ∀ x : Fin n → ℝ, ∀ y₁ y₂ : ℝ,
    ∀ z₁ z₂ : Fin d → ℝ, ∀ u₁ u₂ : E → ℝ,
    (‖bsdej.f s x y₁ z₁ u₁ - bsdej.f s x y₂ z₂ u₂‖₊ : ℝ≥0∞)
      ≤ ENNReal.ofReal L * ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ))
/-- The real-valued form of the Lipschitz inequality, for jump variables at finite `L²(ν)`
distance. -/
theorem abs_sub_le_of_lipschitz {n d : ℕ}
    {bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E}
    {ν : Measure E} {L : ℝ} (hL : 0 ≤ L) (h : Lipschitz bsdej ν L)
    (s : ℝ) (x : Fin n → ℝ) (y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) :
    |bsdej.f s x y₁ z₁ u₁ - bsdej.f s x y₂ z₂ u₂|
      ≤ L * (|y₁ - y₂| + ‖z₁ - z₂‖
          + Real.sqrt (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
  set A : ℝ≥0∞ := ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν with hA
  have hroot : A ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt A.toReal) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hu]
  have key := h s x y₁ y₂ z₁ z₂ u₁ u₂
  rw [hroot] at key
  have hne : ENNReal.ofReal L * ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
      + ENNReal.ofReal (Real.sqrt A.toReal)) ≠ ⊤ := by finiteness
  have hmono := ENNReal.toReal_mono hne key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.coe_ne_top⟩) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
    ENNReal.coe_toReal, ENNReal.coe_toReal, ENNReal.toReal_ofReal hL,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), coe_nnnorm, coe_nnnorm, coe_nnnorm,
    Real.norm_eq_abs, Real.norm_eq_abs] at hmono
end Lipschitz

end LevyStochCalc.BSDEJ.Existence


