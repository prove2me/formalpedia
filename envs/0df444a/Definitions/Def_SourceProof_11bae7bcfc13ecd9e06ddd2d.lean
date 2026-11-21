-- Prove2me | Definitions.Def_SourceProof_11bae7bcfc13ecd9e06ddd2d
-- name    : SourceProof_11bae7bcfc13ecd9e06ddd2d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:11:53.832538+00:00
-- url     : https://prove2.me/theorems/2fb4e898-7df7-45b0-815d-2d61354a9ddf
-- title:
--   LevyStochCalc source module: SourceProof_11bae7bcfc13ecd9e06ddd2d
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub` comes from the `LevyStochCalc.Ito.SmallJumpProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SmallJumpProcess_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Removing the small jumps of a jump diffusion

For a jump diffusion `X` and an antitone family `A : ℕ → Set E` of mark sets whose intersection
is `ν`-null, the *big-jump process* is the path with the compensated integral of the jump
coefficient over `A m` subtracted coordinatewise. The subtracted term is the everywhere-càdlàg
modification of the compensated integral of a mark cut, so its `L²` size is the energy carried
by `A m` and vanishes as `m → ∞`; the big-jump processes therefore converge to the path at every
fixed nonnegative time in `L²`, almost surely along a subsequence, at almost every time of a
bounded window along a subsequence, and — after composing with a `C²` function of time and
state — pathwise along that subsequence.

## Main definitions

* `LevyStochCalc.Ito.SmallJump.JumpIntegrand` — the filtration and admissibility data with
  which the coordinates of the jump coefficient along a path are integrated against `Ñ`.
* `LevyStochCalc.Ito.SmallJump.smallJumpIntegral` — the everywhere-càdlàg modification of the
  compensated integral of one coordinate of the jump coefficient, restricted to the marks
  in `A m`.
* `LevyStochCalc.Ito.SmallJump.bigJumpProcess` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.SmallJump.measurable_uncurry_bigJumpProcess` — joint measurability of a
  coordinate of the big-jump process in the sample point and the time.
* `LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub` — `L²` convergence of
  the big-jump processes to the path at a fixed nonnegative time.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors along a subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors at almost every time of a bounded window, along a
  subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_comp` — the same, transported through a
  `C²` function of time and state.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_drift_bigJumpProcess`,
  `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_quadVar_bigJumpProcess` — pathwise
  convergence of the drift and quadratic-variation integrals along the big-jump processes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.SmallJump

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
variable {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable {Xp : ℝ → Ω → (Fin n → ℝ)} {A : ℕ → Set E}

section Basic

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)

end Basic

section Limits

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)


theorem _root_.Prove2MeSourceProof.h_11bae7bcfc13ecd9e06ddd2d (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m => ∫⁻ ω,
        (‖bigJumpProcess G hA hℱ0 hnull0 m t ω i - Xp t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hrw : ∀ m : ℕ,
      ∫⁻ ω, (‖LevyStochCalc.Ito.SmallJump.bigJumpProcess G hA hℱ0 hnull0 m t ω i - Xp t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖LevyStochCalc.Ito.SmallJump.smallJumpIntegral G hA hℱ0 hnull0 m i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro m
    refine lintegral_congr fun ω => ?_
    rw [LevyStochCalc.Ito.SmallJump.bigJumpProcess_sub, nnnorm_neg]
  simp_rw [hrw]
  rcases eq_or_lt_of_le ht with h0 | h0
  · subst h0
    have hz : ∀ m : ℕ,
        ∫⁻ ω, (‖LevyStochCalc.Ito.SmallJump.smallJumpIntegral G hA hℱ0 hnull0 m i 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
      intro m
      have hae : (fun ω => (‖LevyStochCalc.Ito.SmallJump.smallJumpIntegral G hA hℱ0 hnull0 m i 0 ω‖₊ : ℝ≥0∞) ^ 2)
          =ᵐ[P] fun _ => (0 : ℝ≥0∞) := by
        filter_upwards [LevyStochCalc.Ito.SmallJump.smallJumpIntegral_ae_zero G hA hℱ0 hnull0 m i (le_refl (0 : ℝ))]
          with ω hω
        simp [hω]
      rw [lintegral_congr_ae hae]
      simp
    simp_rw [hz]
    exact tendsto_const_nhds
  · exact LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_smallJumpIntegral G hA hℱ0 hnull0 hanti hnull i h0
end Limits

end LevyStochCalc.Ito.SmallJump


