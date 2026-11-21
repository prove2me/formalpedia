-- Prove2me | Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F002
-- name    : LevyStochCalc_Ito_BigJumpDiffusion_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:28:06.668908+00:00
-- url     : https://prove2.me/theorems/09d1cdc3-2841-4830-987e-50231fa3e2ee
-- title:
--   Source declarations: LevyStochCalc.Ito.BigJumpDiffusion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.BigJumpDiffusion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncating the jumps of a jump diffusion at one mark set

Restricting the jump coefficient of a jump diffusion to a measurable set of marks `A` splits it
into two coefficient bundles, and the compensated integral of an admissible integrand splits
accordingly. Subtracting the everywhere-càdlàg modification of the compensated integral over `A`
from the path leaves the *big-jump path*, which carries the drift, the diffusion and the jumps
outside `A`.

## Main definitions

* `LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.markCutγ` — the coefficient bundle with the jump
  coefficient restricted to a set of marks.
* `LevyStochCalc.Ito.BigJump.SdeData` — the filtration and admissibility data with which a jump
  diffusion satisfies its SDE.
* `LevyStochCalc.Ito.BigJump.cutJumpIntegral` — the everywhere-càdlàg modification of the
  compensated integral of the jump coefficient restricted to a set of marks.
* `LevyStochCalc.Ito.BigJump.bigJumpPath` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl` — the compensated integral of
  an integrand is the sum of the compensated integrals of its two mark cuts.
* `LevyStochCalc.Ito.BigJump.lintegral_sq_iSup_bigJumpPath_lt_top` — the big-jump path has
  square-integrable supremum over every bounded window.
* `LevyStochCalc.Ito.BigJump.isItoLevyProcess_bigJumpPath` — the big-jump path is an Itô–Lévy
  process whose drift and diffusion are those of the jump diffusion along its own path and whose
  jump integrand is the jump coefficient restricted to the complement of the cut.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.Setting

universe v

variable {n d : ℕ} {E : Type v}

end LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.BigJump

universe u v

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.SmallJump

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

section Split

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)

end Split

section Data

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-! `SdeData` is **not** derivable from `JumpDiffusion` alone: the structure's `is_solution`
field bundles the equation and the integrand admissibility but no adaptedness of the path, and
`X_prog` does not follow from them. It is supplied where a solution is built, by
`LevyStochCalc.Ito.BigJump.SdeData.ofSolvesOn` (`Ito/SdeDataOfSolvesOn.lean`). -/

end Data

section Path

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

variable (S : SdeData X) {A : Set E} (hA : MeasurableSet A)
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)

/-- The energy of the truncated compensated integral at the horizon is the energy carried by the
cut. -/
theorem lintegral_sq_cutJumpIntegral (i : Fin n) {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖cutJumpIntegral S hA hℱ0 hnull0 i T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut A (pathJumpCoeff coeffs X.X i) ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← isometry_stochasticIntegral N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') T hT]
  refine lintegral_congr_ae ?_
  filter_upwards [cutJumpIntegral_ae_eq S hA hℱ0 hnull0 i T] with ω hω
  rw [hω]
/-- The truncated compensated integral has finite second moment of its supremum over every
bounded window. -/
theorem lintegral_sq_iSup_cutJumpIntegral_lt_top (i : Fin n) {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ m, (‖Probability.dyadicRunMax
        (cutJumpIntegral S hA hℱ0 hnull0 i) T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  refine lt_of_le_of_lt (Probability.lintegral_iSup_dyadicRunMax_sq_le
    (martingale_cutJumpIntegral S hA hℱ0 hnull0 i) hT.le) ?_
  rw [lintegral_sq_cutJumpIntegral S hA hℱ0 hnull0 i hT]
  exact ENNReal.mul_lt_top (by norm_num) (sq_markCut (S.γ_sq i) A T hT)
end Path

section Diffusion

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

end Diffusion

end LevyStochCalc.Ito.BigJump


