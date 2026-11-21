-- Prove2me | Definitions.Def_SourceProof_ae75084e913ed280513dd96a
-- name    : SourceProof_ae75084e913ed280513dd96a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:33:39.280806+00:00
-- url     : https://prove2.me/theorems/4a5a8338-1a1b-4667-8a76-54abb9fa9c21
-- title:
--   LevyStochCalc source module: SourceProof_ae75084e913ed280513dd96a
-- statement:
--   The original source theorem `LevyStochCalc.Ito.BigJump.isItoLevyProcess_bigJumpPath` comes from the `LevyStochCalc.Ito.BigJumpDiffusion` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F001
import Definitions.Def_SourceProof_c1b36e8cddd2b346f7818b69

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


theorem _root_.Prove2MeSourceProof.h_ae75084e913ed280513dd96a (i : Fin n) :
    IsItoLevyProcess W N S.ℱ S.isBrownian S.isPoisson
      (fun t ω => bigJumpPath S hA hℱ0 hnull0 t ω i) (fun _ => x₀ i)
      (fun s ω => coeffs.μ s (X.X s ω) i) (fun s ω => coeffs.σ s (X.X s ω) i)
      (pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i) := by
  have hbridge : LevyStochCalc.Ito.SmallJump.pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i
      = LevyStochCalc.Poisson.Compensated.markCut Aᶜ (LevyStochCalc.Ito.SmallJump.pathJumpCoeff coeffs X.X i) := LevyStochCalc.Ito.BigJump.pathJumpCoeff_markCutγ Aᶜ X.X i
  have hγm := LevyStochCalc.Ito.BigJump.measurable_pathJumpCoeff_markCutγ_compl S hA i
  have hγp := LevyStochCalc.Ito.BigJump.markedProg_pathJumpCoeff_markCutγ_compl S hA i
  have hγq := LevyStochCalc.Ito.BigJump.sq_pathJumpCoeff_markCutγ_compl (A := A) S i
  refine ⟨LevyStochCalc.Ito.BigJump.measurable_uncurry_bigJumpPath_coord S hA hℱ0 hnull0 i, fun j => S.σ_meas i j,
    fun j => S.σ_prog i j, fun j => S.σ_sq i j, hγm, hγp, hγq, ?_⟩
  have hcg : LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
        (LevyStochCalc.Ito.SmallJump.pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i) hγm hγp hγq
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson (LevyStochCalc.Poisson.Compensated.markCut Aᶜ (LevyStochCalc.Ito.SmallJump.pathJumpCoeff coeffs X.X i))
        (LevyStochCalc.Poisson.Compensated.measurable_markCut (S.γ_meas i) hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA.compl)
        (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (S.γ_sq i) Aᶜ T' hT') := by
    funext t
    exact LevyStochCalc.Ito.BigJump.stochasticIntegral_congr_fun N S.ℱ S.isPoisson hγm hγp hγq _ _ _ hbridge t
  intro t ht
  filter_upwards [S.sde t ht, LevyStochCalc.Ito.BigJump.cutJumpIntegral_ae_eq S hA hℱ0 hnull0 i t,
    _root_.Prove2MeSourceProof.h_c1b36e8cddd2b346f7818b69 N S.ℱ S.isPoisson (LevyStochCalc.Ito.SmallJump.pathJumpCoeff coeffs X.X i)
      (S.γ_meas i) (S.γ_prog i) (S.γ_sq i) hA t] with ω h1 h2 h3
  change X.X t ω i - LevyStochCalc.Ito.BigJump.cutJumpIntegral S hA hℱ0 hnull0 i t ω = _
  rw [h1 i, h2, h3, hcg]
  ring
end Path

section Diffusion

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

end Diffusion

end LevyStochCalc.Ito.BigJump


