-- Prove2me | Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F003
-- name    : LevyStochCalc_Ito_BigJumpDiffusion_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:20:20.167639+00:00
-- url     : https://prove2.me/theorems/b2c8cb17-4781-4515-b97a-bfa43f2c3ba8
-- title:
--   Source declarations: LevyStochCalc.Ito.BigJumpDiffusion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.BigJumpDiffusion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000
import Definitions.Def_LevyStochCalc_Ito_SmallJumpProcess_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F003

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


section Diffusion

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

/-- The multidimensional Brownian Itô integral depends only on its integrand. -/
theorem brownianIntegral_congr_fun (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    {Z Z' : ℝ → Ω → (Fin d → ℝ)}
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω j)
    (hq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm' : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z' s ω j))
    (hp' : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z' s ω j)
    (hq' : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h : Z = Z') (T : ℝ) :
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
        W ℱ hℱ Z hm hp hq T
      = LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
        W ℱ hℱ Z' hm' hp' hq' T := by
  subst h; rfl
end Diffusion

end LevyStochCalc.Ito.BigJump


