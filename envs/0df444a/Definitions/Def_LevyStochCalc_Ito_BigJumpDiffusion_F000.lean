-- Prove2me | Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F000
-- name    : LevyStochCalc_Ito_BigJumpDiffusion_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:21:07.213994+00:00
-- url     : https://prove2.me/theorems/090f4b19-a74c-4997-81c8-9856b4efdb92
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

/-- The coefficient bundle with the jump coefficient restricted to a set of marks: `γ` is left
unchanged on `A` and replaced by `0` off `A`. -/
noncomputable def JumpDiffusionCoeffs.markCutγ (coeffs : JumpDiffusionCoeffs n d E) (A : Set E) :
    JumpDiffusionCoeffs n d E where
  μ := coeffs.μ
  σ := coeffs.σ
  γ := fun s y e => A.indicator (fun _ => coeffs.γ s y e) e
@[simp] theorem JumpDiffusionCoeffs.markCutγ_μ (coeffs : JumpDiffusionCoeffs n d E)
    (A : Set E) : (coeffs.markCutγ A).μ = coeffs.μ := rfl
@[simp] theorem JumpDiffusionCoeffs.markCutγ_σ (coeffs : JumpDiffusionCoeffs n d E)
    (A : Set E) : (coeffs.markCutγ A).σ = coeffs.σ := rfl
@[simp] theorem JumpDiffusionCoeffs.markCutγ_γ (coeffs : JumpDiffusionCoeffs n d E) (A : Set E)
    (s : ℝ) (y : Fin n → ℝ) (e : E) :
    (coeffs.markCutγ A).γ s y e = A.indicator (fun _ => coeffs.γ s y e) e := rfl
/-- A coordinate of the restricted jump coefficient is the restriction of that coordinate. -/
theorem JumpDiffusionCoeffs.markCutγ_γ_apply (coeffs : JumpDiffusionCoeffs n d E) (A : Set E)
    (s : ℝ) (y : Fin n → ℝ) (e : E) (i : Fin n) :
    (coeffs.markCutγ A).γ s y e i = A.indicator (fun _ => coeffs.γ s y e i) e := by
  by_cases he : e ∈ A <;> simp [he]
/-- The jump coefficient is the sum of its restrictions to a set of marks and to its
complement. -/
theorem JumpDiffusionCoeffs.markCutγ_add_markCutγ_compl (coeffs : JumpDiffusionCoeffs n d E)
    (A : Set E) (s : ℝ) (y : Fin n → ℝ) (e : E) :
    coeffs.γ s y e = (coeffs.markCutγ A).γ s y e + (coeffs.markCutγ Aᶜ).γ s y e := by
  by_cases he : e ∈ A <;> simp [he]
/-- The restricted jump coefficient is supported on the cut. -/
theorem JumpDiffusionCoeffs.markCutγ_eq_zero (coeffs : JumpDiffusionCoeffs n d E) (A : Set E) :
    ∀ (s : ℝ) (y : Fin n → ℝ) (e : E), e ∉ A → (coeffs.markCutγ A).γ s y e = 0 :=
  fun _ _ _ he => Set.indicator_of_notMem he _
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

/-- The compensated integral of an integrand determines the compensated integral of any
integrand equal to it. -/
theorem stochasticIntegral_congr_fun {φ ψ : Ω → ℝ → E → ℝ}
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hψp : Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hψq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h : φ = ψ) (T : ℝ) :
    stochasticIntegral N ℱ hℱ φ hφm hφp hφq T
      = stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T := by
  subst h; rfl
omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- An integrand is the sum of its restrictions to a set of marks and to its complement. -/
theorem markCut_add_markCut_compl (A : Set E) (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    markCut A φ ω s e + markCut Aᶜ φ ω s e = φ ω s e := by
  by_cases he : e ∈ A <;> simp [markCut, he]

end Split
end LevyStochCalc.Ito.BigJump


