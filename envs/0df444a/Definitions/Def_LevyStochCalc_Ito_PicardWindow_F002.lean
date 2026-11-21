-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardWindow_F002
-- name    : LevyStochCalc_Ito_PicardWindow_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:38:57.083046+00:00
-- url     : https://prove2.me/theorems/f05e5e52-1419-4b5f-917a-0dccb24ca995
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardWindow
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardWindow. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandFrozen_F000
import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F000
import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F001
import Definitions.Def_SourceProof_7875eb8fe5be21407e758cf4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of the SDE on a window

`SolvesOn` records that a path map satisfies the jump-diffusion integral equation at every time
of `[0, T]`, in the `picardStep` form; the integrand hypotheses that make the two stochastic
integrals well-typed are bundled existentially, as in
`LevyStochCalc.Ito.Setting.JumpDiffusion.is_solution`, so that a solution can be re-read with any
proof of them. Two solutions on a common window and a common filtration agree, by the Bielecki
contraction.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### From an `S²` bound to the time-integrated energy -/

/-! ### Auxiliary Bielecki facts -/

/-! ### Solutions on a window -/

section Solves

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)

end Solves

/-! ### The canonical integrand hypotheses along a process with a finite `S²` norm -/

section Canonical

variable {ν : Measure E}
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}

end Canonical

/-! ### The window fixed point is a solution -/

section FixedPoint

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

/-- A fixed point of the frozen Picard step solves the equation on the window. -/
theorem solvesOn_of_isFixedPoint
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 ≤ T) {Y : ℝ → Ω → (Fin n → ℝ)}
    (hYm : Measurable (Function.uncurry Y))
    (hYa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
    (hYb : bieleckiNorm (P := P) 0 T Y < ⊤)
    (hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hfix : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n,
      Y t ω i = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT x₀ t ω i) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T := by
  refine ⟨measurable_sigma_comp_state coeffs hReg hYm,
    progressivelyMeasurable_sigma_comp_state coeffs hReg hYa,
    lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hYm hYS,
    measurable_gamma_comp_state coeffs hReg hYm,
    markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hYa,
    lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hYm hYS, ?_⟩
  intro t ht
  filter_upwards [hfix t ht,
    _root_.Prove2MeSourceProof.h_7875eb8fe5be21407e758cf4 W N ℱ hℱW hℱN coeffs hReg hLip x₀ hYm hYa hYb hYS hT
      ht.1 ht.2] with ω h1 h2
  intro i
  rw [h1 i, h2]
end FixedPoint

end LevyStochCalc.Ito.Picard


