-- Prove2me | Definitions.Def_SourceProof_374644549dc26783382ef252
-- name    : SourceProof_374644549dc26783382ef252
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:03:25.895707+00:00
-- url     : https://prove2.me/theorems/98a17ec5-72ad-4578-bc23-473c6692a01b
-- title:
--   LevyStochCalc source module: SourceProof_374644549dc26783382ef252
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.martingale_quadVar_stochasticIntegral_rightCont` comes from the `LevyStochCalc.Poisson.Compensated` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensated_F000
import Definitions.Def_SourceProof_fb3437e2bf8e88243b976158

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson L²-Itô–Lévy integral

The L²-Itô–Lévy integral against the compensated Poisson random measure `Ñ`,
with its martingale, quadratic-variation, isometry, and càdlàg properties
(Applebaum 2009 §4.2, Theorems 4.2.3 and 4.2.4).

`stochasticIntegral` is the càdlàg adapted modification (`exists_cadlag_modification`)
of the `L²` integral process `process` (`Poisson/CompensatedProcess.lean`), the
`L²`-limit at every time of the integrals of the mark-step approximants of the
integrand (`Poisson/CompensatedApprox.lean`). `itoIsometry_compensated_unified_existence`
packages the martingale property, the quadratic variation, the L²-isometry, and the
càdlàg paths of `stochasticIntegral` in one 4-conjunct existential;
`itoLevyIsometry`, `quadVar_stochasticIntegral`, `martingale_stochasticIntegral`,
`cadlag_modification_exists`, and `L2Isometry.itoLevyIsometry` are its conjuncts.

`itoIsometry_diff_compensated` is the per-difference L²-isometry for this integral
(Applebaum Thm 4.2.3 step II): the integrals are modifications of the `L²` integral
processes, whose difference isometry `process_sub_lintegral_sq`
(`Poisson/CompensatedDiff.lean`) comes from the mark-step approximants of the two
integrands on a common dyadic refinement. It is consumed by
`Ito.Picard.picardStep_jump_diff_lipschitz_sq_componentwise` and mirrors
`Brownian.Ito.itoIsometry_diff_brownian`.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2 (Thm 4.2.3/4.2.4).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is scoped per-declaration (`open Classical in`) rather than
-- at file scope.

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Integral

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ
    : IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_374644549dc26783382ef252 :
    Martingale
      (fun t ω => (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ ω s e) ^ 2 ∂ν)
      ℱ.rightCont P :=
  LevyStochCalc.Martingale.martingale_of_ae_eq
    (_root_.Prove2MeSourceProof.h_fb3437e2bf8e88243b976158 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (fun t => ((LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global
      t).stronglyMeasurable.pow 2).sub
      ((LevyStochCalc.Poisson.Compensated.compensator_stronglyAdapted ℱ φ h_progMeas t).mono (ℱ.le_rightCont t)))
    (fun t => by
      filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t]
        with ω hω
      show (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2 - _
        = (LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2 - _
      rw [hω]
      rfl)
end Integral

end LevyStochCalc.Poisson.Compensated


