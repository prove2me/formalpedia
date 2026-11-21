-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_Compensated_F000
-- name    : LevyStochCalc_Poisson_Compensated_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:00:48.406177+00:00
-- url     : https://prove2.me/theorems/c64d4480-945a-4158-a35e-6c30eee2c046
-- title:
--   Source declarations: LevyStochCalc.Poisson.Compensated
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.Compensated. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Martingale_CadlagModification_F000
import Definitions.Def_LevyStochCalc_Martingale_CadlagModification_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDiff_F000
import Definitions.Def_SourceProof_2c4e2697eef458aa9c0dbb56

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
/-- The `L²` integral process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` has a modification adapted to
the right-continuous natural filtration whose paths are almost surely càdlàg. -/
theorem exists_cadlag_modification :
    ∃ Y : ℝ → Ω → ℝ, Adapted ℱ.rightCont Y ∧
      (∀ t, Y t =ᵐ[P] process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω)) ∧
          ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L) :=
  LevyStochCalc.Martingale.exists_adapted_ae_cadlag_of_eLpNorm
    (martingale_rightCont_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (_root_.Prove2MeSourceProof.h_95e247e701da3178181c6103 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (fun _ ht => _root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global ht.le)
/-- The L² Itô–Lévy integral `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` against the compensated
measure of a Poisson random measure: the càdlàg adapted modification of the `L²` integral
process `process`, the `L²`-limit of the integrals of the mark-step approximants of `φ`. -/
noncomputable def stochasticIntegral (T : ℝ) : Ω → ℝ :=
  Classical.choose (exists_cadlag_modification N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) T
include hℱ in
lemma stochasticIntegral_adapted :
    Adapted ℱ.rightCont
      (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) :=
  (Classical.choose_spec (exists_cadlag_modification N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)).1
include hℱ in
/-- The stochastic integral agrees almost surely with the `L²` integral process at every
time. -/
lemma stochasticIntegral_ae_eq_process (t : ℝ) :
    stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t
      =ᵐ[P] process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t :=
  (Classical.choose_spec
    (exists_cadlag_modification N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)).2.1 t
include hℱ in
/-- The paths of the stochastic integral are almost surely càdlàg. -/
lemma stochasticIntegral_cadlag :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω)
          (nhdsWithin t (Set.Ioi t))
          (nhds (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω))
        ∧ ∃ L : ℝ,
            Filter.Tendsto
              (fun s => stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω)
              (nhdsWithin t (Set.Iio t)) (nhds L) :=
  (Classical.choose_spec
    (exists_cadlag_modification N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)).2.2
include hℱ in
/-- The stochastic integral is a martingale on the right-continuous natural filtration. -/
theorem martingale_stochasticIntegral_rightCont :
    Martingale (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
      ℱ.rightCont P :=
  LevyStochCalc.Martingale.martingale_of_ae_eq
    (martingale_rightCont_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (fun t => (stochasticIntegral_adapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global
      t).stronglyMeasurable)
    (stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
end Integral

end LevyStochCalc.Poisson.Compensated


