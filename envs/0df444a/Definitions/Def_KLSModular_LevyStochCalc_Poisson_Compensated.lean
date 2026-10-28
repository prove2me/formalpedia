-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Poisson_Compensated
-- name    : KLSModular_LevyStochCalc_Poisson_Compensated
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:10:48.048154+00:00
-- url     : https://prove2.me/theorems/cafbfbf8-33d8-4018-b6c5-9924b126eba7
-- title:
--   Compensated Poisson $L^2$ Itô–Lévy integral
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). For a probability measure $P$, a sigma-finite mark measure $\nu$, a Poisson random measure $N$, a filtration satisfying `IsPoissonFiltration`, and a jointly measurable, marked-progressively measurable integrand with finite squared $\mathbb{R}_{\ge 0}\cup\{\infty\}$-valued energy on every positive horizon, `stochasticIntegral` is the càdlàg adapted modification of the compensated $L^2$ integral process. The bundle proves its adaptedness, equality almost everywhere at each fixed time with `process`, and almost-sure càdlàg paths, together with `itoIsometry_diff_compensated`, which identifies the squared $L^2$ norm of the difference of two such integrals with the integrated squared norm of the difference of their integrands.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Poisson.RandomMeasure
--   import LevyStochCalc.Poisson.NaturalFiltration
--   import LevyStochCalc.Poisson.CompensatedProcessQuadVar
--   import LevyStochCalc.Poisson.CompensatedDiff
--   import LevyStochCalc.Martingale.CadlagModification
--   import Mathlib.Probability.Martingale.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def stochasticIntegral (T : ℝ) : Ω → ℝ :=
--     Classical.choose (exists_cadlag_modification N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) T
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3), [`LevyStochCalc/Poisson/NaturalFiltration`](https://prove2.me/theorems/3fc301ef-9e1c-4f69-a794-649cd2253f90), [`LevyStochCalc/Poisson/CompensatedProcessQuadVar`](https://prove2.me/theorems/1ee3add4-ecaf-47dc-8102-589c03325850), [`LevyStochCalc/Poisson/CompensatedDiff`](https://prove2.me/theorems/483da946-95f5-42b8-81bf-ad874c1b5324), [`LevyStochCalc/Martingale/CadlagModification`](https://prove2.me/theorems/c78ec2ac-f2f0-4f15-be75-bb7fc7d56092).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/Compensated.lean) · `LevyStochCalc.Poisson.Compensated` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/Compensated.lean#L67-L341 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.Compensated`, definition bundle `KLSModular_LevyStochCalc_Poisson_Compensated`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_NaturalFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedProcessQuadVar
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDiff
import Definitions.Def_KLSModular_LevyStochCalc_Martingale_CadlagModification
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/Compensated.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
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
    (process_eLpNorm_two_right_tendsto N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (fun _ ht => process_ae_zero_of_nonpos N ℱ hℱ φ h_meas h_progMeas h_sq_int_global ht.le)
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
end Integral
/-- **L²-isometry for the *difference* of two compensated-Poisson Itô-Lévy integrals.**

For two jointly-measurable, progressively-measurable, L²-bounded
integrands `φ₁, φ₂ : Ω → ℝ → E → ℝ`, the difference
`M¹_T - M²_T := ∫_0^T ∫_E φ₁ Ñ - ∫_0^T ∫_E φ₂ Ñ` satisfies the
L²-isometry against the *integrand difference*:

  `𝔼 |M¹_T - M²_T|² = 𝔼 ∫_0^T ∫_E |φ₁(s, e) - φ₂(s, e)|² ν(de) ds`.

This is the per-`(φ₁, φ₂)` instance of the L²-linearity + isometry of the
Itô-Lévy integral as a linear isometry from `L²(Ω × [0, T] × E, dP ⊗ ds ⊗ dν)`
to `L²(Ω, dP)` (Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed.,
CUP 2009, **Theorem 4.2.3** step (II); Ikeda-Watanabe **Section II.3**). Both
integrals are modifications of the `L²` integral processes of their integrands,
whose difference isometry `process_sub_lintegral_sq` comes from the mark-step
approximants of the two integrands on a common dyadic refinement. -/
theorem itoIsometry_diff_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (h_meas₁ : Measurable (fun (p : Ω × ℝ × E) => φ₁ p.1 p.2.1 p.2.2))
    (h_meas₂ : Measurable (fun (p : Ω × ℝ × E) => φ₂ p.1 p.2.1 p.2.2))
    (h_progMeas₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (h_progMeas₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (h_sq_int_global₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_sq_int_global₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq_int_global₁ T ω
              - stochasticIntegral N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq_int_global₂ T ω‖₊
            : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← process_sub_lintegral_sq N ℱ hℱ φ₁ φ₂ h_meas₁ h_meas₂ h_progMeas₁ h_progMeas₂
    h_sq_int_global₁ h_sq_int_global₂ hT]
  refine lintegral_congr_ae ?_
  filter_upwards [stochasticIntegral_ae_eq_process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq_int_global₁ T,
    stochasticIntegral_ae_eq_process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq_int_global₂ T] with ω h₁ h₂
  rw [h₁, h₂]
end Compensated
end Poisson
end LevyStochCalc


