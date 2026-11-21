-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellOrthogonality_F000
-- name    : LevyStochCalc_Driver_CellOrthogonality_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:28:49.472511+00:00
-- url     : https://prove2.me/theorems/828f2cd8-c71a-43f5-8483-3caa924e2a40
-- title:
--   Source declarations: LevyStochCalc.Driver.CellOrthogonality
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellOrthogonality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossVariation_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F002
import Definitions.Def_LevyStochCalc_Brownian_PRPPerpBridge_F000
import Definitions.Def_LevyStochCalc_Driver_CrossElementary_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
import Definitions.Def_LevyStochCalc_Poisson_PerpBridge_F000
import Definitions.Def_SourceProof_21680fbb00c3cbdc68b476b2
import Definitions.Def_SourceProof_5b38410d9c27cac48b90e4c5
import Definitions.Def_SourceProof_da55a4195e0b45ce7b0016e9
import Definitions.Def_SourceProof_e90edda898bb4b6c25399249
import Definitions.Def_SourceProof_ebffe457c2736bba9661d0fd

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of the increments of a Lévy driver's integrals over a cell

Over a cell `(a, b]` with `0 ≤ a < b` the increment of a Brownian Itô integral is orthogonal in
`L²` to the increment of a compensated integral, and the increments against two distinct
Brownian coordinates are orthogonal to each other; restricting an integrand to `(a, b]` turns
the increment across the cell into the integral at the horizon `b`, where the two ranges and the
distinct coordinates are already orthogonal. Either increment is also orthogonal to every
square-integrable weight measurable at the left endpoint `a`.

## Main statements

* `integral_brownian_cell_mul_compensated_cell_eq_zero` — a Brownian increment and a compensated
  increment over the same cell are orthogonal.
* `integral_brownian_cell_mul_brownian_cell_eq_zero` — the increments against two distinct
  Brownian coordinates over the same cell are orthogonal.
* `integral_mul_brownian_cell_eq_zero`, `integral_mul_compensated_cell_eq_zero` — a
  square-integrable weight measurable at the left endpoint is orthogonal to either increment.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **Kunita–Watanabe orthogonality over a cell.** The increment of a Brownian Itô integral
across `(a, b]` is orthogonal to the increment of a compensated integral across `(a, b]`. -/
theorem integral_brownian_cell_mul_compensated_cell_eq_zero (𝒲 : CrossWitness D ℱ) {i : Fin d}
    (hℱW : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
    (hℱN : Poisson.IsPoissonFiltration D.N ℱ)
    {H : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : Ω → ℝ → E → ℝ} (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs b ω
        - Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs a ω)
      * (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs b ω
        - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs a ω) ∂P = 0 := by
  have hb : (0 : ℝ) < b := ha.trans_lt hab
  have hBr := _root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212 (D.W.W i) ℱ (hℱW i) H
    hHm hHp hHs ha hab (Brownian.Ito.measurable_uncurry_indicator_Ioc_mul H hHm a b)
    (Brownian.Ito.progressivelyMeasurable_indicator_Ioc_mul ℱ H hHp a b)
    (Brownian.Ito.lintegral_sq_indicator_Ioc_mul_lt_top H hHs a b) hb
  have hCo := _root_.Prove2MeSourceProof.h_e90edda898bb4b6c25399249 D.N hℱN hφm hφp hφs ha hab
  have hzero := _root_.Prove2MeSourceProof.h_da55a4195e0b45ce7b0016e9 𝒲 (i := i) hℱW hℱN
    (Brownian.Ito.measurable_uncurry_indicator_Ioc_mul H hHm a b)
    (Brownian.Ito.progressivelyMeasurable_indicator_Ioc_mul ℱ H hHp a b)
    (Brownian.Ito.lintegral_sq_indicator_Ioc_mul_lt_top H hHs a b)
    (Poisson.Compensated.measurable_indIoc_mul hφm a b)
    (Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hφp a b)
    (Poisson.Compensated.sq_int_global_indIoc_mul hφs a b) hb.le
  refine Eq.trans ?_ hzero
  refine integral_congr_ae ?_
  filter_upwards [hBr, hCo] with ω e1 e2
  simp only [Brownian.Ito.stochasticIntegral, e1, e2, min_self, min_eq_left hab.le]
/-- **Orthogonality of the cell increments against two distinct Brownian coordinates.** -/
theorem integral_brownian_cell_mul_brownian_cell_eq_zero
    (hℱW : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {i j : Fin d} (hij : i ≠ j)
    {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs b ω
        - Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs a ω)
      * (Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j) K hKm hKp hKs b ω
        - Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j) K hKm hKp hKs a ω) ∂P = 0 := by
  have h := _root_.Prove2MeSourceProof.h_5b38410d9c27cac48b90e4c5 D.W hℱW hHm hHp hHs hKm hKp hKs
    hij ha hab (Z := fun _ => (1 : ℝ)) measurable_const (M := 1) (fun _ => le_of_eq abs_one)
    stronglyMeasurable_const
  simpa only [Brownian.Ito.stochasticIntegral, one_mul] using h
/-- **A weight known at the left endpoint does not see a Brownian cell increment.** -/
theorem integral_mul_brownian_cell_eq_zero
    (hℱW : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {i : Fin d}
    {H : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {z : Ω → ℝ} (hz : MemLp z 2 P) {a b : ℝ} (hza : AEStronglyMeasurable[ℱ a] z P)
    (hab : a < b) :
    ∫ ω, z ω * (Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs b ω
      - Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs a ω) ∂P = 0 :=
  _root_.Prove2MeSourceProof.h_21680fbb00c3cbdc68b476b2 (D.W.W i) (hℱW i) H hHm hHp hHs hz hza hab.le
/-- **A weight known at the left endpoint does not see a compensated cell increment.** -/
theorem integral_mul_compensated_cell_eq_zero (hℱN : Poisson.IsPoissonFiltration D.N ℱ)
    {φ : Ω → ℝ → E → ℝ} (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {z : Ω → ℝ} (hz : MemLp z 2 P) {a b : ℝ} (hza : AEStronglyMeasurable[ℱ a] z P)
    (hab : a < b) :
    ∫ ω, z ω * (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs b ω
      - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs a ω) ∂P = 0 :=
  _root_.Prove2MeSourceProof.h_ebffe457c2736bba9661d0fd D.N hℱN φ hφm hφp hφs hz hza hab.le
end LevyDriver

end LevyStochCalc.Driver


