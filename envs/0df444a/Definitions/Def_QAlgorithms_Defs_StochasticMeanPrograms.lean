-- Prove2me | Definitions.Def_QAlgorithms_Defs_StochasticMeanPrograms
-- name    : QAlgorithms_Defs_StochasticMeanPrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:35.133362+00:00
-- url     : https://prove2.me/theorems/87ef33cd-1a3a-4c0d-9951-d94bd87697f4
-- title:
--   StochasticMeanPrograms
-- statement:
--   StochasticMeanPrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\StochasticMeanPrograms.lean

import Definitions.Def_QAlgorithms_Defs_ContinuousOraclePrograms
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.StochasticOptimization

variable {n m d k b w M K N c out : ℕ}

/-- A public-parameter family of actual quantum sampling-oracle programs,
2308.01582 pp.8–9 Lemma 1. Accuracy and resource properties are separate
theorem obligations; there is no free mean instruction or correctness field. -/
structure QuantumMeanEstimationProgram (d : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  program : ℝ → ℝ → ℝ → ContinuousOracleProgram d H

/-- One fresh classical sample costs one preparation query, followed by
the physical value-register measurement (2308.01582 pp.3,11). -/
def classicalSample {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : ContinuousOracleProgram d H :=
  .fresh (.query false (.measure fun v => .output v))

/-- Algorithm 1, with its printed threshold and failure schedule
(2308.01582 p.9). For accuracy above L a fresh sample is the disclosed
completion; L=0 also takes a sample, since zero variance need not mean zero
expectation. Negative L
or nonpositive accuracy diverges rather than dividing by zero. -/
def quantumMeanEstimationPlus {d : ℕ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : QuantumMeanEstimationProgram d H)
    (L sigma : ℝ) : ContinuousOracleProgram d H :=
  if L < 0 ∨ sigma ≤ 0 then .diverge
  else if L = 0 then classicalSample
  else if L < sigma then classicalSample
  else .bind (.fresh (M.program L (sigma / 4) (sigma ^ 6 / (4 * L) ^ 6))) fun X1 =>
    .bind classicalSample fun X2 =>
      if ‖X1 - X2‖ ≤ sigma / 4 + 16 * L ^ 3 / sigma ^ 2 then .output X1
      else classicalSample

/-- Positive geometric level law, 2308.01582 pp.10–12 Eq.(7):
J=1+J0, where J0 has geometric failure count at p=1/2. -/
def positiveGeometricLaw : Measure ℕ :=
  (ProbabilityTheory.geometricMeasure ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩).map (fun j : ℕ => j + 1)

/-- Independent three-run multilevel estimator, 2308.01582 p.10 Algorithm 2.
There is no maximum geometric level and no assumed unbiasedness. For L=0
a fresh sample recovers the possibly nonzero deterministic mean. For L>0
the three-run Algorithm-2 schedule is retained, including sigma=L. -/
def quantumVarianceReduction {d : ℕ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : QuantumMeanEstimationProgram d H)
    (L sigma : ℝ) : ContinuousOracleProgram d H :=
  if L < 0 ∨ sigma ≤ 0 then .diverge
  else if L = 0 then classicalSample
  else .bind (quantumMeanEstimationPlus M L (sigma / 10)) fun v0 =>
    .naturalDraw positiveGeometricLaw (by
      unfold positiveGeometricLaw
      exact Measure.isProbabilityMeasure_map (by fun_prop)) fun j =>
      .bind (quantumMeanEstimationPlus M L ((2 : ℝ) ^ (-(3 : ℝ) * j / 4) * sigma / 10)) fun vj =>
        .bind (quantumMeanEstimationPlus M L
          ((2 : ℝ) ^ (-(3 : ℝ) * (j - 1 : ℕ) / 4) * sigma / 10)) fun vprev =>
            .output (v0 + (2 : ℝ) ^ j • (vj - vprev))

/-- Sanity check for the modeled source objects (arxiv-2308.01582v2, PDF pp.8,9,10,11,12). -/
example {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : QuantumMeanEstimationProgram d H) (sigma : ℝ) :
    quantumMeanEstimationPlus M (-1) sigma = .diverge := by
  simp [quantumMeanEstimationPlus]

/-- Zero-variance boundary of 2308.01582 p.8 Problem 3 and pp.9–10. -/
example {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : QuantumMeanEstimationProgram d H) (sigma : ℝ) (hs : 0 < sigma) :
    quantumVarianceReduction M 0 sigma = classicalSample := by
  simp [quantumVarianceReduction,not_le.mpr hs]

end QAlgorithms.StochasticOptimization


