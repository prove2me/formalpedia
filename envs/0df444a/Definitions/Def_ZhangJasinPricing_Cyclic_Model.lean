-- Prove2me | Definitions.Def_ZhangJasinPricing_Cyclic_Model
-- name    : ZhangJasinPricing_Cyclic_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T06:56:55.562238+00:00
-- url     : https://prove2.me/theorems/495620dc-b684-4d92-9f5a-b229aabafd41
-- title:
--   Patient customer cohorts, operational demand, and revenue normalization
-- statement:
--   There are M≥2 strictly ordered nonnegative feasible prices and patience values 0,…,K with K≥1. On an arbitrary measurable probability space, nonnegative real cohort amounts have finite, time-independent means and finite centered second moments. No independence is imposed. Demand sums all currently eligible cohorts that have not purchased at any earlier eligible time; revenue is posted price times that demand. The system starts empty. The price index, valuation-bin index, and calendar time are zero-based. The final valuation bin is retained in the model but never contributes positive revenue. The source's zero marginal cost and unlimited inventory are built into the revenue formula.
--
--   The parameter set consists of single-price parameters and strict price-drop parameters with memory 1,…,K. Each parameter's random realization is the operational revenue from its prescribed experiment, and its mean is its expectation. The transition backlog includes the most recent prior cohort, reading the p. 9 display in accordance with equation (1); see I3. Assumption 1 uses the published extended nonnegative ψ₂ norm, bounded by one on every calendar translate of these revenue experiments, and finite ψ₂ norm on the centered errors. Integrability is part of the imported norm's admissibility condition. This uses the source's revenue-realization normalization, not an MGF proxy or an independence assumption.
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, §§3–6, p. 6 (PDF p. 6)

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
open MeasureTheory
open scoped BigOperators ENNReal
open scoped Classical
noncomputable section

namespace ZhangJasinPricing.Cyclic
/-- Prices and cohort data, with zero-based feasible prices and valuation bins.
Bin M is the nonbuying bin; time is zero-based, patience is 0,...,K. -/
structure Model (Ω : Type) [MeasurableSpace Ω] where
  M : ℕ
  K : ℕ
  M_ge : 2 ≤ M
  K_ge : 1 ≤ K
  price : ℕ → ℝ
  price_nonneg : ∀ i, i < M → 0 ≤ price i
  price_order : ∀ i j, i < j → j < M → price j < price i
  law : Measure Ω
  probability : IsProbabilityMeasure law
  cohort : ℕ → ℕ → ℕ → Ω → ℝ
  mean : ℕ → ℕ → ℝ
  nonneg : ∀ t i k ω, i ≤ M → k ≤ K → 0 ≤ cohort t i k ω
  measurable : ∀ t i k, i ≤ M → k ≤ K → Measurable (cohort t i k)
  integrable : ∀ t i k, i ≤ M → k ≤ K → Integrable (cohort t i k) law
  mean_eq : ∀ t i k, i ≤ M → k ≤ K → (∫ ω, cohort t i k ω ∂law) = mean i k
  variance_finite : ∀ t i k, i ≤ M → k ≤ K →
    Integrable (fun ω => (cohort t i k ω - mean i k)^2) law
/-- Equation (1), including every still-patient cohort that has not bought earlier. -/
def demand {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (C : ℕ → ℕ → ℕ → ℝ) (prices : ℕ → ℕ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (D.K + 1), ∑ s ∈ Finset.Icc (t-k) t,
    ∑ a ∈ Finset.range D.M,
      if a ≤ prices t ∧ (∀ u ∈ Finset.Ico s t, D.price a < D.price (prices u))
      then C s a k else 0

def revenue {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (prices : ℕ → ℕ) (t : ℕ) (ω : Ω) : ℝ :=
  D.price (prices t) * demand D (fun s a k => D.cohort s a k ω) prices t

abbrev Parameter := ℕ × ℕ × ℕ
/-- (i,i,0) denotes r_i; (i,j,l), i<j and 1≤l≤K, denotes a drop. -/
def parameters (M K : ℕ) : Finset Parameter :=
  ((Finset.range M).image (fun i => (i,i,0))) ∪
  (((Finset.range M) ×ˢ (Finset.range M) ×ˢ (Finset.Icc 1 K)).filter
    (fun a => a.1 < a.2.1))

def experiment {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (a : Parameter) (start : ℕ) (ω : Ω) : ℝ :=
  if a.1 = a.2.1 then
    D.price a.1 * ∑ i ∈ Finset.range (a.1+1), ∑ k ∈ Finset.range (D.K+1),
      D.cohort start i k ω
  else
    D.price a.2.1 * ((∑ k ∈ Finset.Icc 1 D.K,
      ∑ s ∈ Finset.Icc (a.2.2-k) (a.2.2-1),
        ∑ i ∈ Finset.Icc (a.1+1) a.2.1, D.cohort (start+s) i k ω) +
      ∑ i ∈ Finset.range (a.2.1+1), ∑ k ∈ Finset.range (D.K+1),
        D.cohort (start+a.2.2) i k ω)

def parameterMean {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (a : Parameter) : ℝ :=
  ∫ ω, experiment D a 0 ω ∂D.law

/-- Assumption 1 on all calendar translates of the revenue experiment;
centering is explicit, with no independence or conditional-mean requirement. -/
def Assumption1 {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) : Prop :=
  ∀ a ∈ parameters D.M D.K, ∀ s,
    HighDimProb.Concentration.subgaussianNorm D.law (experiment D a s) ≤ 1 ∧
    HighDimProb.Concentration.subgaussianNorm D.law
      (fun ω => experiment D a s ω - parameterMean D a) < ⊤
end ZhangJasinPricing.Cyclic


