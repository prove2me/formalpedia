-- Prove2me | Definitions.Def_ZhangJasinPricing_Cyclic_Analysis
-- name    : ZhangJasinPricing_Cyclic_Analysis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T07:00:09.211299+00:00
-- url     : https://prove2.me/theorems/38ce95c6-d713-4856-91fc-04446f7c8773
-- title:
--   Episode events, cycles begun, and undersampled periods
-- statement:
--   The number of parameters is A=M+M(M−1)K/2. At an episode snapshot, the confidence radius for a parameter is √(8 log n(e,c)/q). The event G is exactly the intersection of every outside-interval event, across both parameter families. An episode's joint event with n(e,c)=m includes the requirement that this episode actually occurs; nonexistent episodes do not receive invented snapshots. Snapshots are indexed from one and n(e,c) includes the initial pseudo-count one.
--
--   The horizon cycle count includes any partially played last cycle but excludes the initial pseudo-count. An episode is undersampled if at its start some parameter used by its word has count less than 32 log N/ε². The counted periods are actual word-playing periods of such episodes within the horizon. Initialization and inter-episode clearing periods are accounted for separately in the source and do not belong to these episodes. All quantities are read from the actual OLT recursion.
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, §§3–6, p. 23 (PDF p. 23)

import Definitions.Def_ZhangJasinPricing_Cyclic_Learning
open MeasureTheory
open scoped BigOperators ENNReal
open scoped Classical
noncomputable section

namespace ZhangJasinPricing.Cyclic

def parameterNumber (M K : ℕ) : ℝ := M + (M : ℝ)*(M-1)*K/2

def radius (e : Episode) (a : Parameter) : ℝ :=
  Real.sqrt (8 * Real.log e.cycleCounter / e.counts a)

/-- Printed intersection of failures, not a union. -/
def allFailures {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (e : Episode) : Prop :=
  ∀ a ∈ parameters D.M D.K,
    e.averages a ∉ Set.Icc (parameterMean D a - radius e a) (parameterMean D a + radius e a)

/-- Retrieve episode e (one-based), without inventing a nonexistent episode. -/
def IsEpisode {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode)
    (init : Initialization D.M D.K) (tie : TieRule) (ω : Ω) (e : ℕ) (ep : Episode) : Prop :=
  1 ≤ e ∧ ∃ t, (run D mode init tie ω t).episodes[e-1]? = some ep

def failureAtCycle {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (init : Initialization D.M D.K) (tie : TieRule) (e m : ℕ) : Set Ω :=
  {ω | ∃ ep, IsEpisode D .threshold init tie ω e ep ∧
    allFailures D ep ∧ ep.cycleCounter = m}

/-- Count cycles begun, including an incomplete last cycle; the internal
cycle counter begins at one and advances only when a cycle is completed. -/
def cyclesBegun {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode)
    (init : Initialization D.M D.K) (tie : TieRule) (ω : Ω) (T : ℕ) : ℕ :=
  let s := run D mode init tie ω T
  (s.cycles-1) + if 0 < s.offset then 1 else 0

def smallCounts (K : ℕ) (p : ℕ → ℝ) (e : Episode) (N : ℕ) (ε : ℝ) : Prop :=
  ∃ a ∈ usedParameters .threshold K p e.word,
    (e.counts a : ℝ) < 32 * Real.log N / ε^2

/-- Periods actually spent playing the selected word in undersampled episodes.
Initialization and inter-episode clearing are not within an episode. -/
def undersampledPeriods {Ω : Type} [MeasurableSpace Ω] (D : Model Ω)
    (init : Initialization D.M D.K) (tie : TieRule) (ω : Ω) (T : ℕ) (ε : ℝ) : ℕ :=
  ((Finset.range T).filter (fun t =>
    let s := run D .threshold init tie ω (t+1)
    ∃ ep, s.episodes.getLast? = some ep ∧ ep.start ≤ t ∧
      ¬ s.afterClearing ∧ smallCounts D.K D.price ep
        (cyclesBegun D .threshold init tie ω T) ε)).card

end ZhangJasinPricing.Cyclic


