-- Prove2me | Definitions.Def_DynStochMatching_Reward_Poisson
-- name    : DynStochMatching_Reward_Poisson
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T20:37:05.512+00:00
-- url     : https://prove2.me/theorems/2f41ecb9-daa1-409a-993e-1b5f4b970522
-- title:
--   Independent marked Poisson arrivals
-- statement:
--   Independent rate-one exponential seeds on a countable product probability space generate superposed Poisson arrival gaps and categorical type marks with probabilities proportional to their positive arrival rates. Extra independent coordinates supply private randomization. The categorical inverse CDF has an explicit fallback outside its probability domain. This is a general marked-arrival object, independent of matching.
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, §2, printed 8–9 / PDF 9–10

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DynStochMatching.Reward

/-- Independent exponential seeds. Coordinate blocks supply independent randomization. -/
abbrev RandomSeeds := (ℕ × ℕ) → ℝ

noncomputable def seedLaw : Measure RandomSeeds := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  exact Measure.infinitePi (fun _ : ℕ × ℕ => expMeasure 1)

/-- A marked Poisson stream, separate from any matching or control model. -/
structure MarkedPoissonData (n : ℕ) where
  arrivalRate : Fin n → ℝ
  positive : ∀ i, 0 < arrivalRate i

noncomputable def totalArrivalRate {n : ℕ} (D : MarkedPoissonData n) : ℝ :=
  ∑ i, D.arrivalRate i

noncomputable def arrivalTime {n : ℕ} (D : MarkedPoissonData n)
    (ω : RandomSeeds) (k : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (k + 1), ω (q, 0) / totalArrivalRate D

/-- Inverse categorical CDF, with an explicit branch outside its probability domain. -/
noncomputable def categorical (n : ℕ) (p : Fin n → ℝ) (u : ℝ) : Option (Fin n) := by
  classical
  exact ((List.finRange n).find? fun i =>
    u < ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ i), p j)

noncomputable def arrivalType {n : ℕ} (D : MarkedPoissonData n)
    (ω : RandomSeeds) (k : ℕ) : Option (Fin n) :=
  categorical n (fun i => D.arrivalRate i / totalArrivalRate D) (Real.exp (-ω (k, 1)))

end DynStochMatching.Reward


