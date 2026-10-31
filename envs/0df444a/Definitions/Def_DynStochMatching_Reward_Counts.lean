-- Prove2me | Definitions.Def_DynStochMatching_Reward_Counts
-- name    : DynStochMatching_Reward_Counts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T20:39:25.192999+00:00
-- url     : https://prove2.me/theorems/4ac566e1-ed37-4f9c-a8f8-4b04d374a7b3
-- title:
--   Epoch counts and stationary observable policies
-- statement:
--   Arrival/departure epochs are ordered from the full marked sojourn process. Ordinary match counts count pairs actually matched by deterministic time; modified counts include every eventual match whose two endpoints arrived by the selected epoch. Expected rates and the random epoch denominator remain distinct. Stationarity is a fixed rule on the ordered list of available types, with no time, future lifetime or absolute agent identity as an input; this includes count-state stationary rules with fixed tie-breaking and additionally permits inspection of relative arrival order.
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, §3 and A.2, printed 11–12, 36 / PDF 12–13, 37

import Definitions.Def_DynStochMatching_Reward_Policies

open MeasureTheory Filter
open scoped Classical ENNReal

namespace DynStochMatching.Reward

noncomputable def externalEpochs {n : ℕ} (D : Instance n) (ω : RandomSeeds) : Set ℝ≥0∞ :=
  Set.range (fun k => ENNReal.ofReal (arrivalTime D.toMarkedPoissonData ω k)) ∪
  Set.range (fun k => ENNReal.ofReal (departureTime D ω k))

noncomputable def epoch {n : ℕ} (D : Instance n) (ω : RandomSeeds) : ℕ → ℝ≥0∞
  | 0 => sInf (externalEpochs D ω)
  | q + 1 => sInf {t | t ∈ externalEpochs D ω ∧ epoch D ω q < t}

noncomputable def typedPair {n : ℕ} (D : Instance n) (ω : RandomSeeds)
    (e : ℕ × ℕ) (i j : Fin n) : Prop :=
  e.1 < e.2 ∧ arrivalType D.toMarkedPoissonData ω e.1 = some i ∧
    arrivalType D.toMarkedPoissonData ω e.2 = some j

noncomputable def matchCount {n : ℕ} (D : Instance n) (π : MatchingPolicy)
    (i j : Fin n) (t : ℝ) (ω : RandomSeeds) : ℝ≥0∞ :=
  ∑' e, if typedPair D ω e i j ∧ π e ω ≠ ⊤ ∧ π e ω ≤ ENNReal.ofReal t then 1 else 0

noncomputable def modifiedCount {n : ℕ} (D : Instance n) (π : MatchingPolicy)
    (i j : Fin n) (q : ℕ) (ω : RandomSeeds) : ℝ≥0∞ :=
  ∑' e, if typedPair D ω e i j ∧ π e ω ≠ ⊤ ∧
    ENNReal.ofReal (arrivalTime D.toMarkedPoissonData ω e.2) ≤ epoch D ω q then 1 else 0

noncomputable def expectedMatchCount {n : ℕ} (D : Instance n) (π : MatchingPolicy)
    (i j : Fin n) (t : ℝ) : ℝ :=
  (∫⁻ ω, matchCount D π i j t ω ∂seedLaw).toReal

noncomputable def expectedModifiedCount {n : ℕ} (D : Instance n) (π : MatchingPolicy)
    (i j : Fin n) (q : ℕ) : ℝ :=
  (∫⁻ ω, modifiedCount D π i j q ω ∂seedLaw).toReal

noncomputable def rateOfMatches {n : ℕ} (D : Instance n) (π : MatchingPolicy)
    (i j : Fin n) : ℝ :=
  Filter.liminf (fun t : ℝ => expectedMatchCount D π i j t / t) Filter.atTop

noncomputable def populationBefore {n : ℕ} (D : Instance n) (π : MatchingPolicy)
    (ω : RandomSeeds) (t : ℝ) (i : Fin n) : ℕ :=
  ∑' k : ℕ, if present D ω t k ∧ arrivalType D.toMarkedPoissonData ω k = some i ∧
    (∀ e, e.1 = k ∨ e.2 = k → ENNReal.ofReal t ≤ π e ω) then 1 else 0

noncomputable def actionCounts {n : ℕ} (D : Instance n) (π : MatchingPolicy)
    (ω : RandomSeeds) (t : ℝ) (i j : Fin n) : ℕ :=
  ∑' e, if e.1 < e.2 ∧ π e ω = ENNReal.ofReal t ∧
    ((arrivalType D.toMarkedPoissonData ω e.1 = some i ∧
      arrivalType D.toMarkedPoissonData ω e.2 = some j) ∨
     (arrivalType D.toMarkedPoissonData ω e.1 = some j ∧
      arrivalType D.toMarkedPoissonData ω e.2 = some i)) then 1 else 0

noncomputable def arrivalCutoff {n : ℕ} (D : Instance n) (ω : RandomSeeds) (t : ℝ) : ℕ :=
  if h : ∃ k, t < arrivalTime D.toMarkedPoissonData ω k then Nat.find h else 0

noncomputable def availableBefore {n : ℕ} (D : Instance n) (π : MatchingPolicy)
    (ω : RandomSeeds) (t : ℝ) : List ℕ :=
  (List.range (arrivalCutoff D ω t)).filter fun k => present D ω t k ∧
    (∀ e, e.1 = k ∨ e.2 = k → ENNReal.ofReal t ≤ π e ω)

/-- Stationarity on the finite ordered list of currently available types. This includes the
source's count-state stationary rules with a fixed identity tie rule, and also allows a fixed
rule to inspect arrival order. Neither time, future lifetimes nor absolute agent IDs is an input. -/
noncomputable def stationary {n : ℕ} (D : Instance n) (π : MatchingPolicy) : Prop :=
  (∃ rule : List (Fin n) → Finset (ℕ × ℕ),
    ∀ᵐ ω ∂seedLaw, ∀ q, epoch D ω q ≠ ⊤ →
      let t := (epoch D ω q).toReal
      let agents := availableBefore D π ω t
      let types := agents.filterMap (arrivalType D.toMarkedPoissonData ω)
      ∀ e, π e ω = epoch D ω q ↔ ∃ a ∈ rule types,
        agents[a.1]? = some e.1 ∧ agents[a.2]? = some e.2) ∧
  (∀ᵐ ω ∂seedLaw, ∀ e, π e ω ≠ ⊤ → π e ω ∈ externalEpochs D ω)

end DynStochMatching.Reward


