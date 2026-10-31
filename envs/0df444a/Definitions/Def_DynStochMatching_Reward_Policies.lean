-- Prove2me | Definitions.Def_DynStochMatching_Reward_Policies
-- name    : DynStochMatching_Reward_Policies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T20:38:35.844039+00:00
-- url     : https://prove2.me/theorems/c7281820-fe0f-4388-a060-8eee26b61b7c
-- title:
--   Observable matching policies and average objectives
-- statement:
--   A policy specifies an extended nonnegative stopping time, up to null events, for every ordered pair of distinct agent identities; infinity means no match. Its filtration observes arrived types and arrival times, departures only after they occur, and independent private coins. Feasibility requires both endpoints to be present and prohibits any reuse. Immediate agents are available at their arrival decision. Nonnegative sums of positive and negative reward parts give expected cumulative reward; the long-run objective is its liminf per unit time. The optimum is the supremum over all admissible policies. Costs and abandonment penalties are extended nonnegative values, and their average objective is a limsup. No trajectory, reward bound, or optimal policy is supplied as an input field.
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, §2 and §5, printed 8–10, 20 / PDF 9–11, 21

import Definitions.Def_DynStochMatching_Reward_MarkedInput

open MeasureTheory Filter
open scoped ENNReal Classical

namespace DynStochMatching.Reward

/-- The complete observable arrival/departure history at time t, with independent private coins.
Unrealized sojourn lengths are not part of this observation. -/
noncomputable def observation {n : ℕ} (D : Instance n) (t : ℝ) (ω : RandomSeeds) :=
  ((fun k : ℕ => if arrivalTime D.toMarkedPoissonData ω k ≤ t then
    (true, arrivalTime D.toMarkedPoissonData ω k,
      (arrivalType D.toMarkedPoissonData ω k).map Fin.val |>.getD n)
    else (false, (0 : ℝ), n)),
   (fun k : ℕ => if departureTime D ω k ≤ t then (true, departureTime D ω k)
    else (false, (0 : ℝ))),
   (fun k : ℕ × ℕ => ω (k.1, k.2 + 3)))

@[instance_reducible]
noncomputable def observableSpace {n : ℕ} (D : Instance n) (t : ℝ) : MeasurableSpace RandomSeeds :=
  MeasurableSpace.comap (observation D t) inferInstance

/-- A matching policy assigns a stopping time to each pair of agent identities; infinity means
that the pair is never matched. The smaller identity is always the first endpoint. -/
abbrev MatchingPolicy := (ℕ × ℕ) → RandomSeeds → ℝ≥0∞

noncomputable def present {n : ℕ} (D : Instance n) (ω : RandomSeeds)
    (t : ℝ) (k : ℕ) : Prop :=
  0 ≤ t ∧ arrivalTime D.toMarkedPoissonData ω k ≤ t ∧
    ∃ i, arrivalType D.toMarkedPoissonData ω k = some i ∧
      (t < departureTime D ω k ∨
        (D.lifetime i = Lifetime.immediate ∧ t = arrivalTime D.toMarkedPoissonData ω k))

def sharesAgent (e f : ℕ × ℕ) : Prop :=
  e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2

/-- Feasibility forbids matching an agent twice, including at two different times. -/
noncomputable def feasiblePath {n : ℕ} (D : Instance n) (π : MatchingPolicy)
    (ω : RandomSeeds) : Prop :=
  (∀ e, π e ω ≠ ⊤ → e.1 < e.2 ∧
    present D ω (π e ω).toReal e.1 ∧ present D ω (π e ω).toReal e.2) ∧
  (∀ e f, π e ω ≠ ⊤ → π f ω ≠ ⊤ → sharesAgent e f → e = f)

/-- Nonanticipation is the stopping-time property up to null events in the observable
history filtration. The canonical real seed space includes impossible paths (negative
exponential seeds, for example); changing a policy on those paths changes no decision law. -/
noncomputable def admissible {n : ℕ} (D : Instance n) (π : MatchingPolicy) : Prop :=
  (∀ e, Measurable (π e)) ∧
  (∀ e t, 0 ≤ t → ∃ A : Set RandomSeeds,
    @MeasurableSet RandomSeeds (observableSpace D t) A ∧
      ∀ᵐ ω ∂seedLaw, (ω ∈ A ↔ π e ω ≤ ENNReal.ofReal t)) ∧
  (∀ᵐ ω ∂seedLaw, feasiblePath D π ω)

noncomputable def pairReward {n : ℕ} (D : Instance n) (ω : RandomSeeds)
    (e : ℕ × ℕ) : ℝ :=
  match arrivalType D.toMarkedPoissonData ω e.1, arrivalType D.toMarkedPoissonData ω e.2 with
  | some i, some j => D.reward i j
  | _, _ => 0

/-- Nonnegative sums avoid a real infinite-series default value on exceptional paths. -/
noncomputable def accumulatedRewardPart {n : ℕ} (D : Instance n) (π : MatchingPolicy)
    (positive : Bool) (t : ℝ) (ω : RandomSeeds) : ℝ≥0∞ :=
  ∑' e : ℕ × ℕ, if e.1 < e.2 ∧ π e ω ≠ ⊤ ∧ π e ω ≤ ENNReal.ofReal t then
    ENNReal.ofReal (if positive then pairReward D ω e else -pairReward D ω e) else 0

noncomputable def expectedReward {n : ℕ} (D : Instance n) (π : MatchingPolicy) (t : ℝ) : EReal :=
  (∫⁻ ω, accumulatedRewardPart D π true t ω ∂seedLaw).toEReal -
  (∫⁻ ω, accumulatedRewardPart D π false t ω ∂seedLaw).toEReal

noncomputable def averageReward {n : ℕ} (D : Instance n) (π : MatchingPolicy) : EReal :=
  Filter.liminf (fun t : ℝ => (t⁻¹ : ℝ) * expectedReward D π t) Filter.atTop

/-- The optimum is derived from all observable feasible policies, never supplied as data. -/
noncomputable def optimalReward {n : ℕ} (D : Instance n) : EReal :=
  ⨆ π : {π : MatchingPolicy // admissible D π}, averageReward D π.val

/-- Extended nonnegative edge costs include forbidden matches. -/
structure Costs (n : ℕ) where
  edge : Fin n → Fin n → ℝ≥0∞
  abandonment : Fin n → ℝ≥0∞
  symmetric : ∀ i j, edge i j = edge j i

noncomputable def unmatchedAt (π : MatchingPolicy) (ω : RandomSeeds) (k : ℕ)
    (t : ℝ) : Prop :=
  ∀ e, e.1 = k ∨ e.2 = k → π e ω = ⊤ ∨ ENNReal.ofReal t < π e ω

noncomputable def accumulatedCost {n : ℕ} (D : Instance n) (C : Costs n)
    (π : MatchingPolicy) (t : ℝ) (ω : RandomSeeds) : ℝ≥0∞ :=
  (∑' e : ℕ × ℕ, if e.1 < e.2 ∧ π e ω ≠ ⊤ ∧ π e ω ≤ ENNReal.ofReal t then
    match arrivalType D.toMarkedPoissonData ω e.1, arrivalType D.toMarkedPoissonData ω e.2 with
    | some i, some j => C.edge i j
    | _, _ => 0
   else 0) +
  ∑' k : ℕ, if departureTime D ω k ≤ t ∧ unmatchedAt π ω k (departureTime D ω k) then
    match arrivalType D.toMarkedPoissonData ω k with
    | some i => C.abandonment i
    | none => 0
   else 0

noncomputable def averageCost {n : ℕ} (D : Instance n) (C : Costs n)
    (π : MatchingPolicy) : ℝ≥0∞ :=
  Filter.limsup (fun t : ℝ => (∫⁻ ω, accumulatedCost D C π t ω ∂seedLaw) /
    ENNReal.ofReal t) Filter.atTop

noncomputable def optimalCost {n : ℕ} (D : Instance n) (C : Costs n) : ℝ≥0∞ :=
  ⨅ π : {π : MatchingPolicy // admissible D π}, averageCost D C π.val

end DynStochMatching.Reward


