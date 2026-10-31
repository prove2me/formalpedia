-- Prove2me | Definitions.Def_DynStochMatching_Reward_MarkedInput
-- name    : DynStochMatching_Reward_MarkedInput
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T20:37:48.810993+00:00
-- url     : https://prove2.me/theorems/05822bd4-37ce-43f1-bd8f-1734a4d3c144
-- title:
--   Matching instance and departure regimes
-- statement:
--   A finite type graph has arbitrary real symmetric rewards and strictly positive arrival rates. Each type has either a positive finite exponential lifetime rate or immediate departure after its arrival decision. Self-loops are type-level rewards for two distinct agents. Bipartitions require every nonzero reward edge to cross. Asymmetric instances have one immediate side and one finite-lifetime side. The empty type graph is also representable; its rewards and flows are zero.
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, §2 and §5, printed 8–10, 20–21 / PDF 9–11, 21–22

import Definitions.Def_DynStochMatching_Reward_Poisson

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DynStochMatching.Reward

/-- Immediate departure is an arrival decision, not an infinite exponential parameter. -/
inductive Lifetime where
  | exponential (rate : ℝ) (positive : 0 < rate)
  | immediate

noncomputable def lifetimeDuration (l : Lifetime) (seed : ℝ) : ℝ :=
  match l with
  | .exponential rate _ => seed / rate
  | .immediate => 0

/-- Finite type data; agent populations and time remain unbounded. -/
structure Instance (n : ℕ) extends MarkedPoissonData n where
  lifetime : Fin n → Lifetime
  reward : Fin n → Fin n → ℝ
  symmetric : ∀ i j, reward i j = reward j i

noncomputable def departureTime {n : ℕ} (D : Instance n)
    (ω : RandomSeeds) (k : ℕ) : ℝ :=
  arrivalTime D.toMarkedPoissonData ω k +
    match arrivalType D.toMarkedPoissonData ω k with
    | some i => lifetimeDuration (D.lifetime i) (ω (k, 2))
    | none => 0

/-- Positive finite lifetimes, the ordinary regime of Sections 2 and 5. -/
def IsOrdinary {n : ℕ} (D : Instance n) : Prop :=
  ∀ i, ∃ μ hμ, D.lifetime i = Lifetime.exponential μ hμ

/-- A partition is represented by its first side. -/
def IsBipartition {n : ℕ} (D : Instance n) (side : Fin n → Bool) : Prop :=
  ∀ i j, D.reward i j ≠ 0 → side i ≠ side j

/-- The false side departs immediately; the true side has positive finite lifetimes. -/
def IsAsymmetric {n : ℕ} (D : Instance n) (side : Fin n → Bool) : Prop :=
  IsBipartition D side ∧ ∀ i,
    (side i = false → D.lifetime i = Lifetime.immediate) ∧
    (side i = true → ∃ μ hμ, D.lifetime i = Lifetime.exponential μ hμ)

end DynStochMatching.Reward


