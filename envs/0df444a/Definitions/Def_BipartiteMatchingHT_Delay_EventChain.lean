-- Prove2me | Definitions.Def_BipartiteMatchingHT_Delay_EventChain
-- name    : BipartiteMatchingHT_Delay_EventChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:11:16.861595+00:00
-- url     : https://prove2.me/theorems/5840cec3-75d1-4cbc-b8a9-3be5ce83ba14
-- title:
--   Poisson event chains and extended hitting-time means
-- statement:
--   A finite set of event clocks with nonnegative real rates and positive total rate acts on an arbitrary state space through a deterministic event update. Independent Poisson clocks are equivalently represented by a rate-$R$ Poisson clock whose independent marks have probabilities $r_e/R$. Null events are permitted, so the state space can be countably infinite while the total event rate stays bounded. The transition probabilities are the Poisson mixture of the recursively defined event-chain iterates.
--
--   Stationarity uses the published countable-state probability-vector definition, applied to the event transition kernel. For a target set $A$, the survival recursion checks the initial state and each subsequent event, stopping on the first visit to $A$. Its nonnegative tail sum divided by $R$ is the expected continuous time to hit $A$, in $[0,\infty]$. No stationary distribution, finiteness of the hitting mean, or queueing identity is assumed. This general event-clock object is separate from the paper-specific queue.
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; printed/PDF pp. 2, 7; operational encoding

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsStationaryProb

open scoped BigOperators ENNReal
noncomputable section

namespace BipartiteMatchingHT.Delay

/-- A finite collection of independent Poisson event clocks acting on an arbitrary
state space. Null events are allowed. The state space need not be finite. -/
structure EventChain (S E : Type) [Fintype E] where
  rate : E → ℝ
  nonneg : ∀ e, 0 ≤ rate e
  total_pos : 0 < ∑ e, rate e
  step : S → E → S

namespace EventChain
variable {S E : Type} [Fintype E]

def total (C : EventChain S E) : ℝ := ∑ e, C.rate e

def weight (C : EventChain S E) (e : E) : ℝ≥0∞ :=
  ENNReal.ofReal (C.rate e / C.total)

def kernel (C : EventChain S E) (x y : S) : ℝ≥0∞ := by
  classical
  exact ∑ e, if C.step x e = y then C.weight e else 0

/-- Distribution after n events, including null events. -/
def iterate (C : EventChain S E) : ℕ → S → S → ℝ≥0∞
  | 0, x, y => by classical exact if x = y then 1 else 0
  | n + 1, x, y => ∑ e, C.weight e * C.iterate n (C.step x e) y

/-- The continuous-time transition probabilities: Poisson randomization of the
event chain. This specifies the process without assuming its stationary laws. -/
def transition (C : EventChain S E) (t : ℝ) (x y : S) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal
    (Real.exp (-(C.total * t)) * (C.total * t) ^ n / (n.factorial : ℝ)) *
    C.iterate n x y

/-- Survival through n events before hitting A; the initial state is checked too. -/
def survival (C : EventChain S E) (A : S → Prop) : ℕ → S → ℝ≥0∞
  | 0, x => by classical exact if A x then 0 else 1
  | n + 1, x => by
    classical
    exact if A x then 0 else ∑ e, C.weight e * C.survival A n (C.step x e)

/-- Expected continuous time to hit A. Each event interval has independent
exponential mean 1/total; the tail sum allows infinite waiting times. -/
def meanHitting (C : EventChain S E) (A : S → Prop) (x : S) : ℝ≥0∞ :=
  (∑' n : ℕ, C.survival A n x) / ENNReal.ofReal C.total

def IsStationary (C : EventChain S E) (p : S → ℝ≥0∞) : Prop :=
  KellyRSN.PartialBalance.IsStationaryProb C.kernel p

end EventChain
end BipartiteMatchingHT.Delay


