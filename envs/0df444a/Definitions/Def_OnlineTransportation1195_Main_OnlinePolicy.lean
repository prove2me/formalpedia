-- Prove2me | Definitions.Def_OnlineTransportation1195_Main_OnlinePolicy
-- name    : OnlineTransportation1195_Main_OnlinePolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:35:11.424892+00:00
-- url     : https://prove2.me/theorems/89585763-2efc-499d-acbd-9e8f8e66a9e3
-- title:
--   Deterministic causal policies and multiplicative competitive guarantees
-- statement:
--   For a fixed static instance $I$, a rule $A$ maps every complete arrival sequence to a feasible slot assignment. It is causal if equal arrival prefixes through time $t$ give the same assigned garage at time $t$. Consequently a garage decision can be made at arrival and is irrevocable, even though the function is represented using complete sequences. The rule is selected before quantifying over sequences.
--
--   Its competitive guarantee is
--
--   $$\forall v,\quad \operatorname{cost}(v,A(v))\le\rho\operatorname{OPT}(v).$$
--
--   There is no additive term and no division by OPT. The point-count predicate quantifies over every static instance with $n$ points and asks for a single causal rule on all its arrivals. The garage-count predicate uses the number of garages in each instance. Competitive factors are nonnegative, including trivial zero-capacity instances. No correctness bound is a field required to instantiate a policy; causality and competitiveness are separate predicates.
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), §1 competitive ratio and §4 online assignments, PDF / printed p. 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_Transportation

namespace OnlineTransportation1195.Main

open TransportationInstance

/-- A rule is selected before the arrivals are quantified. It becomes an online
algorithm only after satisfying IsCausal, which says nothing about its cost. -/
abbrev Policy {n : ℕ} (I : TransportationInstance n) := I.Arrivals → I.Assignment

/-- Equal revealed prefixes produce the same irrevocable garage decision.
Slot names are internal; only the actual assigned garage must be causal. -/
def IsCausal {n : ℕ} (I : TransportationInstance n) (A : Policy I) : Prop :=
  ∀ r q t, (∀ j, j ≤ t → r j = q j) → I.garageOf (A r) t = I.garageOf (A q) t

/-- Pure multiplicative competitiveness, including sequences with zero optimum. -/
def Competitive {n : ℕ} (I : TransportationInstance n) (A : Policy I) (ρ : ℝ) : Prop :=
  ∀ r, I.cost r (A r) ≤ ρ * I.opt r

/-- A nonnegative competitive factor on every n-point static instance. -/
def PointRatio (n : ℕ) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ ∀ I : TransportationInstance n,
    ∃ A : Policy I, IsCausal I A ∧ Competitive I A ρ

/-- A nonnegative garage-count factor, on all finite metrics and garage subsets. -/
def GarageRatios (f : ℕ → ℝ) : Prop :=
  (∀ m, 0 ≤ f m) ∧ ∀ n (I : TransportationInstance n),
    ∃ A : Policy I, IsCausal I A ∧ Competitive I A (f I.garages.card)

end OnlineTransportation1195.Main


