-- Prove2me | Definitions.Def_MatchingDelays_Linear_Instance
-- name    : MatchingDelays_Linear_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:49.04376+00:00
-- url     : https://prove2.me/theorems/2aadc193-a72d-4102-95f9-157edd2c353b
-- title:
--   Requests, schedules, and independent offline optima
-- statement:
--   Let $n\ge2$ be even. Requests have locations $x_u$ in an arbitrary metric space $(X,d_0)$ and finite nonnegative arrival times $a_u$. Labels are assigned in arrival order, with a fixed order for simultaneous arrivals. An unordered edge is stored once with increasing endpoint labels. A perfect pairing covers every request exactly once. A schedule assigns each paired edge a finite time $T_{uv}\ge\max(a_u,a_v)$ and has cost
--   $$\sum_{uv\in M}\bigl[d_0(x_u,x_v)+(T_{uv}-a_u)+(T_{uv}-a_v)\bigr].$$
--   The time-expanded request distance is $d(u,v)=d_0(x_u,x_v)+|a_u-a_v|$. The timed offline optimum is the infimum of feasible schedule costs; the independently defined pairing optimum is the infimum of perfect-pairing weights $\sum d(u,v)$. Their equality and attainment are theorem targets, not definitions.
--
--   These definitions preserve repeated locations and simultaneous arrivals. The ambient metric may be infinite or unbounded. **Formalization Note** Labels outside the analysis range have zero auxiliary arrival and distance values and never enter a valid schedule. The infima are used only for valid even sizes, where the first milestone asserts nonemptiness, boundedness and attainment.
-- source:
--   Ahmadian, Chawla, Kumar, Purohit, and Zhang, STOC 2027 submission #482 (October 2026), §2, printed p.5 / PDF p.6, Eq. (1) and the schedule objective. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/482.pdf

import Mathlib

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace MatchingDelays.Linear


/-- Section 2: arrival-ranked requests in an arbitrary ambient metric space.
Sorting labels is an encoding; simultaneous arrivals retain any fixed order. -/
structure Instance (n : ℕ) (X : Type*) [MetricSpace X] where
  location : Fin n → X
  arrival : Fin n → ℝ
  nonnegative : ∀ u, 0 ≤ arrival u
  ranked : Monotone arrival

def ValidSize (n : ℕ) : Prop := 2 ≤ n ∧ Even n

abbrev Edge := ℕ × ℕ

def edge (u v : ℕ) : Edge := (min u v, max u v)
def endpoints (e : Edge) : Finset ℕ := {e.1, e.2}
def allPairs (V : Finset ℕ) : Finset Edge :=
  (V ×ˢ V).filter (fun e => e.1 < e.2)

variable {n : ℕ} {X : Type*} [MetricSpace X]

def arrival (I : Instance n X) (u : ℕ) : ℝ :=
  if h : u < n then I.arrival ⟨u,h⟩ else 0

def spatial (I : Instance n X) (u v : ℕ) : ℝ :=
  if hu : u < n then
    if hv : v < n then dist (I.location ⟨u,hu⟩) (I.location ⟨v,hv⟩) else 0
  else 0

def requestDist (I : Instance n X) (u v : ℕ) : ℝ :=
  spatial I u v + |arrival I u - arrival I v|

def maturation (I : Instance n X) (e : Edge) : ℝ :=
  min (arrival I e.1) (arrival I e.2) + 2 * requestDist I e.1 e.2

def IsPairing (n : ℕ) (M : Finset Edge) : Prop :=
  M ⊆ allPairs (Finset.range n) ∧
  ∀ u ∈ Finset.range n, ∃! e, e ∈ M ∧ u ∈ endpoints e

def FeasibleTimes (I : Instance n X) (M : Finset Edge) (T : Edge → ℝ) : Prop :=
  ∀ e ∈ M, max (arrival I e.1) (arrival I e.2) ≤ T e

def scheduleCost (I : Instance n X) (M : Finset Edge) (T : Edge → ℝ) : ℝ :=
  ∑ e ∈ M, (spatial I e.1 e.2 + (T e - arrival I e.1) + (T e - arrival I e.2))

def pairingCost (I : Instance n X) (M : Finset Edge) : ℝ :=
  ∑ e ∈ M, requestDist I e.1 e.2

def timedCosts (I : Instance n X) : Set ℝ :=
  {c | ∃ M T, IsPairing n M ∧ FeasibleTimes I M T ∧ c = scheduleCost I M T}

def offlineOpt (I : Instance n X) : ℝ := sInf (timedCosts I)
def pairingCosts (I : Instance n X) : Set ℝ :=
  {c | ∃ M, IsPairing n M ∧ c = pairingCost I M}
def pairingOpt (I : Instance n X) : ℝ := sInf (pairingCosts I)

end MatchingDelays.Linear


