-- Prove2me | Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis
-- name    : OnlineMaxWeightMatch_Approx_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:51.757156+00:00
-- url     : https://prove2.me/theorems/1dadf1e6-06aa-4562-b6ea-c7f716f357e5
-- title:
--   Early and late edges (Definition 4.3) and the events V, O, O^E, A_t, i_1, U_1(t) of §4.2–4.3
-- statement:
--   Fix a vector $x=(x_{i,t})$ and run Algorithm 1 (Lines 3–13) on it, with $c=0.01$ and $\theta=\frac{1/2-c}{1/2+c}$.
--
--   1. **Definition 4.3.** Ball $t$ is **early** for bin $i$ if $\sum_{t'<t}x_{i,t'}\le\theta$, and **late** otherwise. Edge $(i,t)$ is early (late) if $t$ is early (late) for $i$.
--   2. $V_{i,t}$ is the indicator of the event that bin $i$ is **vacant** (unmatched) at time $t$, i.e. before ball $t$ is processed; $O_{i,t}:=1-V_{i,t}$ is the indicator that $i$ is **occupied** at time $t$.
--   3. $O^E_{i,t}\le O_{i,t}$ is the indicator that bin $i$ has been matched along an **early** edge before $t$ arrives.
--   4. $A_t$ is the event that ball $t$ arrives; $i_1$ is the bin picked in Line 5 at time $t$; $U_1(t)$ is the event that $t$ is unmatched after its first pick (no edge $(i,t)$ was added in Line 8).
--
--   These are the random quantities of the analysis of the first pick (§4.2) and of the second pick (§4.3): Corollary 4.5 and Lemma 4.8 are about $V$, Lemma 4.9 and Corollary 4.10 about $O^E$, and Equation (20), Lemmas 4.7 and 4.11 condition on $A_t$, $i_1$ and $U_1(t)$.
--
--   **Formalization Note** The events are sets of outcomes of Algorithm 1's probability space; $V_{i,t}$ and $O^E_{i,t}$ are their real-valued indicators. "At time $t$" is the state of the algorithm after balls $1,\dots,t-1$. The event $i_1\ne i$ includes the (probability-zero, under tightness and $p_t>0$) outcome "no bin".
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, pp. 11–14, Definition 4.3; V_{i,t}, M1, M2 (p. 12); A_t, U1(t) (p. 13); O_{i,t}, O^E_{i,t} (p. 14)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Algorithm1

namespace OnlineMaxWeightMatch.Approx

variable {ι : Type*} {n : ℕ}

/-- Definition 4.3: ball `t` is **early** for bin `i` if
`Σ_{t'<t} x_{i,t'} ≤ (1/2 - c)/(1/2 + c)`. -/
def IsEarly (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : Prop :=
  cumX x i t ≤ threshold

/-- Definition 4.3: ball `t` is **late** for bin `i` if it is not early,
`Σ_{t'<t} x_{i,t'} > (1/2 - c)/(1/2 + c)`. -/
def IsLate (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : Prop :=
  threshold < cumX x i t

/-- The event `V_{i,t}`: bin `i` is vacant (unmatched) at time `t`, i.e. before ball `t` is
processed. -/
def vacantSet (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : Set (Outcome ι n) :=
  {ω | IsVacantIn (stateAfter x ω t.val) i}

/-- The event `O_{i,t}`: bin `i` is occupied (matched) at time `t`, the complement of
`V_{i,t}`. -/
def occupiedSet (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : Set (Outcome ι n) :=
  (vacantSet x i t)ᶜ

/-- The event `O^E_{i,t}`: bin `i` is matched along an early edge before ball `t` is
processed. -/
def occupiedEarlySet (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : Set (Outcome ι n) :=
  {ω | ∃ s, IsEarly x i s ∧
    ((i, s) ∈ (stateAfter x ω t.val).1 ∨ (i, s) ∈ (stateAfter x ω t.val).2)}

/-- The indicator random variable `V_{i,t}`. -/
noncomputable def vacancy (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : Outcome ι n → ℝ :=
  (vacantSet x i t).indicator 1

/-- The indicator random variable `O^E_{i,t}`. -/
noncomputable def occupancyEarly (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : Outcome ι n → ℝ :=
  (occupiedEarlySet x i t).indicator 1

/-- The event `A_t`: ball `t` arrives. -/
def arrivalSet (t : Fin n) : Set (Outcome ι n) :=
  {ω | (ω t).arrives = true}

/-- The event `i_1 = j`: the bin picked in Line 5 at time `t` is `j`. -/
def firstPickSet (t : Fin n) (j : ι) : Set (Outcome ι n) :=
  {ω | (ω t).firstPick = some j}

/-- The event `U_1(t)`: ball `t` is unmatched after its first pick (no edge `(i, t)` was added
in Line 8). -/
noncomputable def unmatchedAfterFirstSet (x : ι → Fin n → ℝ) (t : Fin n) :
    Set (Outcome ι n) :=
  {ω | ∀ i, (i, t) ∉ M1 x ω}

end OnlineMaxWeightMatch.Approx


