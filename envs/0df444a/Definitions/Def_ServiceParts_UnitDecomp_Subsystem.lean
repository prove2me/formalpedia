-- Prove2me | Definitions.Def_ServiceParts_UnitDecomp_Subsystem
-- name    : ServiceParts_UnitDecomp_Subsystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T21:40:01.228704+00:00
-- url     : https://prove2.me/theorems/df6d4dd0-35a2-4f17-8e4f-9550be3b0695
-- title:
--   Single-unit single-customer subsystem, its optimal decisions $R^*_n(s,y)$ and the critical distance $y^*(n,s)$
-- statement:
--   Fix a model (Markov chain, demand law, $m$, $h$, $b$, $\alpha$) and a horizon of $N$ periods. A **subsystem** $\mathcal S_w$ consists of one unit and one customer, and its configuration at the beginning of a period is the pair $(z,y)$ of the unit's location and the customer's distance; together with the Markov state $s_n$ this is the state $x^w_n = (s_n, z_{wn}, y_{wn})$.
--
--   In a period with demand $d$, the unit moves (event 2; it moves from $m+1$ to $m$ only if the decision is *Release*), the customer moves (event 3), and if the unit is then on hand ($z = 1$) and the customer waiting ($y = 1$), unit $w$ serves customer $w$ and the configuration becomes $(0,0)$ (event 4, under the commitment constraint of Definition 3). The period's cost is $h$ if the unit is on hand and $b$ if the customer is waiting afterwards (event 5).
--
--   A subsystem policy $\rho$ chooses *Release* or *Hold* from $(n, s_n, z, y)$. Its expected discounted cost in periods $n,\dots,N$ is $C^\rho_n(s,x)$, and the optimal cost is
--   $$V_n(s,x) = \inf_\rho C^\rho_n(s,x).$$
--   For a decision $a$, let $Q_n(s,x,a)$ be the expected cost of taking $a$ in period $n$ and acting optimally afterwards. The set of optimal decisions for a subsystem whose unit is at the supplier and whose customer is at distance $y$ is
--   $$R^*_n(s,y) = \{a : Q_n(s,(m+1,y),a) \le Q_n(s,(m+1,y),a') \text{ for both } a'\},$$
--   the **critical distance** is
--   $$y^*(n,s) = \sup\{\, y : R^*_n(s,y) \ni \mathit{Release}\,\} \in \{0,1,2,\dots\}\cup\{\infty\},$$
--   and the **critical distance policy** releases the unit in period $n$ if and only if the customer's distance $y$ satisfies $y \le y^*(n,s)$.
--
--   These are the objects of Section 2.2.1.2.2 with which Lemma 2 and the optimality of the critical distance policy are stated.
--
--   **Formalization Note** The book writes $y^*(n,s)$ as a maximum; here it is a supremum in $\mathbb N \cup \{\infty\}$, which is $\infty$ when releasing is optimal at arbitrarily large distances (this happens in the last $m-1$ periods, where a released unit cannot arrive before the horizon ends) and would be $0$ for an empty set. The decision of a subsystem policy matters only when the unit is at the supplier.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 26-29, Definitions 1 and 3, Section 2.2.1.2.1 (state x^w_n, p. 27) and Section 2.2.1.2.2 (R*_n, p. 28; y*(n, s_n) and R_n, p. 29)

import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model

open scoped ENNReal NNReal

namespace ServiceParts.UnitDecomp

variable {σ : Type} [Fintype σ]

/-- The configuration `(z, y)` of a subsystem `S_w` at the beginning of a period: `z` is the
location of unit `w` and `y` the distance of customer `w` (Definition 1, p. 26, and the
sufficient state `x^w_n = (sₙ, z_{wn}, y_{wn})` of p. 27, without its Markov component). -/
abbrev SubState := ℕ × ℕ

/-- A Markov policy for a subsystem: a decision for its unit from the period, the Markov
state and the subsystem configuration. The decision only has an effect when the unit is at
the supplier location `m + 1`. -/
abbrev SubPolicy (σ : Type) := ℕ → σ → SubState → Decision

/-- Events 2–4 of a period for a subsystem under the commitment constraint of Definition 3
(unit `w` serves customer `w`): the unit moves (released or not), the customer moves by the
demand `d`, and if afterwards the unit is on hand and the customer waiting, both are used up
(location `0`, distance `0`). -/
def Model.subPost (M : Model σ) (x : SubState) (a : Decision) (d : ℕ) : SubState :=
  let z := unitMove M.m x.1 (decide (a = Decision.release))
  let y := custMove d x.2
  if z = 1 ∧ y = 1 then (0, 0) else (z, y)

/-- Event 5 for a subsystem: `h` if its unit is on hand and `b` if its customer is waiting
at the end of the period. -/
noncomputable def Model.subStage (M : Model σ) (x : SubState) : ℝ≥0∞ :=
  (if x.1 = 1 then (M.h : ℝ≥0∞) else 0) + (if x.2 = 1 then (M.b : ℝ≥0∞) else 0)

/-- Expected discounted cost of the subsystem policy `ρ` in periods `n, n + 1, …, N` from
Markov state `s` and configuration `x` in period `n`. -/
noncomputable def Model.subCost (M : Model σ) (N : ℕ) (ρ : SubPolicy σ) (n : ℕ) (s : σ)
    (x : SubState) : ℝ≥0∞ :=
  M.costToGo M.subPost M.subStage ρ (N + 1 - n) n s x

/-- Optimal expected discounted cost of a subsystem in periods `n, …, N`: the infimum of
`subCost` over all Markov subsystem policies. -/
noncomputable def Model.subOpt (M : Model σ) (N n : ℕ) (s : σ) (x : SubState) : ℝ≥0∞ :=
  ⨅ ρ : SubPolicy σ, M.subCost N ρ n s x

/-- Expected cost of taking decision `a` in period `n` (state `s`, configuration `x`) and
acting optimally in periods `n + 1, …, N`. -/
noncomputable def Model.subQ (M : Model σ) (N n : ℕ) (s : σ) (x : SubState) (a : Decision) :
    ℝ≥0∞ :=
  ∑' d : ℕ, M.demand s d *
    (M.subStage (M.subPost x a d) +
      (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' * M.subOpt N (n + 1) s' (M.subPost x a d))

/-- `R*ₙ(s, y)` (p. 28): the set of optimal decisions in period `n` for a subsystem whose
Markov state is `s`, whose customer is at distance `y` and whose unit is at the supplier
location `m + 1`. -/
noncomputable def Model.optDecisions (M : Model σ) (N n : ℕ) (s : σ) (y : ℕ) : Set Decision :=
  {a | ∀ a' : Decision, M.subQ N n s (M.m + 1, y) a ≤ M.subQ N n s (M.m + 1, y) a'}

/-- The critical distance `y*(n, s) = max {y : R*ₙ(s, y) ⊇ {Release}}` (p. 29), taken as a
supremum in `ℕ∞`: it is `⊤` when releasing is optimal at arbitrarily large distances, and `0`
when the set is empty. -/
noncomputable def Model.criticalDistance (M : Model σ) (N n : ℕ) (s : σ) : ℕ∞ :=
  ⨆ (y : ℕ) (_ : Decision.release ∈ M.optDecisions N n s y), (y : ℕ∞)

/-- The critical distance policy `Rₙ(s, y) = {Release}` iff `y ≤ y*(n, s)` (p. 29). -/
noncomputable def Model.criticalPolicy (M : Model σ) (N : ℕ) : SubPolicy σ :=
  fun n s x => if (x.2 : ℕ∞) ≤ M.criticalDistance N n s then Decision.release else Decision.hold

end ServiceParts.UnitDecomp


