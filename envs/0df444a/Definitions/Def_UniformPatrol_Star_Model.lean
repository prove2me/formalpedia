-- Prove2me | Definitions.Def_UniformPatrol_Star_Model
-- name    : UniformPatrol_Star_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:58.09449+00:00
-- url     : https://prove2.me/theorems/3730a14a-3636-4e9f-88d2-d7dcfe641195
-- title:
--   Star patrolling model, delay attacks, and interception probability
-- statement:
--   The star $S_n$ has a centre $C$ and $n$ attackable end nodes. A patroller strategy $(p,s)$ moves from $C$ to each end with probability $p$, stays at $C$ with probability $1-np$, returns from an end to $C$ with probability $s$, and otherwise stays at that end. Admissibility means $p>0$, $np\leq1$, and $0<s\leq1$. An attacker strategy chooses an end $A$ and delay $d\geq1$. If the patroller returns to $A$ before $d$ consecutive periods of absence, the delay count restarts.
--
--   Starting at $C$ immediately after departure from $A$, let $T_A$ be the first positive step returning to $A$. For attack duration $m$, the interception probability is
--
--   $$Q_{n,m}(p,s;A,d)=1-\frac{\Pr_C(T_A\geq d+m-1)}{\Pr_C(T_A\geq d)}.$$
--
--   Finite taboo-path sums define these probabilities on the original star. A pure saddle point compares the payoff over all admissible patroller and attacker strategies; a strategy is optimal if it occurs in one. The model also defines the conditional centre probability $c(d)$ and the update map $f(c,s)$.
--
--   **Formalization Note** The centre is `none` and end $i$ is `some i`. The attack starts in the $d$th period of absence. The theorems require $n\geq2$ and $m\geq2$; $n\geq2$ is added so another end exists and the conditioning event is positive. Mixed strategies are not represented.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, pp. 1–3 (PDF 2–4), §§1–2; p. 11 (PDF 12), eq. (17); p. 4 (PDF 5), eq. (3)

import Mathlib
import Definitions.Def_UniformPatrol_Star_ZeroSum

namespace UniformPatrol.Star

/-- The centre is `none`; the n end nodes are `some i`. -/
abbrev Node (n : ℕ) := Option (Fin n)

/-- A Markov patrol on the star with centre-to-end probability p per end and reflection probability s. -/
structure PStrat (n : ℕ) where
  p : ℝ
  s : ℝ
  p_pos : 0 < p
  np_le : (n : ℝ) * p ≤ 1
  s_pos : 0 < s
  s_le : s ≤ 1

/-- The attacked end node and the number of consecutive periods of absence before attacking. -/
structure AStrat (n : ℕ) where
  A : Fin n
  d : ℕ
  one_le_d : 1 ≤ d

/-- One-step probability on the original star, before reduction by symmetry. -/
def trans (n : ℕ) (p s : ℝ) : Node n → Node n → ℝ
  | none, none => 1 - (n : ℝ) * p
  | none, some _ => p
  | some _, none => s
  | some i, some j => if i = j then 1 - s else 0

/-- Probability of ending at y after t steps without having visited A in steps 1 through t. -/
def avoid (n : ℕ) (p s : ℝ) (A : Fin n) (x₀ : Node n) : ℕ → Node n → ℝ
  | 0, y => if y = x₀ then 1 else 0
  | t + 1, y => if y = some A then 0 else
      ∑ x : Node n, avoid n p s A x₀ t x * trans n p s x y

/-- Probability that the first visit to A is later than t. -/
def survive (n : ℕ) (p s : ℝ) (A : Fin n) (x₀ : Node n) (t : ℕ) : ℝ :=
  ∑ y : Node n, avoid n p s A x₀ t y

/-- Probability of visiting A within t steps. -/
def hitWithin (n : ℕ) (p s : ℝ) (A : Fin n) (x₀ : Node n) (t : ℕ) : ℝ :=
  1 - survive n p s A x₀ t

/-- Equation (17): conditional interception probability for the attack starting in the d-th
period of absence, with X₀ at the centre in the first period of absence. -/
noncomputable def Q (n m : ℕ) (x : PStrat n) (a : AStrat n) : ℝ :=
  1 - survive n x.p x.s a.A none (a.d + m - 2) /
    survive n x.p x.s a.A none (a.d - 1)

/-- Pure saddle-point optimality over the full patroller and attacker strategy sets. -/
def IsSaddle (n m : ℕ) (x : PStrat n) (a : AStrat n) : Prop :=
  PureSaddle (Q n m) x a

def IsOptimalP (n m : ℕ) (x : PStrat n) : Prop :=
  ∃ a : AStrat n, IsSaddle n m x a

def IsOptimalA (n m : ℕ) (a : AStrat n) : Prop :=
  ∃ x : PStrat n, IsSaddle n m x a

/-- Conditional probability of the centre at the start of an attack with delay d. -/
noncomputable def cAt (n : ℕ) (p s : ℝ) (A : Fin n) (d : ℕ) : ℝ :=
  avoid n p s A none (d - 1) none / survive n p s A none (d - 1)

/-- The conditional centre-probability update, equation (3). -/
noncomputable def fMap (n : ℕ) (p s c : ℝ) : ℝ :=
  (c * (1 - (n : ℝ) * p) + (1 - c) * s) / (1 - p * c)

end UniformPatrol.Star


