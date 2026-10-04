-- Prove2me | Definitions.Def_PolylogKServer_Allocation_Problem
-- name    : PolylogKServer_Allocation_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:28:29.314571+00:00
-- url     : https://prove2.me/theorems/516fc924-e110-4a64-a014-aac9d1970671
-- title:
--   The fractional allocation problem on a weighted star and (θ, γ)-competitiveness
-- statement:
--   Consider a weighted star with $d$ leaves ("locations"), the distance from the center to location $i$ being $w_i>0$, and at most $k$ servers. An instance also fixes an initial quota $\kappa(0)\le k$ and an initial integral configuration $n^0$ with $n^0_i\le k$ servers at location $i$ and $\sum_i n^0_i\le\kappa(0)$.
--
--   At time $t\ge1$ a request arrives: a location $i^t$, a quota $\kappa(t)\le k$ (the number of servers available at time $t$) and a cost vector $h^t=(h^t(0),\dots,h^t(k))$, where $h^t(j)\ge0$ is the cost of serving the request with $j$ servers at $i^t$; the costs are monotone, $h^t(j)\ge h^t(j+1)$.
--
--   1. A **fractional state** is $x=(x_{i,j})_{i\in[d],\,0\le j\le k}$ with $x_{i,j}$ the probability of having exactly $j$ servers at location $i$. It is feasible for the quota $\kappa$ if $x_{i,\cdot}$ is a probability distribution for each $i$ and $\sum_i\sum_j j\,x_{i,j}\le\kappa$.
--   2. When the state changes from $x^{t-1}$ to $x^t$ at time $t$, the **hit cost** is $\sum_j h^t(j)\,x^t_{i^t,j}$ and the **movement cost** is
--   $$
--   \sum_i w_i\sum_{j=1}^{k}\Big|\sum_{j'<j}x^t_{i,j'}-\sum_{j'<j}x^{t-1}_{i,j'}\Big| .
--   $$
--   3. $\mathrm{Optcost}$ is the minimum total cost (hit cost plus movement cost) of an **integral** solution: a sequence of integral configurations $n^t$ starting at $n^0$ with $n^t_i\le k$ and $\sum_i n^t_i\le\kappa(t)$, paying $h^t(n^t_{i^t})+\sum_i w_i|n^t_i-n^{t-1}_i|$ at time $t$.
--   4. $g(\kappa)=\sum_{t\ge1}|\kappa(t)-\kappa(t-1)|$ is the total variation of the quota pattern and $w_{\max}=\max_i w_i$.
--   5. An **online fractional allocation algorithm** chooses the state after each request as a function of the requests seen so far. It is **$(\theta,\gamma)$-competitive** if it starts at the point mass on $n^0$, every state it reaches is feasible for the current quota, and there is a constant $a$, independent of the request sequence, such that on every request sequence
--   $$
--   \text{hit cost}\le\theta\,(\mathrm{Optcost}+w_{\max}\,g(\kappa))+a,\qquad \text{movement cost}\le\gamma\,(\mathrm{Optcost}+w_{\max}\,g(\kappa))+a.
--   $$
--
--   The allocation problem is the building block of the paper's fractional k-server algorithm: every internal node of a weighted HST runs one allocation instance to split its servers among its children.
--
--   **Formalization Note** The additive constant $a$ is not in the definition on p. 5 but is in Theorem 14 (p. 20), from which Theorem 5 follows; it may depend on the instance ($d$, $k$, $w$, $n^0$, $\kappa(0)$) but not on the requests. The diameter $\Delta$ of p. 5 is taken to be $w_{\max}$, as in Theorem 14. Cost vectors are finite real numbers. Requests are a finite list; the quota $\kappa(t)$ is carried by the $t$-th request.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 5 (allocation problem, (θ, γ)-competitive, g(κ)), p. 7 (fractional allocation problem, constraints 1–2, eq. (1)), p. 20 (Theorem 14: integral Optcost, w_max, additive term)

import Mathlib

/-!
# The allocation problem on a weighted star and its fractional version

Bansal, Buchbinder, Mądry, Naor, *A Polylogarithmic-Competitive Algorithm for the k-Server
Problem*, arXiv:1110.1580v1, §1.2, p. 5 (the allocation problem, (θ, γ)-competitiveness,
`g(κ)`), p. 7 (the fractional allocation problem, constraints 1–2, hit cost, movement cost (1)),
p. 20 (Theorem 14: `Optcost` is an integral optimum, `w_max = max_i w_i` is the diameter, and the
guarantee carries an additive term depending only on the start and final configurations).

An instance consists of `d` locations with weights `w i > 0` (the distance from the center of the
star to location `i`), the maximal number `k` of servers, an initial quota `κ₀ = κ(0) ≤ k` and an
initial integral configuration `n₀` (`n₀ i ≤ k` servers at `i`, `∑ i, n₀ i ≤ κ₀`). A request at
time `t` is a location `i^t`, a cost vector `h^t = (h^t(0), …, h^t(k))` that is non-negative and
non-increasing, and the quota `κ(t) ≤ k`.
-/

namespace PolylogKServer.Allocation

open Finset

/-- A request of the allocation problem: the requested location `loc = i^t`, the cost vector
`h = h^t` (`h j` is the cost of serving the request with `j` servers at `loc`), and the number
`quota = κ(t)` of servers available at this time step. -/
structure Request (d k : ℕ) where
  loc : Fin d
  h : Fin (k + 1) → ℝ
  quota : ℕ

/-- A request is admissible (p. 5): `κ(t) ≤ k`, and the cost vector is non-negative and
monotone, `h(j) ≥ h(j + 1)` for `0 ≤ j ≤ k - 1`. -/
def Request.Valid {d k : ℕ} (r : Request d k) : Prop :=
  r.quota ≤ k ∧ (∀ j, 0 ≤ r.h j) ∧ Antitone r.h

/-- `h(j)` for a natural number `j`, read as `h(min j k)`; it is only ever used with `j ≤ k`. -/
def Request.hAt {d k : ℕ} (r : Request d k) (j : ℕ) : ℝ :=
  r.h ⟨min j k, Nat.lt_succ_of_le (Nat.min_le_right j k)⟩

/-- A fractional state `x i j`: the probability of having exactly `j` servers at location `i`. -/
abbrev FracState (d k : ℕ) := Fin d → Fin (k + 1) → ℝ

/-- Feasibility of a fractional state for the quota `κ` (p. 7): (1) for each location the
`x i ·` form a probability distribution, and (2) the expected number of servers used is at most
`κ`, `∑ i ∑ j j · x i j ≤ κ`. -/
def FracFeasible {d k : ℕ} (x : FracState d k) (κ : ℕ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∀ i, ∑ j, x i j = 1) ∧ (∑ i, ∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * x i j ≤ κ)

/-- The point mass at the integral configuration `n₀` (the common starting state). -/
def pointMass {d k : ℕ} (n₀ : Fin d → ℕ) : FracState d k :=
  fun i j => if (j : ℕ) = n₀ i then 1 else 0

/-- `∑_{j' < j} x i j'`. -/
def cumul {d k : ℕ} (x : FracState d k) (i : Fin d) (j : ℕ) : ℝ :=
  ∑ j' : Fin (k + 1), if (j' : ℕ) < j then x i j' else 0

/-- The hit cost of serving the request `r` in the state `x` (p. 7): `∑_j h(j) x_{i^t, j}`. -/
def hitCost {d k : ℕ} (r : Request d k) (x : FracState d k) : ℝ :=
  ∑ j, r.h j * x r.loc j

/-- The movement cost of changing the state from `x` to `x'` (p. 7, eq. (1)):
`∑_i w_i ∑_{j=1}^{k} |∑_{j'<j} x'_{i,j'} − ∑_{j'<j} x_{i,j'}|`. -/
def moveCost {d k : ℕ} (w : Fin d → ℝ) (x x' : FracState d k) : ℝ :=
  ∑ i, w i * ∑ j ∈ Icc 1 k, |cumul x' i j - cumul x i j|

/-- All requests of the sequence are admissible. -/
def ValidSeq {d k : ℕ} (ρ : List (Request d k)) : Prop := ∀ r ∈ ρ, r.Valid

/-- The quota pattern of the request sequence `ρ` started at `κ₀`: `κ(0) = κ₀` and `κ(t)` is
the quota of the `t`-th request (`t ≥ 1`). -/
def quotaAt {d k : ℕ} (κ₀ : ℕ) (ρ : List (Request d k)) : ℕ → ℝ
  | 0 => κ₀
  | t + 1 => ((ρ[t]?).map Request.quota).getD 0

/-- The total variation of the quota pattern (p. 5): `g(κ) = ∑_{t ≥ 1} |κ(t) − κ(t − 1)|`. -/
def quotaVariation {d k : ℕ} (κ₀ : ℕ) (ρ : List (Request d k)) : ℝ :=
  ∑ t ∈ range ρ.length, |quotaAt κ₀ ρ (t + 1) - quotaAt κ₀ ρ t|

/-- The diameter used in the guarantee: `w_max = max_i w_i` (Theorem 14, p. 20). -/
noncomputable def wmax {d : ℕ} (w : Fin d → ℝ) : ℝ := ⨆ i, w i

/-- An integral schedule `n` (with `n t i` servers at location `i` after the `t`-th request)
serves `ρ` from `n₀`: `n 0 = n₀`, and after each request at most `k` servers sit at each
location and at most `κ(t)` servers are used in total. -/
def IntFeasible {d k : ℕ} (n₀ : Fin d → ℕ) (ρ : List (Request d k)) (n : ℕ → Fin d → ℕ) :
    Prop :=
  n 0 = n₀ ∧ ∀ t (ht : t < ρ.length),
    (∀ i, n (t + 1) i ≤ k) ∧ ∑ i, n (t + 1) i ≤ (ρ[t]'ht).quota

/-- The total cost of an integral schedule: hit cost `∑_t h^t(n^t_{i^t})` plus movement cost
`∑_t ∑_i w_i |n^t_i − n^{t−1}_i|` (eq. (1) at integral states). -/
noncomputable def intCost {d k : ℕ} (w : Fin d → ℝ) (ρ : List (Request d k))
    (n : ℕ → Fin d → ℕ) : ℝ :=
  ∑ t ∈ range ρ.length,
    ((((ρ[t]?).map fun r => r.hAt (n (t + 1) r.loc)).getD 0) +
      ∑ i, w i * |((n (t + 1) i : ℕ) : ℝ) - ((n t i : ℕ) : ℝ)|)

/-- `Optcost`: the cost of an optimal **integral** solution of the instance (Theorem 14, p. 20),
the infimum of `intCost` over all integral schedules serving `ρ` from `n₀`. (The all-zero
schedule after time 0 is always feasible, and all costs are non-negative for admissible
requests and positive weights, so the infimum is over a nonempty set bounded below.) -/
noncomputable def optCost {d k : ℕ} (w : Fin d → ℝ) (n₀ : Fin d → ℕ)
    (ρ : List (Request d k)) : ℝ :=
  sInf {c : ℝ | ∃ n : ℕ → Fin d → ℕ, IntFeasible n₀ ρ n ∧ c = intCost w ρ n}

/-- An **online fractional allocation algorithm**: its state after the requests `l` is
`state l`, a function of the request prefix only; `state []` is its initial state. -/
structure FracAlg (d k : ℕ) where
  state : List (Request d k) → FracState d k

/-- Total hit cost of `A` on `ρ`: `∑_t ∑_j h^t(j) x^t_{i^t, j}`, with `x^t` the state after the
first `t` requests. -/
noncomputable def FracAlg.hitTotal {d k : ℕ} (A : FracAlg d k) (ρ : List (Request d k)) : ℝ :=
  ∑ t ∈ range ρ.length,
    (((ρ[t]?).map fun r => hitCost r (A.state (ρ.take (t + 1)))).getD 0)

/-- Total movement cost of `A` on `ρ`: `∑_t` of eq. (1) between consecutive states. -/
noncomputable def FracAlg.moveTotal {d k : ℕ} (A : FracAlg d k) (w : Fin d → ℝ)
    (ρ : List (Request d k)) : ℝ :=
  ∑ t ∈ range ρ.length, moveCost w (A.state (ρ.take t)) (A.state (ρ.take (t + 1)))

/-- `A` is a **(θ, γ)-competitive** fractional allocation algorithm on the weighted star `w`
from the initial configuration `n₀` with initial quota `κ₀` (p. 5, with the additive term of
Theorem 14, p. 20):
1. it starts at the point mass at `n₀`;
2. after every admissible request sequence its state is feasible for the current quota;
3. there is a constant `a`, fixed before the request sequence, such that on every admissible
   request sequence the hit cost is at most `θ · (Optcost + w_max · g(κ)) + a` and the movement
   cost is at most `γ · (Optcost + w_max · g(κ)) + a`. -/
def FracAlg.IsCompetitive {d k : ℕ} (A : FracAlg d k) (w : Fin d → ℝ) (n₀ : Fin d → ℕ)
    (κ₀ : ℕ) (θ γ : ℝ) : Prop :=
  A.state [] = pointMass n₀ ∧
  (∀ (l : List (Request d k)) (r : Request d k), ValidSeq (l ++ [r]) →
    FracFeasible (A.state (l ++ [r])) r.quota) ∧
  ∃ a : ℝ, ∀ ρ : List (Request d k), ValidSeq ρ →
    A.hitTotal ρ ≤ θ * (optCost w n₀ ρ + wmax w * quotaVariation κ₀ ρ) + a ∧
    A.moveTotal w ρ ≤ γ * (optCost w n₀ ρ + wmax w * quotaVariation κ₀ ρ) + a

end PolylogKServer.Allocation


