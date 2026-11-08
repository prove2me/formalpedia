-- Prove2me | Definitions.Def_OnlineJRP_LinearDelay_OPT
-- name    : OnlineJRP_LinearDelay_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:51:43.772682+00:00
-- url     : https://prove2.me/theorems/6dbae155-e12d-4dee-905f-88b9f256128b
-- title:
--   Online joint replenishment with linear delays: instances, purchases, feasibility, cost and the offline optimum
-- statement:
--   An **instance** of the joint replenishment problem with linear delays has items $[n]$, a joint cost $c_{\mathrm{joint}}>0$, item costs $c_i\ge 0$ and a finite sequence of **requests** $r=(t_r,i_r,w_r)$ with release time $t_r\ge 0$, item $i_r\in[n]$ and weight $w_r>0$. A **purchase** $(t,S)$ has a time $t$ and a nonempty set $S\subseteq[n]$; it costs $c_{\mathrm{joint}}+\sum_{i\in S}c_i$ and serves every request $r$ with $i_r\in S$, $t_r\le t$ that has not already been served. A solution is **feasible** if every request is served. The **service time** $s_r$ is the time of the purchase serving $r$, and the cost of a solution is
--   $$
--   \sum_{(t,S)}\Big(c_{\mathrm{joint}}+\sum_{i\in S}c_i\Big)+\sum_r w_r(s_r-t_r).
--   $$
--   The **offline optimum** $\mathrm{OPT}$ is the infimum of the costs of the feasible solutions. These objects are the terms in which the competitive ratio is stated.
--
--   **Formalization Note** The requests are a list in release order, with the position as the identity of a request. A solution is a list of purchases: repeating a purchase only costs more, so the infimum is that over sets. The service time is the infimum of the times of the purchases able to serve the request, which is a minimum on a feasible solution; cost is used only on feasible solutions.
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Sec. 1, p. 1

import Mathlib

namespace OnlineJRP.LinearDelay

open Finset

/-- The costs of an instance (Baligács, Chang, Coester, Optimal Online Joint Replenishment with
Linear Delays (preprint, sha256 116bba5b…), Sec. 1, p. 1): a joint cost `cjoint > 0` and an item
cost `c i ≥ 0` for each of the items `Fin n`.

**Formalization Note** Only the requests are online; the algorithm of the goal theorem receives
these costs as a parameter. The paper's normalization `cjoint = 1` is used only in the milestones
about Algorithms 1–3. -/
structure Params (n : ℕ) where
  /-- The joint cost of a purchase. -/
  cjoint : ℝ
  /-- The item costs. -/
  c : Fin n → ℝ
  cjoint_pos : 0 < cjoint
  c_nonneg : ∀ i, 0 ≤ c i

/-- A request `r = (t_r, i_r, w_r)`: release time, item and weight (Sec. 1, p. 1). The conditions
`t_r ≥ 0`, `w_r > 0` are in `IsInstance`. -/
structure Req (n : ℕ) where
  /-- Release time `t_r`. -/
  t : ℝ
  /-- Item `i_r`. -/
  i : Fin n
  /-- Weight `w_r`. -/
  w : ℝ

/-- A finite request sequence (Sec. 1, p. 1): release times `≥ 0`, weights `> 0`.

**Formalization Note** The sequence is listed in release order, with simultaneous requests in the
order the algorithm processes them; every finite family can be listed this way, so no instance is
lost. The list position is the identity of a request: equal triples stay distinct requests. -/
def IsInstance {n : ℕ} (σ : List (Req n)) : Prop :=
  (∀ r ∈ σ, 0 ≤ r.t ∧ 0 < r.w) ∧ σ.Pairwise (fun a b => a.t ≤ b.t)

/-- A purchase `(t, S)` with `S` a nonempty set of items (Sec. 1, p. 1). -/
structure Purchase (n : ℕ) where
  /-- The time `t` of the purchase. -/
  time : ℝ
  /-- The purchased items `S`. -/
  items : Finset (Fin n)
  nonempty : items.Nonempty

/-- `(t, S)` can serve `r` when `i_r ∈ S` and `t_r ≤ t` (Sec. 1, p. 1). -/
def Serves {n : ℕ} (p : Purchase n) (r : Req n) : Prop :=
  r.i ∈ p.items ∧ r.t ≤ p.time

/-- A solution is feasible if every request is served (Sec. 1, p. 1). -/
def IsFeasible {n : ℕ} (sol : List (Purchase n)) (σ : List (Req n)) : Prop :=
  ∀ r ∈ σ, ∃ p ∈ sol, Serves p r

/-- The service time `s_r` of `r`: the time of the purchase that serves it, i.e. the earliest
purchase of `sol` that can serve it, since a purchase serves every such request "that has not
already been served" (Sec. 1, p. 1).

**Formalization Note** The set is finite, and nonempty exactly when some purchase can serve `r`, so
on a feasible solution this `sInf` is a minimum. On an infeasible solution it is the junk value `0`;
`cost` is only ever used on feasible solutions (`OPT` ranges over them, and the goal asserts
feasibility of the algorithm's output). -/
noncomputable def serviceTime {n : ℕ} (sol : List (Purchase n)) (r : Req n) : ℝ :=
  sInf {t | ∃ p ∈ sol, Serves p r ∧ p.time = t}

/-- The cost of a solution (Sec. 1, p. 1): the total purchasing cost `cjoint + ∑_{i ∈ S} c_i` plus
the total delay cost `w_r (s_r - t_r)`. -/
noncomputable def cost {n : ℕ} (P : Params n) (sol : List (Purchase n)) (σ : List (Req n)) : ℝ :=
  (sol.map (fun p => P.cjoint + ∑ i ∈ p.items, P.c i)).sum +
    (σ.map (fun r => r.w * (serviceTime sol r - r.t))).sum

/-- The optimal offline cost: the infimum of the costs of all feasible finite lists of purchases.

**Formalization Note** The paper's solution is a set of purchases. A list may repeat a purchase, which
only costs more, so the infimum is the same; an infinite set of purchases has infinite cost. On an
instance the set of costs is nonempty when `σ` is (buy the item of each request at its release
time; for `σ = []` take the empty list) and bounded below by `0`, so this `sInf` is not the junk value. -/
noncomputable def OPT {n : ℕ} (P : Params n) (σ : List (Req n)) : ℝ :=
  sInf {C | ∃ sol : List (Purchase n), IsFeasible sol σ ∧ C = cost P sol σ}

end OnlineJRP.LinearDelay


