-- Prove2me | Definitions.Def_VRPTWColGen92_Bound_Network
-- name    : VRPTWColGen92_Bound_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:05:25.354702+00:00
-- url     : https://prove2.me/theorems/42fb3a14-d954-42c0-885d-80c1f876ad67
-- title:
--   Secs. 2–3, p. 344 — the VRPTW network, resource-feasible paths, routes, 2-cycle-free paths and VRPTW solutions
-- statement:
--   This module sets up the vehicle routing problem with time windows (VRPTW) of Desrochers, Desrosiers and Solomon (1992) and the three solution spaces of their pricing subproblem.
--
--   **Instance (Sec. 2, p. 344).** The nodes are $0, 1, \dots, n$; node $0$ is the central depot $d$ and the nodes $1, \dots, n$ are the customers $N\setminus\{d\}$. The data are:
--   1. an arc set $A$, an arbitrary relation on the nodes (it is free data: the paper eliminates arcs in its preprocessing and branching);
--   2. for every pair $(i,j)$ a cost $c_{ij}$ and a duration $t_{ij}$ (the service time at $i$ is included in $t_{ij}$);
--   3. for every node a demand $q_i$ and a time window $[a_i, b_i]$;
--   4. the vehicle capacity $Q$.
--
--   No sign, integrality or triangle condition is imposed on the data here; statements that need one state it.
--
--   **Paths (Sec. 3, p. 344).** A path visiting the customers $i_1, \dots, i_K$ in this order is recorded by its customer list $p = (i_1,\dots,i_K)$; its node sequence is
--   $$(i_0, i_1, \dots, i_K, i_{K+1}) = (d, i_1, \dots, i_K, d).$$
--   For a function $f$ on pairs of nodes, $\sum_{k=0}^{K} f(i_k, i_{k+1})$ is the sum of $f$ over the consecutive pairs of the node sequence; the **cost** of the path is $c_r = \sum_{k=0}^{K} c_{i_k i_{k+1}}$. The **load** is $\sum_{k=1}^{K} q_{i_k}$ (a customer visited twice contributes its demand twice). The path is **schedulable** if there are service start times $T_0, \dots, T_{K+1}$, one per position, with
--   $$T_0 = 0,\qquad T_k + t_{i_k i_{k+1}} \le T_{k+1}\ (0 \le k \le K),\qquad a_{i_k} \le T_k \le b_{i_k}\ (0 \le k \le K+1).$$
--
--   A **path of the second model** is a customer list with $K \ge 1$, containing no depot, all of whose arcs $(i_k, i_{k+1})$ lie in $A$, that is schedulable and has load at most $Q$; customers may repeat. A **feasible route** (the set $R$ of the paper, first model) is such a path visiting every customer at most once. A **2-cycle** is a pattern $(i, j, i)$ among three consecutive customers, and a **path of the third model** is a second-model path with no 2-cycle.
--
--   **VRPTW solutions (Sec. 2, set partitioning model).** A VRPTW solution is a finite set $S$ of feasible routes such that every customer $i$ is visited by exactly one of them: $\sum_{r \in S} \delta_{ir} = 1$, where $\delta_{ir}\in\{0,1\}$ is the number of visits of route $r$ to $i$. Its cost is $\sum_{r\in S} c_r$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Nodes are `Fin (n+1)` with the depot `0`; a path is a `List` of nodes (its customers), and the node sequence is `0 :: p ++ [0]`. Service times are indexed by position, not by node, because a path of the second model can visit a node twice. Three readings are pinned down and disclosed: the depot's window is also imposed at the return (the page writes $0 \le k \le K$; Figure 1 gives the depot the window $[0,8]$, which with $T_d = 0$ only binds at the return); the capacity constraint is "load $\le Q$" (the page says "less than", but the recurrences use $q \le Q$ and Figure 1's count of twenty-two paths needs $\le$); a 2-cycle is a pattern of the customer list, so $(d, i, d)$ is not a 2-cycle. A path visits at least one customer and passes through the depot only at its ends.
-- source:
--   Desrochers, Desrosiers & Solomon, A new optimization algorithm for the vehicle routing problem with time windows, Oper. Res. 40 (1992), pp. 344–346, Secs. 2–3

import Mathlib

namespace VRPTWColGen92.Bound

/-- A VRPTW instance on the nodes `Fin (n+1)`: node `0` is the depot `d`, the nonzero nodes are the
customers `N \ {d}`. `arc` is the arc set `A` (free data), `c i j` the cost and `t i j` the duration of
arc `(i, j)`, `q i` the demand, `[a i, b i]` the time window of node `i`, and `Q` the vehicle capacity
(Desrochers, Desrosiers & Solomon 1992, Secs. 2–3, p. 344). -/
structure Instance (n : ℕ) where
  arc : Fin (n + 1) → Fin (n + 1) → Prop
  c : Fin (n + 1) → Fin (n + 1) → ℝ
  t : Fin (n + 1) → Fin (n + 1) → ℝ
  q : Fin (n + 1) → ℝ
  a : Fin (n + 1) → ℝ
  b : Fin (n + 1) → ℝ
  Q : ℝ

variable {n : ℕ}

/-- The node sequence `(i_0, i_1, …, i_K, i_{K+1}) = (d, i_1, …, i_K, d)` of the path whose customer
list is `p = [i_1, …, i_K]`. -/
def nodes (p : List (Fin (n + 1))) : List (Fin (n + 1)) := (0 :: p) ++ [0]

/-- The sum of `f i_k i_{k+1}` over the consecutive pairs `k = 0, …, K` of the node sequence. -/
def arcSum (f : Fin (n + 1) → Fin (n + 1) → ℝ) (p : List (Fin (n + 1))) : ℝ :=
  (((nodes p).zip (nodes p).tail).map (fun e => f e.1 e.2)).sum

/-- Every arc `(i_k, i_{k+1})` of the node sequence belongs to `A`. -/
def ArcsOK (I : Instance n) (p : List (Fin (n + 1))) : Prop :=
  ∀ k (hk : k + 1 < (nodes p).length), I.arc (nodes p)[k] (nodes p)[k + 1]

/-- Service start times `T_k`, indexed by the position `k = 0, …, K+1` in the node sequence, with
`T_0 = 0` (`T_d = 0`), `T_k + t_{i_k i_{k+1}} ≤ T_{k+1}` (waiting allowed) and
`a_{i_k} ≤ T_k ≤ b_{i_k}` at every position, the return to the depot included. -/
def Schedulable (I : Instance n) (p : List (Fin (n + 1))) : Prop :=
  ∃ T : ℕ → ℝ, T 0 = 0 ∧
    (∀ k (hk : k + 1 < (nodes p).length),
      T k + I.t (nodes p)[k] (nodes p)[k + 1] ≤ T (k + 1)) ∧
    (∀ k (hk : k < (nodes p).length),
      I.a (nodes p)[k] ≤ T k ∧ T k ≤ I.b (nodes p)[k])

/-- The load `∑_{k=1}^{K} q_{i_k}`: every visit adds its demand. -/
def load (I : Instance n) (p : List (Fin (n + 1))) : ℝ := (p.map I.q).sum

/-- The cost `c_r = ∑_{k=0}^{K} c_{i_k i_{k+1}}` of the path. -/
def cost (I : Instance n) (p : List (Fin (n + 1))) : ℝ := arcSum I.c p

/-- A path of the second model (state-space relaxation): it visits at least one customer, passes through
the depot only at its two ends, uses arcs of `A`, admits a schedule and its load is at most `Q`.
Customers may repeat. -/
def IsPath (I : Instance n) (p : List (Fin (n + 1))) : Prop :=
  p ≠ [] ∧ (0 : Fin (n + 1)) ∉ p ∧ ArcsOK I p ∧ Schedulable I p ∧ load I p ≤ I.Q

/-- A feasible route (the paper's set `R`, first model): a path visiting each customer at most once. -/
def IsRoute (I : Instance n) (p : List (Fin (n + 1))) : Prop :=
  IsPath I p ∧ p.Nodup

/-- No 2-cycle `(i, j, i)` in the customer list. -/
def NoTwoCycle (p : List (Fin (n + 1))) : Prop :=
  ∀ k (hk : k + 2 < p.length), p[k] ≠ p[k + 2]

/-- A path of the third model: a second-model path without 2-cycles. -/
def IsPath3 (I : Instance n) (p : List (Fin (n + 1))) : Prop :=
  IsPath I p ∧ NoTwoCycle p

/-- A VRPTW solution (the set partitioning model of Sec. 2): a finite set of feasible routes covering
every customer exactly once. -/
def IsVRPTWSolution (I : Instance n) (S : Finset (List (Fin (n + 1)))) : Prop :=
  (∀ p ∈ S, IsRoute I p) ∧
    ∀ i : Fin (n + 1), i ≠ 0 → ∑ p ∈ S, (p.count i : ℝ) = 1

/-- The cost `∑_{r ∈ S} c_r` of a VRPTW solution. -/
def solCost (I : Instance n) (S : Finset (List (Fin (n + 1)))) : ℝ :=
  ∑ p ∈ S, cost I p

end VRPTWColGen92.Bound


