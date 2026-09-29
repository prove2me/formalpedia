-- Prove2me | Definitions.Def_SplitDeliveryVRPTW_Known_Instance
-- name    : SplitDeliveryVRPTW_Known_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:49:14.404667+00:00
-- url     : https://prove2.me/theorems/4943f050-3d0e-4a24-aa44-b69a22c855ab
-- title:
--   SDVRPTW instance: nodes, arc set $\mathcal A$, and the triangle inequality
-- statement:
--   This file sets up the data of the **split-delivery vehicle routing problem with time windows** (SDVRPTW) as defined by Desaulniers (2010, §1).
--
--   An unlimited number of identical vehicles of capacity $Q > 0$ are housed at a single depot and serve a set $\mathcal N$ of $n$ customers. The problem lives on a directed graph $\mathcal G = (\mathcal V, \mathcal A)$ whose node set is $\mathcal V = \mathcal N \cup \{0, n+1\}$, where $0$ and $n+1$ are the depot at the beginning and at the end of the planning horizon. An **instance** consists of
--
--   1. the capacity $Q > 0$;
--   2. a positive demand $d_i > 0$ for each customer $i \in \mathcal N$ (the condition $d_i \le Q$ of the VRPTW is *not* imposed, since deliveries may be split);
--   3. a time window $[e_v, l_v]$ for each node $v$, the two depot copies sharing one window: $[e_0, l_0] = [e_{n+1}, l_{n+1}]$;
--   4. nonnegative travel times $t_{vw} \ge 0$, which include the service time at $v$ (service times do not depend on the delivered quantities);
--   5. nonnegative travel costs $c_{vw} \ge 0$.
--
--   The **arc set** $\mathcal A$ contains the idle-vehicle arc $(0, n+1)$ and every arc $(v, w)$ with $v \ne w$, $v \ne n+1$, $w \ne 0$ and
--   $$
--   e_v + t_{vw} \le l_w .
--   $$
--
--   The **triangle inequality**, which the paper assumes throughout, is the pair of conditions
--   $$
--   t_{vx} \le t_{vw} + t_{wx} \quad (v, w, x \text{ pairwise distinct}), \qquad c_{vx} \le c_{vw} + c_{wx} \quad ((v,w), (w,x), (v,x) \in \mathcal A).
--   $$
--
--   These objects are shared by every statement of the mission: the four known properties of optimal SDVRPTW solutions are all stated for an instance satisfying the triangle inequality.
--
--   **Formalization Note** Nodes form the inductive type `Node n` with constructors `start` (node $0$), `cust i` for `i : Fin n` (customers indexed from $0$), and `finish` (node $n+1$). The paper writes "there exists an arc $(i,j) \in \mathcal A$ if $e_i + t_{ij} \le l_j$"; the arc set is read as the set so defined (if and only if). Arcs into the start depot or out of the end depot, which a route from $0$ to $n+1$ never uses, are excluded; only $(n+1, 0)$ is excluded explicitly on the page. The paper defines $t_{vw}$ only for $v \ne w$ and $c_{vw}$ only on arcs; in Lean both are total functions, the unused entries are free data (required nonnegative, which loses no instance), and the triangle inequality is imposed only where the paper's data is defined.
-- source:
--   Desaulniers, Branch-and-Price-and-Cut for the Split-Delivery Vehicle Routing Problem with Time Windows, Operations Research 58(1):179–192 (2010), https://doi.org/10.1287/opre.1090.0713, p. 179, Section 1 (problem definition, triangle inequality assumption)

import Mathlib

namespace SplitDeliveryVRPTW.Known

/-- The nodes of the SDVRPTW graph 𝒢 = (𝒱, 𝒜) (Desaulniers 2010, §1, p. 179):
`start` is the depot at the beginning of the planning horizon (node `0`), `cust i` is
customer `i ∈ 𝒩` (the paper's customer `i + 1`, customers indexed from `0` here), and
`finish` is the depot at the end of the planning horizon (node `n + 1`). -/
inductive Node (n : ℕ) where
  | start : Node n
  | cust : Fin n → Node n
  | finish : Node n
  deriving DecidableEq

/-- An instance of the split-delivery vehicle routing problem with time windows
(Desaulniers 2010, §1, p. 179), with `n` customers:
* `Q` — the capacity of every (identical) vehicle, `0 < Q`;
* `d i` — the positive demand of customer `i` (`d i ≤ Q` is *not* required: split deliveries);
* `[e v, l v]` — the time window of node `v`; the two depot copies share one window;
* `t v w` — the nonnegative travel time from `v` to `w`, service time at `v` included
  (service times do not depend on the delivered quantities);
* `c v w` — the nonnegative travel cost of arc `(v, w)`.
The paper defines `t` only for `v ≠ w` and `c` only on arcs; the remaining entries are
unused data. -/
structure Instance (n : ℕ) where
  Q : ℝ
  d : Fin n → ℝ
  e : Node n → ℝ
  l : Node n → ℝ
  t : Node n → Node n → ℝ
  c : Node n → Node n → ℝ
  Q_pos : 0 < Q
  d_pos : ∀ i, 0 < d i
  depot_window : e .start = e .finish ∧ l .start = l .finish
  t_nonneg : ∀ v w, 0 ≤ t v w
  c_nonneg : ∀ v w, 0 ≤ c v w

/-- The arc set 𝒜 (Desaulniers 2010, §1, p. 179): the idle-vehicle arc `(0, n+1)`, and every
arc `(v, w)` with `v ≠ w` and `e_v + t_vw ≤ l_w`; arcs into the start depot or out of the end
depot are excluded (routes run from `0` to `n + 1`). -/
def Instance.IsArc {n : ℕ} (I : Instance n) (v w : Node n) : Prop :=
  (v = .start ∧ w = .finish) ∨
    (v ≠ w ∧ v ≠ .finish ∧ w ≠ .start ∧ I.e v + I.t v w ≤ I.l w)

/-- The triangle inequality for travel times and costs, assumed throughout the paper
(Desaulniers 2010, §1, p. 179): `t_vx ≤ t_vw + t_wx` for pairwise distinct nodes (the pairs
on which `t` is defined), and `c_vx ≤ c_vw + c_wx` whenever the three arcs belong to 𝒜
(the arcs on which `c` is defined). -/
def Instance.TriangleInequality {n : ℕ} (I : Instance n) : Prop :=
  (∀ v w x : Node n, v ≠ w → w ≠ x → v ≠ x → I.t v x ≤ I.t v w + I.t w x) ∧
    (∀ v w x : Node n, I.IsArc v w → I.IsArc w x → I.IsArc v x →
      I.c v x ≤ I.c v w + I.c w x)

end SplitDeliveryVRPTW.Known


