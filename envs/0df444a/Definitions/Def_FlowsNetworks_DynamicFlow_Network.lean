-- Prove2me | Definitions.Def_FlowsNetworks_DynamicFlow_Network
-- name    : FlowsNetworks_DynamicFlow_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:21.269076+00:00
-- url     : https://prove2.me/theorems/6b6182bf-116e-407f-b806-fbd6fe4c9c9f
-- title:
--   Network $[N; \mathcal A]$ with integer capacities and costs; static flows, the optimality properties (3.18)–(3.20), arc numbers, the dual program, chains and paths
-- statement:
--   Following Chapter I (§§1–2) and Chapter III (§3) of Ford and Fulkerson's *Flows in Networks*, this file sets up the static objects of the minimal cost flow problem.
--
--   1. A **network** $G = [N; \mathcal A]$ consists of a finite set $N$ of **nodes** and a set $\mathcal A$ of ordered pairs $(x, y)$ of nodes, the **arcs**, with $x \neq y$. There is at most one arc from $x$ to $y$, but both $(x, y)$ and $(y, x)$ may be arcs. Every arc carries a **capacity** $c(x, y)$, a positive integer, and a **cost** $a(x, y)$, a nonnegative integer; in §9 the cost is the **traversal time** of the arc.
--   2. For node sets $X, Y$ and a real function $g$ on the arcs, $g(X, Y) = \sum_{(x, y) \in \mathcal A,\ x \in X,\ y \in Y} g(x, y)$.
--   3. A **flow from $s$ to $t$ with value $v$** is a real function $f$ on the arcs with
--   $$f(s, N) - f(N, s) = v, \qquad f(x, N) - f(N, x) = 0 \ (x \neq s, t), \qquad f(t, N) - f(N, t) = -v, \qquad 0 \le f(x, y) \le c(x, y).$$
--   Its **total cost** is $\sum_{\mathcal A} a(x, y) f(x, y)$. The **$p$-th related program** (3.7)–(3.11) maximizes $pv - \sum_{\mathcal A} a(x, y) f(x, y)$ over flows.
--   4. Integer **node numbers** $\pi$ and a flow $f$ satisfy the **optimality properties** for the $p$-th related program if, for every arc $(x, y)$,
--   $$\text{(3.18)}\ \pi(s) = 0,\ \pi(t) = p; \qquad \text{(3.19)}\ \pi(y) - \pi(x) < a(x, y) \Rightarrow f(x, y) = 0; \qquad \text{(3.20)}\ \pi(y) - \pi(x) > a(x, y) \Rightarrow f(x, y) = c(x, y).$$
--   The **arc numbers** are (3.21) $\gamma(x, y) = \max(0, \pi(y) - \pi(x) - a(x, y))$.
--   5. The **dual program** (3.12)–(3.15): real $\pi$, $\gamma$ with $-\pi(s) + \pi(t) = p$, $\pi(x) - \pi(y) + \gamma(x, y) \ge -a(x, y)$ and $\gamma(x, y) \ge 0$ on every arc, minimizing $\sum_{\mathcal A} c(x, y) \gamma(x, y)$.
--   6. A **chain** from $s$ to $t$ is a sequence $x_1, \dots, x_k$ ($k \ge 2$) of distinct nodes with $x_1 = s$, $x_k = t$ and every $(x_i, x_{i+1})$ an arc. A **path** from $s$ to $t$ is a sequence of distinct nodes from $s$ to $t$ where each step uses either the forward arc $(x_i, x_{i+1})$ or the reverse arc $(x_{i+1}, x_i)$; its **path cost** is the sum of the costs of its forward arcs minus the sum of the costs of its reverse arcs.
--
--   **Formalization Note** Nodes form a `Fintype` with decidable equality, arcs a `Finset (N × N)`. Capacities and costs are natural numbers (the book's positive and nonnegative integers), with $c > 0$ on arcs as a field; the positivity of the traversal times in §9 is a hypothesis of the §9 statements. Flows are real functions that vanish off $\mathcal A$. A flow is defined in Chapter I's net form; §3 adjoins $s$ and $t$ so that no arc enters $s$ or leaves $t$, and then the net form is exactly (3.7)–(3.10). Chains are lists of nodes; a path is an injective map $\{0, \dots, n\} \to N$ with a Boolean choice of direction per step.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, pp. 3–5 (§1, networks, chains (1.1), paths), p. 7 (§2, flows (2.1)–(2.2)); Chapter III, pp. 35–38 (§3, (3.6)–(3.21)), p. 43 (path cost)

import Mathlib

namespace FlowsNetworks.DynamicFlow

/-- A directed network `[N; 𝒜]` with arc capacities `c(x, y)` and arc costs `a(x, y)`
(Ford–Fulkerson, *Flows in Networks*, Chapter I, pp. 3–4 and 7; Chapter III, §3 p. 35 and §9
p. 81). The node set `N` is a finite type; the arc set `𝒜` is a finite set of ordered pairs, so
there is at most one arc from `x` to `y`, while both `(x, y)` and `(y, x)` may be arcs. Arcs are
loop-free (`x ≠ y`). Capacities are positive integers and costs nonnegative integers ("We suppose
throughout that … c(x, y) are positive integers, a(x, y) nonnegative integers", p. 35). In §9 the
cost `a(x, y)` is the traversal time of the arc, a positive integer (p. 81); that extra positivity
is a hypothesis of the §9 statements. Values of `cap` and `cost` off `𝒜` play no role. -/
structure Network (N : Type) [Fintype N] [DecidableEq N] where
  /-- the arc set `𝒜 ⊆ N × N` -/
  arcs : Finset (N × N)
  /-- no arc leads from a node to itself -/
  loopless : ∀ q ∈ arcs, q.1 ≠ q.2
  /-- the capacity `c(x, y)` -/
  cap : N → N → ℕ
  /-- capacities are positive integers -/
  cap_pos : ∀ q ∈ arcs, 0 < cap q.1 q.2
  /-- the arc cost `a(x, y)` (§3), the traversal time of the arc (§9) -/
  cost : N → N → ℕ

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The book's notation `g(X, Y) = ∑ g(x, y)`, the sum over all arcs `(x, y) ∈ 𝒜` with `x ∈ X` and
`y ∈ Y` (Chapter I, §3). -/
def arcSum (G : Network N) (g : N → N → ℝ) (X Y : Finset N) : ℝ :=
  ∑ q ∈ G.arcs.filter (fun q => q.1 ∈ X ∧ q.2 ∈ Y), g q.1 q.2

/-- `f(x, N) − f(N, x)`: the net flow out of the node `x`. -/
def netOut (G : Network N) (f : N → N → ℝ) (x : N) : ℝ :=
  arcSum G f {x} Finset.univ - arcSum G f Finset.univ {x}

/-- A (static, node-arc) flow from `s` to `t` with value `v` (Chapter I, (2.1)–(2.2); Chapter III,
(3.7)–(3.10)): a function on the arcs (zero off `𝒜`) with `0 ≤ f(x, y) ≤ c(x, y)` on every arc,
`f(s, N) − f(N, s) = v`, `f(x, N) − f(N, x) = 0` for `x ≠ s, t`, and `f(t, N) − f(N, t) = −v`. When
no arc enters `s` and no arc leaves `t`, as §3 arranges, these are exactly (3.7)–(3.10). -/
def IsStaticFlow (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) : Prop :=
  (∀ x y, (x, y) ∉ G.arcs → f x y = 0) ∧
  (∀ q ∈ G.arcs, 0 ≤ f q.1 q.2 ∧ f q.1 q.2 ≤ (G.cap q.1 q.2 : ℝ)) ∧
  netOut G f s = v ∧
  (∀ x, x ≠ s → x ≠ t → netOut G f x = 0) ∧
  netOut G f t = -v

/-- The flow is integral valued. -/
def IsIntegral (f : N → N → ℝ) : Prop :=
  ∀ x y, ∃ n : ℤ, f x y = n

/-- The total cost `∑_𝒜 a(x, y) f(x, y)`. -/
def totalCost (G : Network N) (f : N → N → ℝ) : ℝ :=
  ∑ q ∈ G.arcs, (G.cost q.1 q.2 : ℝ) * f q.1 q.2

/-- The optimality properties (3.18), (3.19), (3.20) of a flow `f` and integer node numbers `π`
for the `p`-th related program (Chapter III, p. 38):
`π(s) = 0`, `π(t) = p`; `π(y) − π(x) < a(x, y) ⇒ f(x, y) = 0`;
`π(y) − π(x) > a(x, y) ⇒ f(x, y) = c(x, y)`, for every arc `(x, y)`. -/
def OptimalityProperties (G : Network N) (s t : N) (p : ℕ) (f : N → N → ℝ) (π : N → ℤ) :
    Prop :=
  π s = 0 ∧ π t = (p : ℤ) ∧
  ∀ q ∈ G.arcs,
    (π q.2 - π q.1 < (G.cost q.1 q.2 : ℤ) → f q.1 q.2 = 0) ∧
    ((G.cost q.1 q.2 : ℤ) < π q.2 - π q.1 → f q.1 q.2 = (G.cap q.1 q.2 : ℝ))

/-- The arc numbers (3.21): `γ(x, y) = max(0, π(y) − π(x) − a(x, y))`. -/
def arcNumber (G : Network N) (π : N → ℤ) (x y : N) : ℤ :=
  max 0 (π y - π x - (G.cost x y : ℤ))

/-- Feasibility for the dual (3.12)–(3.14) of the `p`-th related program, for real node numbers
`π` and arc numbers `γ`: `−π(s) + π(t) = p`; `π(x) − π(y) + γ(x, y) ≥ −a(x, y)` and
`γ(x, y) ≥ 0` for every arc `(x, y)`. -/
def IsDualFeasible (G : Network N) (s t : N) (p : ℕ) (π : N → ℝ) (γ : N → N → ℝ) : Prop :=
  -π s + π t = (p : ℝ) ∧
  ∀ q ∈ G.arcs,
    -(G.cost q.1 q.2 : ℝ) ≤ π q.1 - π q.2 + γ q.1 q.2 ∧ 0 ≤ γ q.1 q.2

/-- The dual objective (3.15): `∑_𝒜 c(x, y) γ(x, y)`. -/
def dualObjective (G : Network N) (γ : N → N → ℝ) : ℝ :=
  ∑ q ∈ G.arcs, (G.cap q.1 q.2 : ℝ) * γ q.1 q.2

/-- A chain from `s` to `t` (Chapter I, (1.1), p. 4), recorded by its list of nodes
`x₁, …, x_k`: `k ≥ 2` distinct nodes with `x₁ = s`, `x_k = t`, and `(x_i, x_{i+1})` an arc for
each `i = 1, …, k − 1`. -/
def IsChainFromTo (G : Network N) (s t : N) (l : List N) : Prop :=
  2 ≤ l.length ∧ l.Nodup ∧ l.head? = some s ∧ l.getLast? = some t ∧
    ∀ (i : ℕ) (h : i + 1 < l.length), (l[i], l[i + 1]) ∈ G.arcs

/-- `∑_{i=1}^{k−1} g(x_i, x_{i+1})` along the node list `x₁, …, x_k` (an integer-valued `g`). -/
def chainSum (g : N → N → ℤ) (l : List N) : ℤ :=
  (List.zipWith g l l.tail).sum

/-- A path from `s` to `t` (Chapter I, p. 5): distinct nodes `s = x₀, x₁, …, xₙ = t` together
with, for each step `i`, a selected arc that is either the forward arc `(xᵢ, xᵢ₊₁)` (when
`fwd i = true`) or the reverse arc `(xᵢ₊₁, xᵢ)` (when `fwd i = false`). -/
def IsPathFromTo (G : Network N) (s t : N) {n : ℕ} (x : Fin (n + 1) → N) (fwd : Fin n → Bool) :
    Prop :=
  Function.Injective x ∧ x 0 = s ∧ x (Fin.last n) = t ∧
    ∀ i : Fin n,
      (fwd i = true → (x i.castSucc, x i.succ) ∈ G.arcs) ∧
      (fwd i = false → (x i.succ, x i.castSucc) ∈ G.arcs)

/-- The path cost (Chapter III, p. 43): the sum of the arc costs of the forward arcs of the path
minus the sum of the arc costs of its reverse arcs. -/
def pathCost (G : Network N) {n : ℕ} (x : Fin (n + 1) → N) (fwd : Fin n → Bool) : ℤ :=
  ∑ i : Fin n,
    if fwd i then (G.cost (x i.castSucc) (x i.succ) : ℤ) else -(G.cost (x i.succ) (x i.castSucc) : ℤ)

end FlowsNetworks.DynamicFlow


