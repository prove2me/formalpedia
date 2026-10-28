-- Prove2me | Definitions.Def_NSWApxHard_Reduction_Instance
-- name    : NSWApxHard_Reduction_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:33.181769+00:00
-- url     : https://prove2.me/theorems/febda02b-2085-4c21-90c5-de7070ea9557
-- title:
--   The reduction from 3-regular Vertex Cover to Nash social welfare and the rule of Lemma 2.3 (pp. 2–3)
-- statement:
--   Let $G=(V,E)$ be a graph on $V=\{0,\dots,N-1\}$, let $k$ be a natural number (the paper's $c_{\min}N$) and $\alpha$ a real number (the paper takes $\alpha\in(1/3,1/2)$). The **reduced instance** (Lee, p. 2) has
--   1. a *vertex agent* $a(v)$ for every vertex $v$ and an *edge agent* $a(e)$ for every edge $e$;
--   2. $k$ identical *vertex items*, each worth $1$ to every vertex agent and $0$ to every edge agent;
--   3. an *edge item* $i(e)$ for every edge $e$, worth $1-\alpha$ to $a(e)$ and $0$ to every other agent;
--   4. a *shared item* $i(v,e)$ for every pair with $v\in e$, worth $1/3$ to $a(v)$, $\alpha$ to $a(e)$ and $0$ to every other agent.
--
--   For an allocation $x$ (a map from items to agents) let $\mathrm{vItems}_x(v)$ be the number of vertex items held by $a(v)$, and for an agent $b$ and a shared item $s$ let $\mathrm{other}_x(b,s)$ be the number of shared items other than $s$ held by $b$. The **rule of Lemma 2.3** (p. 3) holds for the shared item $s=i(v,e)$ when $x(s)$ is
--   $$\begin{cases} a(e) & \text{if } \mathrm{vItems}_x(v)=1,\\ a(v) & \text{else if } \mathrm{other}_x(a(e),s)=1,\\ a(e) & \text{else if } \mathrm{other}_x(a(v),s)=2,\\ a(v) & \text{otherwise.}\end{cases}$$
--
--   These objects carry the completeness and soundness analysis of the reduction (Lemmas 2.2–2.4).
--
--   **Formalization Note** Edges are the elements of $G$'s edge set in `Sym2 (Fin N)`; shared items are the pairs $(v,e)$ with $e$ an edge and $v\in e$. Agents are `Fin N ⊕ Edge G`, items `Fin k ⊕ (Edge G ⊕ Inc G)`. The number of vertex items is a natural number $k$ because $c_{\min}N$ need not be an integer. "Has 1 shared item other than $i(v,e)$" is read literally as a count of all shared items other than $i(v,e)$ held by the agent; in an optimal allocation no agent holds an item worth $0$ to it, so this is the count of the agent's own shared items.
-- source:
--   Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, arXiv:1507.01159v1, p. 2 (the reduction: vertex/edge agents, vertex/edge/shared items) and p. 3, Lemma 2.3 (rules 1–4)

import Mathlib
import Definitions.Def_NSWApxHard_Reduction_CubicVC

namespace NSWApxHard.Reduction

open Finset

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-- The edges of `G`. -/
abbrev Edge : Type := {e : Sym2 (Fin N) // e ∈ G.edgeFinset}

/-- The vertex-edge pairs `(v, e)` with `v ∈ e`. -/
abbrev Inc : Type := {p : Fin N × Sym2 (Fin N) // p.2 ∈ G.edgeFinset ∧ p.1 ∈ p.2}

/-- The agents of the reduced instance (Lee, p. 2): a vertex agent `a(v)` (`inl v`) for every
vertex and an edge agent `a(e)` (`inr e`) for every edge. -/
abbrev Agent : Type := Fin N ⊕ Edge G

/-- The items of the reduced instance (Lee, p. 2): `k` vertex items (`inl j`), an edge item
`i(e)` (`inr (inl e)`) for every edge, and a shared item `i(v, e)` (`inr (inr (v, e))`) for every
vertex-edge pair with `v ∈ e`. -/
abbrev Item (k : ℕ) : Type := Fin k ⊕ (Edge G ⊕ Inc G)

variable {G}

/-- The vertex agent `a(v)` of the shared item `i(v, e)`. -/
def Inc.vAgent (s : Inc G) : Agent G := Sum.inl s.1.1

/-- The edge agent `a(e)` of the shared item `i(v, e)`. -/
def Inc.eAgent (s : Inc G) : Agent G := Sum.inr ⟨s.1.2, s.2.1⟩

/-- The shared item `i(v, e)` as an item. -/
def Inc.item {k : ℕ} (s : Inc G) : Item G k := Sum.inr (Sum.inr s)

variable (G)

/-- The utilities of the reduced instance (Lee, p. 2): a vertex item is worth 1 to every vertex
agent and 0 to every edge agent; the edge item `i(e)` is worth `1 - α` to `a(e)` and 0 to every
other agent; the shared item `i(v, e)` is worth `1/3` to `a(v)`, `α` to `a(e)` and 0 to every
other agent. -/
noncomputable def redUtil (k : ℕ) (α : ℝ) : Agent G → Item G k → ℝ
  | Sum.inl _, Sum.inl _ => 1
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inl _, Sum.inr (Sum.inl _) => 0
  | Sum.inr e, Sum.inr (Sum.inl e') => if e = e' then 1 - α else 0
  | Sum.inl v, Sum.inr (Sum.inr s) => if s.1.1 = v then 1 / 3 else 0
  | Sum.inr e, Sum.inr (Sum.inr s) => if e.1 = s.1.2 then α else 0

variable {G}

/-- The number of vertex items the vertex agent `a(v)` holds under the allocation `x`. -/
def vItems {k : ℕ} (x : Item G k → Agent G) (v : Fin N) : ℕ :=
  (univ.filter (fun j : Fin k => x (Sum.inl j) = Sum.inl v)).card

/-- The number of shared items other than `s` that the agent `ag` holds under `x`. -/
def sharedOther {k : ℕ} (x : Item G k → Agent G) (ag : Agent G) (s : Inc G) : ℕ :=
  (univ.filter (fun s' : Inc G => s' ≠ s ∧ x (Sum.inr (Sum.inr s')) = ag)).card

/-- The rule of Lemma 2.3 (Lee, p. 3) for the shared item `s = i(v, e)` under the allocation `x`:
1. if `a(v)` has 1 vertex item, `a(e)` gets `i(v, e)`;
2. elseif `a(e)` has 1 shared item other than `i(v, e)`, `a(v)` gets `i(v, e)`;
3. elseif `a(v)` has 2 shared items other than `i(v, e)`, `a(e)` gets `i(v, e)`;
4. else `a(v)` gets `i(v, e)`. -/
def Rule {k : ℕ} (x : Item G k → Agent G) (s : Inc G) : Prop :=
  x s.item =
    if vItems x s.1.1 = 1 then s.eAgent
    else if sharedOther x s.eAgent s = 1 then s.vAgent
    else if sharedOther x s.vAgent s = 2 then s.eAgent
    else s.vAgent

end NSWApxHard.Reduction


