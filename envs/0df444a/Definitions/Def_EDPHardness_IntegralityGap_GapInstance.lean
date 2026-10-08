-- Prove2me | Definitions.Def_EDPHardness_IntegralityGap_GapInstance
-- name    : EDPHardness_IntegralityGap_GapInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:08.496504+00:00
-- url     : https://prove2.me/theorems/ddb801b6-d9e6-41ba-b948-92328e6bfc2f
-- title:
--   §2.2–2.3 — the random c-uniform hypergraph H, the graph G(H), canonical paths, G′, and the events ℰ₁, ℰ₂, ℰ₃
-- statement:
--   Fix integers $n\ge1$ and $c\ge2$. Write $\log$ for the logarithm to base $2$ and $\ln$ for the natural logarithm, and set
--   $$\beta_1=\frac14\Big(\frac{\log n}{150(\log\log n)^2}\Big)^{1/c},\qquad \beta_2=6(2\beta_1)^{c-1}\ln\beta_1 .$$
--
--   1. **The random hypergraph.** $H$ has vertex set $\{0,\dots,n-1\}$ and $m=\lfloor\beta_2 n\rfloor$ hyperedges $h_0,\dots,h_{m-1}$, each a $c$-element subset of the vertices; the hyperedges are chosen independently and each uniformly among the $c$-subsets (repetitions allowed). Equivalently, $H$ is uniform on the finite set of all such $m$-tuples, and $\Pr[\mathcal E]$ is the fraction of tuples satisfying $\mathcal E$.
--   2. **The graph $G=G(H)$.** Its vertices are $s(v),t(v)$ for every vertex $v$ of $H$ and $\ell_i,r_i$ for every hyperedge $h_i$. Its edges are the **special edges** $(\ell_i,r_i)$, and the **regular edges**: if $v$ lies in the hyperedges $h_{i_1},\dots,h_{i_k}$ with $i_1<\dots<i_k$ and $k\ge1$, the edges $(s(v),\ell_{i_1})$, $(r_{i_k},t(v))$ and $(r_{i_j},\ell_{i_{j+1}})$ for $1\le j\le k-1$; if $v$ lies in no hyperedge ($k=0$), the edge $(s(v),t(v))$. The source–sink pairs are $(s(v),t(v))$, one for every $v$.
--   3. **Canonical paths.** $P(v)=(s(v),\ell_{i_1},r_{i_1},\dots,\ell_{i_k},r_{i_k},t(v))$, which traverses the hyperedges containing $v$ in increasing order; for $k=0$ it is $(s(v),t(v))$.
--   4. **The graph $G'$.** $G'$ is obtained from $G$ by shrinking each special edge $(\ell_i,r_i)$ to a vertex $u_i$; $u_a$ and $u_b$ ($a\ne b$) are adjacent when $(r_a,\ell_b)$ or $(r_b,\ell_a)$ is an edge of $G$.
--   5. **Events.** Let $\deg_H(v)$ be the number of hyperedges containing $v$, and $K_g$ the number of (simple) cycles of length at most $g$ in $G'$.
--      - $\mathcal E_1$: some set $S$ of $\lceil n/\beta_1\rceil$ vertices is **bad**, i.e. contains none of the hyperedges.
--      - $\mathcal E_2$: more than $n/\beta_1$ vertices are **high-degree**, i.e. lie in more than $10\beta_2c$ hyperedges.
--      - $\mathcal E_3$ (for an integer $g$): $K_g>(6\beta_2c^2)^{g+1}$.
--   6. **The length threshold** of the analysis is $g=\lceil 3\beta_1\beta_2c^2\rceil$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The paper treats $\beta_2 n$, $n/\beta_1$ and $3\beta_1\beta_2c^2$ as integers; here the number of hyperedges is $\lfloor\beta_2n\rfloor$, the bad-set size $\lceil n/\beta_1\rceil$, and $g=\lceil3\beta_1\beta_2c^2\rceil$, while the thresholds $n/\beta_1$, $10\beta_2c$ and $(6\beta_2c^2)^{g+1}$ stay real. The edge $(s(v),t(v))$ for a vertex in no hyperedge is a convention the page omits (it is the $k=0$ case of the canonical path; without it such a pair could not be routed at all). $G$ is a simple graph: regular edges $(r_a,\ell_b)$ produced by several vertices are one edge. $G'$ is kept on the vertices $u_i$ only, since $s(v)$ and $t(v)$ lie on no cycle. Cycles are counted once each, as edge sets. The paper's definition of $K_g$ says "cycles … in $G$"; its proof and its use count cycles in $G'$, which is what is formalized. The canonical path is recorded by its vertex sequence.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), p. 491 (β₁, β₂), pp. 492–494, Sections 2.2–2.3 (H, ℰ₁, ℰ₂, G, canonical paths, G′, K_g, ℰ₃), p. 495, Section 2.4 (g)

import Mathlib

namespace EDPHardness.IntegralityGap

/-! # The random-hypergraph integrality-gap instance of Andrews et al. (2010), §2.2–2.3 -/

/-- `β₁ = ¼ · (log n / (150 (log log n)²))^{1/c}` (p. 491), with `log = log₂`. -/
noncomputable def beta1 (n c : ℕ) : ℝ :=
  (1 / 4) * (Real.logb 2 n / (150 * (Real.logb 2 (Real.logb 2 n)) ^ 2)) ^ ((1 : ℝ) / c)

/-- `β₂ = 6 (2β₁)^{c−1} ln β₁` (p. 491), with `ln` the natural logarithm. -/
noncomputable def beta2 (n c : ℕ) : ℝ :=
  6 * (2 * beta1 n c) ^ (c - 1) * Real.log (beta1 n c)

/-- The number of hyperedges, `⌊β₂ n⌋` (the paper's `β₂n`). -/
noncomputable def numEdges (n c : ℕ) : ℕ := ⌊beta2 n c * n⌋₊

/-- The size of a bad set, `⌈n/β₁⌉` (the paper's `n/β₁`). -/
noncomputable def badSize (n c : ℕ) : ℕ := ⌈(n : ℝ) / beta1 n c⌉₊

/-- The length threshold of §2.4, `g = ⌈3 β₁ β₂ c²⌉` (the paper's `g = 3β₁β₂c²`). -/
noncomputable def gParam (n c : ℕ) : ℕ := ⌈3 * beta1 n c * beta2 n c * (c : ℝ) ^ 2⌉₊

/-- A hypergraph on the vertex set `Fin n` with `m` hyperedges `h₀, …, h_{m−1}`, each a
`c`-element subset (§2.2). Repetitions are allowed. -/
abbrev Hyp (n m c : ℕ) := Fin m → {s : Finset (Fin n) // s.card = c}

/-- The probability of an event under the random hypergraph of §2.2: the `m` hyperedges are
independent and each is uniform over the `c`-subsets of `Fin n`, i.e. `H` is uniform on
`Hyp n m c`. -/
noncomputable def hypProb (n m c : ℕ) (E : Hyp n m c → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter E).card : ℝ) / (Fintype.card (Hyp n m c) : ℝ)

/-- The vertices of the EDP instance `G(H)` (§2.3): `s(v), t(v)` for each vertex `v` of `H`, and
`ℓᵢ, rᵢ` for each hyperedge `hᵢ`. -/
inductive Node (n m : ℕ)
  | s (v : Fin n)
  | t (v : Fin n)
  | l (i : Fin m)
  | r (i : Fin m)
  deriving DecidableEq

/-- The edge rules of §2.3 (one orientation of each edge).
* special edge `(ℓᵢ, rᵢ)` for each `i`;
* `(s(v), ℓ_{i₁})` where `h_{i₁}` is the first hyperedge containing `v`;
* `(r_{i_k}, t(v))` where `h_{i_k}` is the last hyperedge containing `v`;
* `(r_a, ℓ_b)` when `a < b`, and for some `v ∈ h_a ∩ h_b` no `h_j` with `a < j < b` contains `v`
  (consecutive hyperedges of `v`);
* `(s(v), t(v))` when `v` lies in no hyperedge (degree-zero convention, not on the page). -/
inductive GapRel {n m c : ℕ} (H : Hyp n m c) : Node n m → Node n m → Prop
  | special (i : Fin m) : GapRel H (.l i) (.r i)
  | first (v : Fin n) (i : Fin m) (hv : v ∈ (H i).1) (hmin : ∀ j < i, v ∉ (H j).1) :
      GapRel H (.s v) (.l i)
  | last (v : Fin n) (i : Fin m) (hv : v ∈ (H i).1) (hmax : ∀ j, i < j → v ∉ (H j).1) :
      GapRel H (.r i) (.t v)
  | consec (v : Fin n) (a b : Fin m) (hab : a < b) (ha : v ∈ (H a).1) (hb : v ∈ (H b).1)
      (hbetween : ∀ j, a < j → j < b → v ∉ (H j).1) : GapRel H (.r a) (.l b)
  | isolated (v : Fin n) (hv : ∀ i, v ∉ (H i).1) : GapRel H (.s v) (.t v)

/-- The graph `G = G(H)` of §2.3, as a simple graph (coinciding regular edges are one edge). -/
def gapGraph {n m c : ℕ} (H : Hyp n m c) : SimpleGraph (Node n m) :=
  SimpleGraph.fromRel (GapRel H)

/-- The source of pair `v`. -/
def src (n m : ℕ) (v : Fin n) : Node n m := .s v

/-- The sink of pair `v`. -/
def snk (n m : ℕ) (v : Fin n) : Node n m := .t v

/-- The vertex sequence of the canonical path
`P(v) = (s(v), ℓ_{i₁}, r_{i₁}, …, ℓ_{i_k}, r_{i_k}, t(v))`, `i₁ < ⋯ < i_k` the hyperedges
containing `v` (for `k = 0`, `P(v) = (s(v), t(v))`). -/
def canonicalSupport {n m c : ℕ} (H : Hyp n m c) (v : Fin n) : List (Node n m) :=
  Node.s v :: (((List.finRange m).filter (fun i => decide (v ∈ (H i).1))).flatMap
    (fun i => [Node.l i, Node.r i]) ++ [Node.t v])

/-- `G′` (p. 493): `G(H)` with each special edge `(ℓᵢ, rᵢ)` shrunk to a vertex `uᵢ`, restricted to
the vertices `uᵢ` (the vertices `s(v), t(v)` lie on no cycle). `uₐ ∼ u_b` iff `(r_a, ℓ_b)` or
`(r_b, ℓ_a)` is an edge of `G(H)`. -/
def contracted {n m c : ℕ} (H : Hyp n m c) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun a b => (gapGraph H).Adj (.r a) (.l b))

/-- `deg_H(v)`, the number of hyperedges containing `v`. -/
def degH {n m c : ℕ} (H : Hyp n m c) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => v ∈ (H i).1)).card

/-- Event `ℰ₁` (p. 492): some set `S` of size `⌈n/β₁⌉` is bad, i.e. contains no hyperedge. -/
def E1 (n c : ℕ) {m : ℕ} (H : Hyp n m c) : Prop :=
  ∃ S : Finset (Fin n), S.card = badSize n c ∧ ∀ i, ¬ (H i).1 ⊆ S

/-- Event `ℰ₂` (p. 493): more than `n/β₁` vertices are high-degree (in more than `10β₂c`
hyperedges). -/
def E2 (n c : ℕ) {m : ℕ} (H : Hyp n m c) : Prop :=
  (((Finset.univ.filter (fun v => 10 * beta2 n c * c < (degH H v : ℝ))).card : ℕ) : ℝ)
    > (n : ℝ) / beta1 n c

/-- `K_g`: the number of (simple) cycles of length at most `g` in `G′`, each cycle counted once
as its edge set. -/
noncomputable def cycleCount {n m c : ℕ} (H : Hyp n m c) (g : ℕ) : ℕ :=
  {S : Finset (Sym2 (Fin m)) |
    ∃ (u : Fin m) (p : (contracted H).Walk u u), p.IsCycle ∧ p.length ≤ g ∧
      p.edges.toFinset = S}.ncard

/-- Event `ℰ₃` for the value `g` (p. 494): `K_g > (6β₂c²)^{g+1}`. -/
def E3 (n c : ℕ) {m : ℕ} (g : ℕ) (H : Hyp n m c) : Prop :=
  (cycleCount H g : ℝ) > (6 * beta2 n c * (c : ℝ) ^ 2) ^ (g + 1)

end EDPHardness.IntegralityGap


