-- Prove2me | Definitions.Def_SemiStreamMWM_Graph
-- name    : SemiStreamMWM_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:14:31.901733+00:00
-- url     : https://prove2.me/theorems/a81e8d1e-53b1-4a34-be70-945597c05908
-- title:
--   §1, §1.3, §2.1 — matchings, $\mu(G)$, $\mu_w(G)$, the matching polytope $\mathcal P_G$ and its truncation $\mathcal P_{G,\delta}$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph. A **matching** is a set of edges no two of which share a vertex. $\mu(G)$ is the largest cardinality of a matching and, for integer edge weights $w_e$, $\mu_w(G)$ is the largest weight $w(M)=\sum_{e\in M}w_e$ of a matching; both are attained, and the empty matching gives $0$.
--
--   For $x\in\mathbb R^E$ write $x_v=\sum_{e\ni v}x_e$ for the degree of a vertex $v$ and $x(S)=\sum_{e\in E[S]}x_e$ for the mass of the edges with both endpoints in $S\subseteq V$. The **matching polytope** $\mathcal P_G$ is the convex hull of the indicator vectors $\vec 1_M$ of all matchings. For $\delta\ge 0$ the **truncated matching polytope** is
--
--   $$\mathcal P_{G,\delta}=\{x\in\mathbb R^E_{\ge 0}:\ x_v\le 1-2\delta\ \ \forall v\in V;\ \ x(S)\le (|S|-1)/2\ \ \forall S\in\mathcal O_G\},$$
--
--   where $\mathcal O_G$ is the family of odd vertex sets. Under real edge weights $r$ and for a set of edges $H$, an $(\alpha,\beta)$-MWM in $H$ is a matching $M\subseteq H$ with $r(M)\ge\alpha\cdot\max_{M'\subseteq H}r(M')-\beta$. The paper's standing weight assumption is that weights are integers in $[1,W]$ with $W\ge 8$ a power of two.
--
--   These objects are shared by every statement of the mission: the framework of §2 optimizes over $\mathcal P_G$ while keeping its iterates in $\mathcal P_{G,\delta}$.
--
--   **Formalization Note** Edges are the subtype `G.edgeSet` of `Sym2 V`, vectors are functions on it, and a matching is a `Finset` of edges. Odd sets include singletons, for which the constraint is $x(S)\le 0$. The $(\alpha,\beta)$ condition is stated against every matching inside $H$, which is the same as against the maximum when $\alpha\ge0$.
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), §1 p.3; §1.1 p.5; §1.3 p.8; §2.1 p.10; footnote 1 p.3

import Mathlib

open Classical

namespace SemiStreamMWM

/-! # Matchings, the matching polytope and its truncation

J. Chen, *Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs:
A Unified Framework* (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), §1 p.3 (matchings,
µ_w(G), µ(G)), §1.1 p.5 (the matching polytope P_G, x_v, x(S), O_G), §1.3 p.8 ((α, β)-MWM),
§2.1 p.10 (the truncated matching polytope P_{G,δ}), footnote 1 p.3 (W ≥ 8 a power of two).

**Formalization Note.** A graph is a `SimpleGraph V` on a finite vertex type; its edges are the
subtype `G.edgeSet` of `Sym2 V`, and a vector `x ∈ ℝ^E` is a function `G.edgeSet → ℝ`. A matching
is a finite set of edges, no two of which share a vertex. Integer weights are a function
`w : Sym2 V → ℕ`; only its values on edges are ever used. `µ(G)` (`mcm`) and `µ_w(G)` (`mwm`) are
maxima over the finite, nonempty set of matchings (the empty matching gives `0`). The polytope
`P_G` is, as on p.5, the convex hull of the indicator vectors of matchings. Odd sets include
singletons (`O_G` is the family of odd vertex sets); for them the constraint reads `x(S) ≤ 0` and
holds for every nonnegative `x`. All subtractions in the constraints are real. -/

variable {V : Type*} [Fintype V]

/-- A matching of `G` (p.3): a set of edges, no two of which share a vertex. -/
def IsMatching (G : SimpleGraph V) (M : Finset G.edgeSet) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v ∈ (e : Sym2 V), v ∉ (f : Sym2 V)

/-- The finite set of all matchings of `G`. -/
noncomputable def matchings (G : SimpleGraph V) : Finset (Finset G.edgeSet) :=
  Finset.univ.filter (IsMatching G)

/-- `µ(G)`: the maximum cardinality of a matching (p.3). -/
noncomputable def mcm (G : SimpleGraph V) : ℕ :=
  (matchings G).sup Finset.card

/-- `µ_w(G)`: the maximum weight `w(M) = Σ_{e∈M} w_e` of a matching (p.3). -/
noncomputable def mwm (G : SimpleGraph V) (w : Sym2 V → ℕ) : ℕ :=
  (matchings G).sup fun M => ∑ e ∈ M, w e.1

/-- The number of edges `m = |E|`. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

/-- The indicator vector `1_M ∈ ℝ^E` of a set of edges. -/
noncomputable def ind (G : SimpleGraph V) (M : Finset G.edgeSet) : G.edgeSet → ℝ :=
  fun e => if e ∈ M then 1 else 0

/-- The weight vector `w ∈ ℝ^E`. -/
def weightVec (G : SimpleGraph V) (w : Sym2 V → ℕ) : G.edgeSet → ℝ :=
  fun e => (w e.1 : ℝ)

/-- The inner product `r^⊤x = Σ_e r_e x_e` on `ℝ^E`. -/
noncomputable def wdot (G : SimpleGraph V) (r x : G.edgeSet → ℝ) : ℝ :=
  ∑ e, r e * x e

/-- The matching polytope `P_G` (p.5): the convex hull of the indicator vectors of all matchings. -/
noncomputable def matchingPolytope (G : SimpleGraph V) : Set (G.edgeSet → ℝ) :=
  convexHull ℝ (ind G '' {M | IsMatching G M})

/-- `x_v = Σ_{e∋v} x_e = (Ax)_v`, the degree of `v` under `x` (p.5). -/
noncomputable def deg (G : SimpleGraph V) (x : G.edgeSet → ℝ) (v : V) : ℝ :=
  ∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then x e else 0

/-- `x(S) = Σ_{e∈E[S]} x_e`, the mass of the edges with both endpoints in `S` (p.5). -/
noncomputable def inside (G : SimpleGraph V) (x : G.edgeSet → ℝ) (S : Finset V) : ℝ :=
  ∑ e : G.edgeSet, if ∀ v ∈ (e : Sym2 V), v ∈ S then x e else 0

/-- The truncated matching polytope (p.10):
`P_{G,δ} = {x ∈ ℝ^E_{≥0} : x_v ≤ 1 − 2δ ∀v ∈ V; x(S) ≤ (|S| − 1)/2 ∀S ∈ O_G}`. -/
def truncPolytope (G : SimpleGraph V) (δ : ℝ) : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v, deg G x v ≤ 1 - 2 * δ) ∧
    ∀ S : Finset V, Odd S.card → inside G x S ≤ ((S.card : ℝ) - 1) / 2}

/-- `M` is an `(α, β)`-MWM in the edge set `H` under real edge weights `r` (p.8): a matching inside
`H` whose weight is at least `α` times the best weight of a matching inside `H`, minus `β`.
Stated against every matching `M'` inside `H`, which is the same as against the maximum for
`α ≥ 0`. A `(1 − δ)`-MWM is a `(1 − δ, 0)`-MWM. -/
def IsApproxMWM (G : SimpleGraph V) (r : G.edgeSet → ℝ) (H : Finset G.edgeSet) (α β : ℝ)
    (M : Finset G.edgeSet) : Prop :=
  IsMatching G M ∧ M ⊆ H ∧
    ∀ M' : Finset G.edgeSet, IsMatching G M' → M' ⊆ H → α * (∑ e ∈ M', r e) - β ≤ ∑ e ∈ M, r e

/-- The paper's standing weight assumptions (p.3 and footnote 1): integer edge weights in `[1, W]`,
and `W ≥ 8` a power of two. -/
def Standing (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) : Prop :=
  (∀ e ∈ G.edgeSet, 1 ≤ w e ∧ w e ≤ W) ∧ 8 ≤ W ∧ ∃ j : ℕ, W = 2 ^ j

end SemiStreamMWM


