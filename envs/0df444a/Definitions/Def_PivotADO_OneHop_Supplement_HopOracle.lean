-- Prove2me | Definitions.Def_PivotADO_OneHop_Supplement_HopOracle
-- name    : PivotADO_OneHop_Supplement_HopOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:55:23.551591+00:00
-- url     : https://prove2.me/theorems/981b3f7c-98d5-477b-95aa-2da9b34a06cf
-- title:
--   Definition 3 — $r$-pivot $\beta$-hop $k$-stretch approximate distance oracles
-- statement:
--   Let $G=(V,E)$ be an undirected, unweighted simple graph with shortest-path distance $\delta_G$. Let $r,\beta\ge1$ be integers and $k\ge1$. An **$r$-pivot $\beta$-hop $k$-stretch ADO** for $G$ consists of
--
--   1. a weighted undirected graph $H=(V,E_H,w_H)$ with $w_H(x,y)\ge\delta_G(x,y)$ for every $(x,y)\in E_H$, where by convention $w_H(a,a)=0$ and $w_H(x,y)=\infty$ for $x\ne y$ with $(x,y)\notin E_H$;
--   2. a set $P(v)\subseteq V$ of at most $r$ **pivots** for every $v\in V$, with $v\in P(v)$,
--
--   such that for all $u,v\in V$,
--
--   $$\delta_G(u,v)\le d^{\le\beta}_{H,P}(u,v)\le k\,\delta_G(u,v).$$
--
--   Here $d^{\le\beta}_{H,P}(u,v)$ is the minimum of
--
--   $$w_H(u,p_u)+\sum_{i=1}^{j}w_H\bigl(p'_{x_{i-1}},p_{x_i}\bigr)+\sum_{i=1}^{j-1}\Bigl(w_H(p_{x_i},x_i)+w_H(x_i,p'_{x_i})\Bigr)+w_H(p_v,v)$$
--
--   over all $1\le j\le\beta$, all vertices $x_1,\dots,x_{j-1}\in V$, and all pivots $p_u\in P(u)$, $p_v\in P(v)$ and $p_{x_i},p'_{x_i}\in P(x_i)$, where $p'_{x_0}=p_u$ and $p_{x_j}=p_v$. This is the weight of the walk $u\to p_u\to p_{x_1}\to x_1\to p'_{x_1}\to\cdots\to p_{x_{j-1}}\to x_{j-1}\to p'_{x_{j-1}}\to p_v\to v$ with $j$ stored hops; the pivot jumps do not count as hops. The **space** of the oracle is $|E_H|$.
--
--   This model is the object of Theorem 2; for $\beta=1$ it is the one-hop model of the mission's goal.
--
--   **Formalization Note** $H$ reuses the published `WeightedGraph` (a simple graph with symmetric $[0,\infty]$ edge weights) and its `weight`, which supplies the conventions $w_H(a,a)=0$ and $w_H=\infty$ off stored edges. With $x_0=u$, $x_j=v$, the cost is written as $\sum_{i=0}^{j-1}\bigl(w_H(x_i,p'_{x_i})+w_H(p'_{x_i},p_{x_{i+1}})+w_H(p_{x_{i+1}},x_{i+1})\bigr)$, which equals (5.5) because $w_H$ is symmetric; the vertices and pivots are indexed by $\mathrm{Fin}(j+1)$, and the unused entries $p_{x_0}$, $p'_{x_j}$ range over the (nonempty) pivot sets. The minimum is an infimum in $[0,\infty]$ over this finite family. Stored edges may carry weight $\infty$; they are counted in the space.
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Definition 3 and equation (5.5), p.20 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_WeightedGraph

set_option autoImplicit false
open scoped Classical ENNReal
noncomputable section

namespace PivotADO.OneHop.Supplement

open PivotADO.OneHop

/-! Definition 3 (r-pivot β-hop k-stretch ADO), Kadria–Roditty, STOC 2027 submission
#584 (October 2026), p.20 (PDF 21), equation (5.5). -/

/-- The weight (5.5) of the walk
`u = x₀ → p'_{x₀} → p_{x₁} → x₁ → p'_{x₁} → ⋯ → p_{x_j} → x_j = v`
with `j` stored hops `p'_{x_i} → p_{x_{i+1}}`. Here `pout i = p'_{x_i}` and
`pin i = p_{x_i}`; the values `pin 0` and `pout (Fin.last j)` are not used.
Every summand uses the stored weight `w_H` (zero on the diagonal, `⊤` off stored edges).
Since `w_H` is symmetric, this is exactly the sum (5.5). -/
def hopWalkCost {V : Type*} (H : WeightedGraph V) {j : ℕ}
    (x pin pout : Fin (j + 1) → V) : ℝ≥0∞ :=
  ∑ i : Fin j, (H.weight (x i.castSucc) (pout i.castSucc) +
    H.weight (pout i.castSucc) (pin i.succ) + H.weight (pin i.succ) (x i.succ))

/-- `d^{≤β}_{H,P}(u, v)`: the minimum of (5.5) over `1 ≤ j ≤ β`, intermediate vertices
`x₁, …, x_{j−1}` and pivots `p_{x_i}, p'_{x_i} ∈ P(x_i)` (which may differ), with
`x₀ = u`, `x_j = v`. -/
def hopEstimate {V : Type*} (H : WeightedGraph V) (pivots : V → Finset V) (β : ℕ)
    (u v : V) : ℝ≥0∞ :=
  ⨅ (j : ℕ) (_ : 1 ≤ j ∧ j ≤ β) (x : Fin (j + 1) → V)
    (_ : x 0 = u ∧ x (Fin.last j) = v) (pin : Fin (j + 1) → V) (pout : Fin (j + 1) → V)
    (_ : ∀ i, pin i ∈ pivots (x i) ∧ pout i ∈ pivots (x i)),
    hopWalkCost H x pin pout

/-- An r-pivot β-hop k-stretch ADO for `G` (Definition 3). The space of the oracle is
`edgeCount storage.graph`, counting every stored edge (including any of weight `⊤`). -/
structure HopOracle {V : Type*} (G : SimpleGraph V) (r β : ℕ) (k : ℝ) where
  storage : WeightedGraph V
  pivots : V → Finset V
  self_mem : ∀ v, v ∈ pivots v
  card_le : ∀ v, (pivots v).card ≤ r
  dominates : ∀ u v, storage.graph.Adj u v → distance G u v ≤ storage.weight u v
  bounds : ∀ u v, distance G u v ≤ hopEstimate storage pivots β u v ∧
    hopEstimate storage pivots β u v ≤ ENNReal.ofReal k * distance G u v

end PivotADO.OneHop.Supplement


