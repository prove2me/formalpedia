-- Prove2me | Definitions.Def_ARTreeCover_Supplement_HighwayDimLE
-- name    : ARTreeCover_Supplement_HighwayDimLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:02:28.200945+00:00
-- url     : https://prove2.me/theorems/4d14aaa3-d0ee-4306-92ba-1fc7e29f9167
-- title:
--   $(1+\epsilon)$-highway dimension at most $h$ (functional highway dimension)
-- statement:
--   Fix $\epsilon>0$ and $h\in\mathbb N$. A weighted graph $G$ has **$(1+\epsilon)$-highway dimension at most $h$** if for every $r>0$ and every vertex $v$, writing $B_v=B_G(v,(4+8\epsilon)r)$, there is a hitting set $H\subseteq B_v$ with $|H|\le h$ such that for all $x,y\in B_v$ with $d_G(x,y)>r$ there is a path $P$ from $x$ to $y$ with all vertices in $B_v$, of length
--   $$w(P)\le(1+\epsilon)\,d_G(x,y),$$
--   that meets $H$.
--
--   This is the functional highway dimension of Feldmann and Filtser (Definition 9), evaluated at one value of $\epsilon$. Road networks are modelled as graphs of small highway dimension; Theorems 23, 28 and 42 assume this bound.
--
--   **Formalization Note** Definition 9 asks the condition for every $\epsilon$ with a function $h(\epsilon)$. The theorems assume "(1+ϵ)-highway dimension at most h(ϵ)" for their own $\epsilon$ and use only $h(\epsilon)$, so the predicate is the condition at that single $\epsilon$ with $h=h(\epsilon)$. Balls are closed; a path has no repeated vertex.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 9, p.11 (PDF p.14)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- `HighwayDimLE G ε h`: `G` has `(1 + ε)`-highway dimension at most `h`: for every `r > 0` and
every vertex `v`, with `B_v = B_G(v, (4 + 8ε)r)`, there is a hitting set `H ⊆ B_v` with `|H| ≤ h`
such that every two `x, y ∈ B_v` with `d_G(x, y) > r` are joined by a path inside `B_v` of weight at
most `(1 + ε) d_G(x, y)` that meets `H`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 9 (Functional Highway Dimension
[34]), p.11 (PDF p.14): "An undirected weighted graph G = (V, E) has highway dimension
h : R+ → N ∪ {∞} if for every ε > 0, r > 0, and v ∈ V, there is a hitting set
H ⊆ Bv = BG(v, (4 + 8ϵ)r) of size |H| ≤ h(ϵ), such that for every x, y ∈ Bv with dG(x, y) > r,
there is a path P between x and y in Bv of length w(P) ≤ (1 + ϵ)dG(x, y) such that P ∩ H ≠ ∅."

**Formalization Note.** The theorems' hypothesis "(1 + ϵ)-highway dimension at most h(ϵ)" is read
as Definition 9's condition at the theorem's own `ϵ` only, with `h = h(ϵ) ∈ ℕ` (Definition 9 writes
`ε` and `ϵ` for one variable). Balls are closed, `B_G(v, R) = {x | d_G(v, x) ≤ R}`. A path is a
walk of `G` without repeated vertices; "in `B_v`" means all its vertices are in `B_v`; its length is
the base `walkWeight`. -/
def HighwayDimLE {V : Type} (G : WGraph V) (ε : ℝ) (h : ℕ) : Prop :=
  ∀ (r : ℝ), 0 < r → ∀ v : V,
    ∃ Hs : Finset V, Hs.card ≤ h ∧
      (∀ z ∈ Hs, G.dist v z ≤ ENNReal.ofReal ((4 + 8 * ε) * r)) ∧
      ∀ x y, G.dist v x ≤ ENNReal.ofReal ((4 + 8 * ε) * r) →
        G.dist v y ≤ ENNReal.ofReal ((4 + 8 * ε) * r) → ENNReal.ofReal r < G.dist x y →
        ∃ p : G.graph.Walk x y, p.IsPath ∧
          (∀ z ∈ p.support, G.dist v z ≤ ENNReal.ofReal ((4 + 8 * ε) * r)) ∧
          G.walkWeight p ≤ ENNReal.ofReal (1 + ε) * G.dist x y ∧ ∃ z ∈ p.support, z ∈ Hs

end ARTreeCover.Supplement


