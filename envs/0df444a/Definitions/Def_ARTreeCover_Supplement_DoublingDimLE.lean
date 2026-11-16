-- Prove2me | Definitions.Def_ARTreeCover_Supplement_DoublingDimLE
-- name    : ARTreeCover_Supplement_DoublingDimLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:02:07.927212+00:00
-- url     : https://prove2.me/theorems/7eafcf43-9d71-41be-8641-97b002ed4693
-- title:
--   Doubling dimension at most $d$ of the shortest-path metric
-- statement:
--   For a weighted graph $G$ with shortest-path distance $d_G$, the **doubling constant** $\lambda$ is the least integer such that every ball $B(x,r)=\{y\mid d_G(x,y)\le r\}$, $r>0$, is covered by at most $\lambda$ balls of radius $r/2$; the **doubling dimension** is $\log_2\lambda$ (Definition 7).
--
--   The graph has **doubling dimension at most $d$** if $\log_2\lambda\le d$, i.e. every such ball is covered by at most $2^d$ balls of radius $r/2$ centred at vertices of $G$.
--
--   Doubling metrics are a standard class of low-dimensional metrics; Theorems 12, 23, 28 and 42 assume this bound.
--
--   **Formalization Note** The real number $d$ is arbitrary and $2^d$ is the real power. Balls are closed. The distance is the mission's $d_G\in[0,\infty]$, which is $\infty$ between different components, so every ball lies inside one component.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 7, p.11 (PDF p.14)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- `DoublingDimLE G d`: the (extended) metric `(V, d_G)` induced by `G` has doubling dimension at
most `d`: every closed ball `B(x, r) = {y | d_G(x, y) ≤ r}` (`r > 0`) is covered by at most `2^d`
closed balls of radius `r/2` centred at vertices.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 7, p.11 (PDF p.14): "The doubling
constant λ is the smallest integer such that for every r > 0, any ball of radius r in X can be
covered by at most λ balls of radius r/2. The doubling dimension of X is defined as log2 λ. For an
undirected weighted graph G, the doubling dimension is defined as the doubling dimension of the
metric space (V, dG)."

**Formalization Note.** "Doubling dimension at most `d`" is `log₂ λ ≤ d`, i.e. `λ ≤ 2^d`, i.e. every
ball has a cover by at most `2^d` half-radius balls (`2^d` is `Real.rpow`, `d` real). Balls are
closed; centres range over `V`. Distances are the base `d_G ∈ [0, ∞]` (`∞` across components, so a
ball lies inside one component). -/
def DoublingDimLE {V : Type} (G : WGraph V) (d : ℝ) : Prop :=
  ∀ (x : V) (r : ℝ), 0 < r →
    ∃ Cs : Finset V, (Cs.card : ℝ) ≤ (2 : ℝ) ^ d ∧
      ∀ y, G.dist x y ≤ ENNReal.ofReal r → ∃ c ∈ Cs, G.dist c y ≤ ENNReal.ofReal (r / 2)

end ARTreeCover.Supplement


