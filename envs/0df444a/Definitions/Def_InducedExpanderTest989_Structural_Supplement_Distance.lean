-- Prove2me | Definitions.Def_InducedExpanderTest989_Structural_Supplement_Distance
-- name    : InducedExpanderTest989_Structural_Supplement_Distance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:29:28.244188+00:00
-- url     : https://prove2.me/theorems/4eaa4838-5c6c-43af-8231-84f2c234360f
-- title:
--   Normalized edit distance, ε-farness and the size factor of distance testing
-- statement:
--   Let $G$ and $H$ be simple graphs on the same vertex set $[n]$, both of maximum degree at most a fixed bound $d$. Their **edit distance** is the number $|E(G)\triangle E(H)|$ of unordered vertex pairs that are an edge of exactly one of them, and their normalized distance is
--   $$\mathrm{dist}_d(G,H)=\frac{|E(G)\triangle E(H)|}{dn}.$$
--   For a graph property $\mathcal P$, $\mathrm{dist}_d(G,\mathcal P)$ is the minimum of $\mathrm{dist}_d(G,H)$ over the graphs $H\in\mathcal P$ of maximum degree at most $d$, and $G$ is **$\varepsilon$-far** from $\mathcal P$ when $\mathrm{dist}_d(G,\mathcal P)>\varepsilon$, that is, when every such $H$ satisfies $|E(G)\triangle E(H)|>\varepsilon dn$.
--
--   Distance testing at the original core size runs the structural tester with the size-relaxation factor
--   $$\kappa(\alpha,\varepsilon)=1-\min\Big\{\frac14,\frac{\varepsilon}{8\alpha}\Big\}.$$
--
--   These objects state the distance-testing promise of Theorem 5.1 and the repair bounds of Lemma 5.1 and Corollary 5.1.
--
--   **Formalization Note** The edit distance is the cardinality of the symmetric difference of the two edge sets (`editDistance`). The predicate `FarFrom d ε G P` writes the minimum out as a statement about every target graph; when no target graph of maximum degree at most $d$ exists, the minimum over the empty set is $+\infty$ and every graph is far. `distKappa α ε` is the factor $\kappa(\alpha,\varepsilon)$.
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.3 (PDF p.5), §1.1 "Distance testing"; p.32 (PDF p.34), Theorem 5.1 (choice of κ)

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Graph

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal symmDiff
noncomputable section

namespace InducedExpanderTest989.Structural.Supplement

/-- `|E(G) △ E(H)|`: the number of unordered pairs that are an edge of exactly one of the two
graphs on the same vertex set `[n]` (§1.1, p. 3). -/
def editDistance {n : ℕ} (G H : SimpleGraph (Fin n)) : ℕ :=
  (symmDiff G.edgeSet H.edgeSet).ncard

/-- `G` is `ε`-far from the property `P` (§1.1, p. 3): `dist_d(G, P) > ε`, where
`dist_d(G, H) = |E(G) △ E(H)| / (d n)` and the minimum ranges over graphs `H ∈ P` of maximum
degree at most `d`. The minimum is written out: every such `H` is at normalized distance `> ε`.
With no such `H` the minimum over `∅` is `+∞` and every graph is far. -/
def FarFrom {n : ℕ} (d : ℕ) (ε : ℝ) (G : SimpleGraph (Fin n))
    (P : SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ H : SimpleGraph (Fin n), DegreeBound d H → P H → ε * d * n < (editDistance G H : ℝ)

/-- The size-relaxation factor of Theorem 5.1: `κ = 1 − min{1/4, ε/(8α)}`. -/
def distKappa (α ε : ℝ) : ℝ := 1 - min (1/4) (ε / (8 * α))

end InducedExpanderTest989.Structural.Supplement


