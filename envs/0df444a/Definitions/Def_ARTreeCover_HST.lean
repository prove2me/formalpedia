-- Prove2me | Definitions.Def_ARTreeCover_HST
-- name    : ARTreeCover_HST
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:51:59.749544+00:00
-- url     : https://prove2.me/theorems/12efbff1-ea31-47c5-8bd0-e5e89fa3d7f7
-- title:
--   Hierarchically separated trees, as leaf ultrametrics with values in $[0,\infty]$
-- statement:
--   A **hierarchically separated tree** $T$ is recorded by its leaf set $L(T)\subseteq V$ and the function $\rho_T(x,y)=\ell(\mathrm{LCA}_T(x,y))$ on leaves, which satisfies
--
--   $$\rho_T(x,x)=0,\qquad \rho_T(x,y)=\rho_T(y,x),\qquad \rho_T(x,z)\le\max\{\rho_T(x,y),\rho_T(y,z)\}.$$
--
--   Values lie in $[0,\infty]$, and $\rho_T(u,v)=\infty$ when $u$ or $v$ is not a leaf of $T$.
--
--   By the paragraph after Definition 3 of the paper and by Fact 6, the leaf ultrametrics of HSTs are exactly the finite ultrametrics, and no statement of the paper uses the internal vertices, so this pair carries everything. $\rho_T(x,y)=0$ for distinct leaves is allowed (an internal vertex with label 0).
--
--   **Formalization Note** The value $\infty$ is needed: the proof of Lemma 13 labels a root "diam(G) or ∞" (p.32), and a cover of an edgeless graph needs it.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 3, Fact 6, p.10 (PDF p.13); Definition 15, p.29 (PDF p.32)

import Mathlib

open scoped ENNReal

namespace ARTreeCover

/-- A hierarchically separated tree, recorded by its set of leaves `L(T) ⊆ V` and the function
`ρ_T(u, v) = ℓ(LCA_T(u, v))`, an ultrametric on the leaves with values in `[0, ∞]`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 3, Fact 6 and the paragraph after
it, p.10 (PDF p.13): "Given an HST, let L be its set of leaves, and define the function
d(x, y) = ℓ(LCA(x, y)). It is not hard to see that (L, d) is an ultrametric space."; "Every finite
ultrametric (X, ρ) can be represented by an HST"; "we denote ρ_T(u, v) = ℓ(LCA_T(u, v)), for every
u, v ∈ L(T)". Definition 15, p.29: "each T ∈ H with a set L(T) ⊆ V of leaves".

**Formalization Note.**
1. By the quoted sentence and Fact 6, the leaf ultrametrics of HSTs are exactly the finite
   ultrametrics, so an HST is encoded by `(L(T), ρ_T)`; its internal vertices play no role in any
   statement of the paper. `ρ x y = 0` for distinct leaves is allowed (an internal vertex with
   label 0).
2. Labels, hence `ρ`, take values in `[0, ∞]`: the proof of Lemma 13 labels a root "diam(G) or ∞"
   (p.32), and covers of disconnected graphs need it.
3. `ρ u v = ∞` when `u` or `v` is not a leaf, so that "`d_G ≤ min_T ρ_T`" can be stated for all
   pairs of `V`. -/
structure HST (V : Type) where
  /-- The leaf set `L(T) ⊆ V`. -/
  leaves : Set V
  /-- `ρ_T(u, v)`, the label of the lowest common ancestor. -/
  ρ : V → V → ℝ≥0∞
  /-- `ρ_T(x, x) = 0` on leaves (leaves are labelled 0). -/
  self : ∀ x ∈ leaves, ρ x x = 0
  /-- Symmetry. -/
  symm : ∀ x y, ρ x y = ρ y x
  /-- The ultrametric inequality on leaves. -/
  ultra : ∀ x ∈ leaves, ∀ y ∈ leaves, ∀ z ∈ leaves, ρ x z ≤ max (ρ x y) (ρ y z)
  /-- `ρ_T` is `∞` off the leaves. -/
  off : ∀ u v, (u ∉ leaves ∨ v ∉ leaves) → ρ u v = ⊤

end ARTreeCover


