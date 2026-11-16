-- Prove2me | Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyEmbedding
-- name    : ARTreeCover_Supplement_IsAlmostRamseyEmbedding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:03:22.653562+00:00
-- url     : https://prove2.me/theorems/a341179a-8c50-47a5-a6f7-ffc77f324e44
-- title:
--   Almost-Ramsey embedding for scale $\Delta$ into a metric space
-- statement:
--   Let $G$ be a weighted graph and $(Y,d_Y)$ a metric space. A map $f:V\to Y$ is an **almost-Ramsey embedding for scale $\Delta>0$ that satisfies $s$ vertices with distortion $\alpha$** (Definition 23) if there is $S\subseteq V$ with $|S|\ge s$ such that
--   $$d_G(u,v)\le d_Y(f(u),f(v))\le\alpha\Delta\qquad\text{for every }u\in S\text{ and }v\in V\text{ with }d_G(u,v)\le\Delta.$$
--
--   Theorems 38–42 give such embeddings into $\ell_q^{D}$ with $D=O(\log n)$ and constant or $O(k)$ distortion for many vertices.
--
--   **Formalization Note** The distance $d_G\in[0,\infty]$ is compared with the real distance $d_Y$ through the inclusion $\mathbb R_{\ge0}\to[0,\infty]$. In the theorems $Y=\ell_q^D$ is the space $\mathbb R^D$ with the $\ell_q$ norm, $q\in[1,\infty]$.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 23, p.49 (PDF p.52)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- `IsAlmostRamseyEmbedding G f Δ s α`: the map `f : V → Y` into a metric space is an
almost-Ramsey embedding for scale `∆` that satisfies `s` vertices with distortion `α`: there is
`S ⊆ V` with `|S| ≥ s` such that `d_G(u, v) ≤ d_Y(f(u), f(v)) ≤ α∆` for every `u ∈ S` and every
`v ∈ V` with `d_G(u, v) ≤ ∆`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 23, p.49 (PDF p.52): "Given an
undirected weighted graph G = (V, E) and a metric space (Y, dY), an embedding f : V → Y is called an
almost-Ramsey embedding for scale ∆ > 0, that satisfies s vertices with distortion α, if there
exists a subset S ⊆ V of size |S| ≥ s, such that for every u ∈ S and v ∈ V with dG(u, v) ≤ ∆,
dG(u, v) ≤ dY(f(u), f(v)) ≤ α∆."

**Formalization Note.** `d_G ∈ [0, ∞]` is compared with the real distance `d_Y` through
`ENNReal.ofReal`. `s` is a real number. For the theorems, `Y` is `ℓ_q^D`, i.e.
`PiLp q (fun _ : Fin D => ℝ)`; "stretch" in Theorems 39–42 is this distortion `α`. -/
def IsAlmostRamseyEmbedding {V Y : Type} [MetricSpace Y] (G : WGraph V) (f : V → Y)
    (Δ s α : ℝ) : Prop :=
  ∃ S : Finset V, s ≤ (S.card : ℝ) ∧
    ∀ u ∈ S, ∀ v, G.dist u v ≤ ENNReal.ofReal Δ →
      G.dist u v ≤ ENNReal.ofReal (dist (f u) (f v)) ∧ dist (f u) (f v) ≤ α * Δ

end ARTreeCover.Supplement


