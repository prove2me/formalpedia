-- Prove2me | Definitions.Def_HopRamsey_augmentComplete
-- name    : HopRamsey_augmentComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:00.076209+00:00
-- url     : https://prove2.me/theorems/cb69e552-b354-4b9a-8bb2-2d96530c5621
-- title:
--   The auxiliary graph $G'$ of §4.4
-- statement:
--   Given a weighted graph $G=(V,E,w)$ and $\omega>0$, the graph $G'$ is obtained from $G$ by adding an edge of weight $\omega$ between every pair of distinct non-adjacent vertices; edges of $G$ keep their weights. In §4.4, $\omega=2\rho\Phi'$ where $\rho$ is the distortion of the finite-diameter case and $\Phi'$ the largest finite $h$-hop distance of $G$; $G'$ has finite $h$-hop diameter, so the finite case applies to it.
--
--   **Formalization Note** $G'$ is the complete graph on $V$; $\omega$ is a parameter that must be positive to be an edge weight.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), §4.4, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

namespace HopRamsey

open ARTreeCover

/-- The auxiliary graph `G′` of §4.4: `G` plus an edge of weight `ω` between every pair of
distinct non-adjacent vertices.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), §4.4, p.25
(PDF p.27): "We create an auxiliary graph G′ by taking G and adding an edge of weight ω = 2ρ·Φ′
between every pair of non-adjacent vertices."

**Formalization Note.** `G′` is the complete graph on `V`; an edge keeps its weight in `G` when it
is an edge of `G` and has weight `ω` otherwise. The weight `ω` is a parameter with `ω > 0` (a
weight must be positive). -/
noncomputable def augmentComplete {V : Type} (G : WGraph V) (ω : ℝ) (hω : 0 < ω) : WGraph V :=
  open Classical in
  { graph := ⊤
    w := fun e => if e ∈ G.graph.edgeSet then G.w e else ω
    w_pos := by
      intro e _
      by_cases he : e ∈ G.graph.edgeSet
      · simp only [he, if_true]; exact G.w_pos e he
      · simp only [he, if_false]; exact hω }

end HopRamsey


