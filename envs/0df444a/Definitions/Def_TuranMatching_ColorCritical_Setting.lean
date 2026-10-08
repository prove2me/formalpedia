-- Prove2me | Definitions.Def_TuranMatching_ColorCritical_Setting
-- name    : TuranMatching_ColorCritical_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:53.80622+00:00
-- url     : https://prove2.me/theorems/4a652eb0-d3ea-407a-956f-66e2e25ce9f2
-- title:
--   p. 5 — color-critical graphs and the high-degree set X
-- statement:
--   This file adds two objects of N. Alon and P. Frankl, *Turán graphs with bounded matching number* (arXiv:2210.15076v1) used in Proposition 3.1, on top of the shared setting of this series (`TuranMatching.Clique.Setting`). That file defines the matching number $\nu(G)$, the Turán number $t(n,k)$, the graph $G(n,k,s)$ of p. 1 (`bigGraph n k s`) and its edge count $g(n,k,s)$ (`gNum n k s`). All graphs are finite and simple.
--
--   1. **Color-critical graphs** (p. 5). A graph $H$ is color-critical if it contains an edge $e$ whose deletion decreases its chromatic number:
--   $$\chi(H-e)<\chi(H).$$
--   2. **The high-degree set** (proof of Proposition 3.1, p. 5). For a graph $G$ on $n$ vertices and $s\ge 0$, $X=X(G,s)$ is the set of vertices of degree exceeding $2s$.
--
--   Together with the shared objects, these are the objects in terms of which Proposition 3.1 and every step of its proof are stated.
--
--   **Formalization Note** Vertices of $G$ are `Fin n`. Chromatic numbers are compared in $\mathbb N\cup\{\infty\}$ (Mathlib's `chromaticNumber`), so an infinite chromatic number is never sent to a junk finite value. Deleting the edge $e$ is Mathlib's `deleteEdges {e}`, and $e$ is required to be an edge of $H$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 5, §3 (color-critical); p. 5, proof of Proposition 3.1 (the set X)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

namespace TuranMatching.ColorCritical

open Finset SimpleGraph

/-- §3, p. 5: `H` is color-critical if it contains an edge whose deletion decreases its
chromatic number (compared in `ℕ∞`). -/
def IsColorCritical {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ e ∈ H.edgeSet, (H.deleteEdges {e}).chromaticNumber < H.chromaticNumber

/-- The set `X` of the proof of Proposition 3.1 (p. 5): the vertices of degree exceeding `2s`. -/
def highDeg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ℕ) : Finset (Fin n) :=
  {v | 2 * s < G.degree v}

end TuranMatching.ColorCritical


