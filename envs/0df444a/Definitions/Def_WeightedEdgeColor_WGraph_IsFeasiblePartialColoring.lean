-- Prove2me | Definitions.Def_WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
-- name    : WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:03.754445+00:00
-- url     : https://prove2.me/theorems/ef767a7b-1e78-4f34-a032-8648a6c4c38d
-- title:
--   Feasible partial weighted coloring and the colored incident weight at a vertex
-- statement:
--   Let $G=(V,E)$ be an edge-weighted graph and $\mathcal C$ a palette. A **partial coloring** assigns to each edge either a color $c\in\mathcal C$ or nothing. It is **feasible** if every color has incident weight at most one at every vertex:
--   $$
--   \sum_{e\ni v,\ e\text{ colored } c} w_e\le 1\qquad(v\in V,\ c\in\mathcal C).
--   $$
--   The **colored incident weight** at $v$ is the total weight of the edges at $v$ that receive a color.
--
--   These are the objects in the conclusion of the local-to-global rounding theorem (Theorem 3.1).
--
--   **Formalization Note** A partial coloring is a map $E\to$ `Option` $\mathcal C$, with `none` meaning uncolored.
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorem 3.1, p.6; Appendix A, p.24

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph

set_option autoImplicit false

namespace WeightedEdgeColor

namespace WGraph

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- A feasible partial coloring with palette `C`: an edge `e` is colored `c` when
`φ e = some c` and uncolored when `φ e = none`; at every vertex each color has incident
colored weight at most one.

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Theorem 3.1, p.6; Appendix A, p.24 ("A feasible color has incident weight at most one at every
vertex").

**Formalization Note.** Partial colorings are maps `E → Option C`. -/
def IsFeasiblePartialColoring (G : WGraph V E) {C : Type} [DecidableEq C]
    (φ : E → Option C) : Prop :=
  ∀ (v : V) (c : C), ∑ e ∈ (G.inc v).filter (fun e => φ e = some c), G.w e ≤ 1

/-- The colored incident weight at `v`: the total weight of the edges at `v` that receive a
color under the partial coloring `φ`. -/
noncomputable def coloredWeight (G : WGraph V E) {C : Type} (φ : E → Option C) (v : V) : ℝ :=
  ∑ e ∈ (G.inc v).filter (fun e => (φ e).isSome), G.w e

end WGraph

end WeightedEdgeColor


