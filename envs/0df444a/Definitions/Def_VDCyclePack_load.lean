-- Prove2me | Definitions.Def_VDCyclePack_load
-- name    : VDCyclePack_load
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:23.616094+00:00
-- url     : https://prove2.me/theorems/6a39a3b0-f5cb-4aac-b528-c71592134bbd
-- title:
--   Load $\sum_{C\ni v}x_C$ of a weighting of the cycles at a vertex
-- statement:
--   Let $x$ assign a real weight $x_C$ to every cycle $C$ of a finite graph $G$. The **load** at a vertex $v$ is
--   $$
--   \sum_{C\in\mathcal C(G),\ v\in V(C)} x_C .
--   $$
--
--   The vertex constraints of the natural LP (1) say that every load is at most one.
--
--   **Formalization Note** The weights are a function on all subgraphs of $G$; only its values on cycles are read.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.9

import Mathlib
import Definitions.Def_VDCyclePack_cycles

namespace VDCyclePack

open Classical in
/-- **Load of a weighting of the cycles at a vertex.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.9: "The load at a vertex v is Σ_{C∋v} x_C".

For weights `x` on the cycles of `G`, `load G x v = Σ_{C ∈ 𝒞(G), v ∈ V(C)} x C`.

**Formalization Note.** Weights are a function on all subgraphs; only its values on cycles are
read. -/
noncomputable def load {V : Type*} [Fintype V] (G : SimpleGraph V) (x : G.Subgraph → ℝ) (v : V) :
    ℝ :=
  ∑ C ∈ (cycles G).filter (fun C => v ∈ C.verts), x C

end VDCyclePack


