-- Prove2me | Definitions.Def_VDCyclePack_mdeg
-- name    : VDCyclePack_mdeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:31.226171+00:00
-- url     : https://prove2.me/theorems/c3e88888-2d66-46df-934a-a7b07c807daf
-- title:
--   Degree in an auxiliary multigraph (a loop counts two)
-- statement:
--   An auxiliary multigraph has a finite set of edges, each with an unordered pair of ends; a loop has equal ends and parallel edges have the same ends. The **degree** of a vertex $v$ counts every non-loop edge at $v$ once and every loop at $v$ twice.
--
--   **Formalization Note** A vertex type $W$, a finite edge type $E$ and an end map $E\to\mathrm{Sym}^2(W)$.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.10

import Mathlib

namespace VDCyclePack

open Classical in
/-- **Degree in an auxiliary multigraph (a loop counts two).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.10: "Auxiliary multigraphs may have loops and parallel edges. A loop
forms a cycle of length one and contributes two to the degree of its vertex".

A multigraph has a finite edge type `E` and an end map `ends : E → Sym2 W` (a loop is a diagonal
pair, parallel edges have equal ends). `mdeg ends v` counts each non-loop edge at `v` once and each
loop at `v` twice. -/
noncomputable def mdeg {W E : Type*} [Fintype E] (ends : E → Sym2 W) (v : W) : ℕ :=
  ∑ e : E, if ends e = s(v, v) then 2 else if v ∈ ends e then 1 else 0

end VDCyclePack


