-- Prove2me | Definitions.Def_LCPlanarSteiner_pcost
-- name    : LCPlanarSteiner_pcost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:30.871669+00:00
-- url     : https://prove2.me/theorems/1b9f8258-067d-49be-86c6-7a66b5ba6016
-- title:
--   Cost of a set of arcs, shared arcs paid once
-- statement:
--   For a finite set $F$ of arc indices,
--   $$
--   c(F) = \sum_{e \in F} c_e .
--   $$
--   An arc used by several paths of a purchased union is paid once.
--
--   This is the objective of directed Steiner forest: the cost of the union of the bought arcs.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §1, p.2

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net

namespace LCPlanarSteiner

/-- **Cost `c(F)` of a set of arcs; shared arcs are paid once.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §1, p.2: "Buying F ⊆ E costs
c(F) = Σ_{e∈F} c_e; shared edges are paid once."

`pcost G F = Σ_{e ∈ F} c_e` for a finite set `F` of arc indices.

**Formalization Note.** An index outside the arc list contributes `0`. -/
def pcost (G : Net) (F : Finset ℕ) : ℚ := ∑ e ∈ F, G.cst e

end LCPlanarSteiner


