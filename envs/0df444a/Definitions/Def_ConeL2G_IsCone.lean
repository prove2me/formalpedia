-- Prove2me | Definitions.Def_ConeL2G_IsCone
-- name    : ConeL2G_IsCone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:48.958373+00:00
-- url     : https://prove2.me/theorems/86c719a0-1338-4f66-828f-c20df19a92a8
-- title:
--   A cone centered at $v$
-- statement:
--   A graph $H$ is a **cone centered at $v$** if $v$ is adjacent to every other vertex of $H$. One writes $H=\{v\}\cup H'$ and calls the vertices of $H'$ the leaves; edges among the leaves are allowed.
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 1.1, p.4

import Mathlib

namespace ConeL2G

/-- **A cone centered at `v`.** Li–Oveis Gharan, arXiv:2610.37721, Section 1.1, p.4: "We say a
graph `H` (as a subgraph of `G`) is a cone centered at `v` if `v` is connected to all other vertices
of `H`. In such a case we write `H = {v} ∪ H′` and we call vertices of `H′` leaves."

Edges among the leaves are allowed (Theorem 1.6, p.4). The leaves are the vertices `u ≠ v`. -/
def IsCone {V : Type*} (H : SimpleGraph V) (v : V) : Prop :=
  ∀ u : V, u ≠ v → H.Adj v u

end ConeL2G


