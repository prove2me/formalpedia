-- Prove2me | Definitions.Def_ImplicitParityWL_ColoredGraph
-- name    : ImplicitParityWL_ColoredGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:02.504416+00:00
-- url     : https://prove2.me/theorems/5fdcfbda-8979-40b7-a7b3-7ba568353b5f
-- title:
--   Colored graph
-- statement:
--   A **colored graph** is a triple $G=(V(G),E(G),\chi_G)$ of a finite vertex set, an edge set of unordered pairs of distinct vertices, and a vertex coloring $\chi_G:V(G)\to K$ into a set $K$ of colors. All graphs are simple and undirected, and each vertex has exactly one color. Two graphs that are compared use the same set of colors.
--
--   Colored graphs are the objects on which the Weisfeiler–Leman algorithm and the bijective pebble game run in this mission.
--
--   **Formalization Note** The vertex type $V$ and the color type $K$ are parameters of the structure, and finiteness of $V$ is a `Fintype` binder where it is used.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §3, p.14

import Mathlib

namespace ImplicitParityWL

/-- A **colored graph** `G = (V(G), E(G), χ_G)` with vertices in `V` and colors in `K`: a simple
undirected graph on `V` together with a vertex coloring `χ : V → K` (Curticapean, Liu, Neuen,
Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, STOC 2027
submission, manuscript of November 3, 2026, §3, p.14).

**Formalization Note** Finiteness of the vertex set is a `[Fintype V]` binder wherever it is used.
Two graphs that are compared share the color type `K` and may have different vertex types. -/
structure ColoredGraph (K : Type*) (V : Type*) where
  /-- The underlying simple undirected graph. -/
  graph : SimpleGraph V
  /-- The vertex coloring. -/
  χ : V → K

end ImplicitParityWL


