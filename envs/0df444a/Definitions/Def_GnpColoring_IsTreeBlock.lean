-- Prove2me | Definitions.Def_GnpColoring_IsTreeBlock
-- name    : GnpColoring_IsTreeBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:26.774202+00:00
-- url     : https://prove2.me/theorems/6482f21c-2482-4eee-a5e7-56b436ce56d8
-- title:
--   $G[B]$ is a tree
-- statement:
--   $G[B]$ is a **tree** if it is connected (in particular $B\neq\emptyset$) and has $|B|-1$ edges.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.2, p.15

import Mathlib
import Definitions.Def_GnpColoring_inducedEdgeCount

open scoped Classical
open Finset

namespace GnpColoring

/-- **`G[B]` is a tree**: `G[B]` is connected (in particular `B` is nonempty) and has `|B| − 1`
edges.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.2, p.15: "If B is a tree, we call it a tree block".

**Formalization Note** A finite connected graph is a tree iff it has one edge fewer than
vertices. -/
def IsTreeBlock {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) : Prop :=
  (G.induce (B : Set (Fin n))).Connected ∧ inducedEdgeCount G B + 1 = B.card

end GnpColoring


