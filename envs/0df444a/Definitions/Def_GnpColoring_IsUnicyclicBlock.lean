-- Prove2me | Definitions.Def_GnpColoring_IsUnicyclicBlock
-- name    : GnpColoring_IsUnicyclicBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:23.235363+00:00
-- url     : https://prove2.me/theorems/7ce6acb7-3dd6-44f1-aebc-18072434406b
-- title:
--   $G[B]$ is unicyclic
-- statement:
--   $G[B]$ is **unicyclic** if it is connected and has exactly one cycle; for a finite connected graph this means it has exactly $|B|$ edges.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 2.1, p.13; Definition 3.2, p.15

import Mathlib
import Definitions.Def_GnpColoring_inducedEdgeCount

open scoped Classical
open Finset

namespace GnpColoring

/-- **`G[B]` is unicyclic**: `G[B]` is connected and has exactly one cycle, i.e. `|B|` edges.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 2.1, p.13: "A connected graph is unicyclic if it has exactly one cycle";
Definition 3.2, p.15 ("a tree with at most one extra edge … otherwise we call it unicyclic").

**Formalization Note** A finite connected graph has exactly one cycle iff its number of edges
equals its number of vertices. -/
def IsUnicyclicBlock {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) : Prop :=
  (G.induce (B : Set (Fin n))).Connected ∧ inducedEdgeCount G B = B.card

end GnpColoring


