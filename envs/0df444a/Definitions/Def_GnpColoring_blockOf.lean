-- Prove2me | Definitions.Def_GnpColoring_blockOf
-- name    : GnpColoring_blockOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:28.112194+00:00
-- url     : https://prove2.me/theorems/a40abd87-be3f-4084-8db5-3f8d7f57a6b7
-- title:
--   The block containing a vertex
-- statement:
--   Fix a vertex set $S$. For $v\notin S$, the **block of $v$** is the vertex set of the connected component containing $v$ in the graph obtained from $G$ by deleting the vertices of $S$: the vertices $u$ reachable from $v$ by a walk avoiding $S$. For $v\in S$ it is the empty set.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.2, p.15

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The block of a vertex**: for `v ∉ S`, the vertex set of the connected component of `v` in the
graph obtained from `G` by removing all vertices of `S`; for `v ∈ S`, the empty set.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.2, p.15: "Choose a subset S ⊆ Ŝ and let 𝓑 the set of connected components of
G after removing all vertices in S."

**Formalization Note** `u` lies in the block of `v ∉ S` iff some walk of `G` from `v` to `u`
avoids `S`. -/
noncomputable def blockOf {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  univ.filter fun u => v ∉ S ∧ ∃ p : G.Walk v u, ∀ w ∈ p.support, w ∉ S

end GnpColoring


