-- Prove2me | Definitions.Def_GnpColoring_portOf
-- name    : GnpColoring_portOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:48.646227+00:00
-- url     : https://prove2.me/theorems/e8f360f2-900b-4a22-8e11-b006f3cc37bb
-- title:
--   The port $\rho_{B,s}$ of a boundary vertex
-- statement:
--   For a block $B$ and $s\in\partial B$, $\rho_{B,s}$ is the neighbour of $s$ in $B$; in a valid partition it is unique.
--
--   **Formalization Note** It is chosen by the axiom of choice; when $s$ has no neighbour in $B$ the value is $s$ itself, a case never used.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.2 (2), p.15

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The port `ρ_{B,s}` of a boundary vertex**: the neighbour of `s ∈ ∂B` in `B`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.2 (2), p.15 ("every vertex in the boundary ∂B … has exactly one neighbor in
B"), used in Lemma 3.9, p.18, and Corollary 3.15, p.23.

**Formalization Note** Under validity the neighbour is unique; it is picked by `Classical.choose`.
If `s` has no neighbour in `B` the value is `s` (never used). -/
noncomputable def portOf {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) (s : Fin n) :
    Fin n :=
  if h : ∃ u, u ∈ B ∧ G.Adj s u then Classical.choose h else s

end GnpColoring


