-- Prove2me | Definitions.Def_GnpColoring_extBoundary
-- name    : GnpColoring_extBoundary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:50.935075+00:00
-- url     : https://prove2.me/theorems/71d3cd12-e9fc-4ec9-bf9e-dc12cb29884b
-- title:
--   The exterior boundary $\partial U$
-- statement:
--   For a vertex set $U$, its **exterior vertex boundary** is
--
--   $$\partial U=\{v\in V\setminus U:\ N_G(v)\cap U\neq\emptyset\}.$$
--
--   For a block $B$ of $S$, $\partial B\subseteq S$ consists of singletons.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 2.1, p.13

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The exterior vertex boundary** `∂U = {v ∈ V ∖ U : N_G(v) ∩ U ≠ ∅}`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 2.1, p.13 ("for its exterior vertex boundary. In particular, ∂B consists of
singleton vertices when B is a block in our partition"); Definition 3.2 (2), p.15. -/
noncomputable def extBoundary {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) :
    Finset (Fin n) :=
  univ.filter fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj v u

end GnpColoring


