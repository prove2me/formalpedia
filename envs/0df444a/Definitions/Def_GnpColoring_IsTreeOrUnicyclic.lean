-- Prove2me | Definitions.Def_GnpColoring_IsTreeOrUnicyclic
-- name    : GnpColoring_IsTreeOrUnicyclic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:31.445429+00:00
-- url     : https://prove2.me/theorems/1fe1ee7f-b6e6-4f52-83e7-aa633d0c1801
-- title:
--   $G[B]$ is a tree or unicyclic
-- statement:
--   $G[B]$ is a tree or is unicyclic ("a tree with at most one extra edge"). In particular $G[B]$ is connected and $B$ is nonempty.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.2 (1), p.15

import Mathlib
import Definitions.Def_GnpColoring_IsTreeBlock
import Definitions.Def_GnpColoring_IsUnicyclicBlock

open scoped Classical
open Finset

namespace GnpColoring

/-- **`G[B]` is a tree or unicyclic** ("induces a tree with at most one extra edge").

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.2 (1), p.15; Theorem 4.2 (ii), p.36; Lemmas 5.5 and 5.8, pp.45 and 52. -/
def IsTreeOrUnicyclic {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) : Prop :=
  IsTreeBlock G B ∨ IsUnicyclicBlock G B

end GnpColoring


