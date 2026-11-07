-- Prove2me | Definitions.Def_DDNNFNeg_BDD_IsUnambiguous
-- name    : DDNNFNeg_BDD_IsUnambiguous
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:32.257349+00:00
-- url     : https://prove2.me/theorems/be9a0826-4f2b-42bb-ad4f-51cf68ce220a
-- title:
--   Unambiguous branching program
-- statement:
--   A branching program is **unambiguous** if on every input there is at most one sequence of guesses that leads from the starting vertex to a $1$-terminal.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 3.2, p.9

import Mathlib
import Definitions.Def_DDNNFNeg_BDD_acceptCount

namespace DDNNFNeg

/-- The branching program `B` is unambiguous (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 3.2, p.9): on every input there
is at most one sequence of guesses that leads from the starting vertex to a `1`-terminal. -/
def BDD.IsUnambiguous {X : Type*} (B : BDD X) : Prop :=
  ∀ x : X → Bool, B.acceptCount x B.start ≤ 1

end DDNNFNeg


