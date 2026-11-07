-- Prove2me | Definitions.Def_DDNNFNeg_BDD_Computes
-- name    : DDNNFNeg_BDD_Computes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:17.994458+00:00
-- url     : https://prove2.me/theorems/2f83d5f2-b31e-480f-8e64-674d0781ea52
-- title:
--   A branching program computes $f$
-- statement:
--   A branching program $B$ **computes** $f : \{0,1\}^X \to \{0,1\}$ if on every input $x$ the computation accepts — some sequence of guesses leads from the starting vertex to the $1$-terminal — if and only if $f(x) = 1$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 3.2, p.9

import Mathlib
import Definitions.Def_DDNNFNeg_BDD_acceptCount

namespace DDNNFNeg

/-- The branching program `B` computes `f : {0,1}^X → {0,1}` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 3.2, p.9): on
every input `x`, the computation accepts (some sequence of guesses leads from the starting
vertex to the `1`-terminal) if and only if `f x = 1`. -/
def BDD.Computes {X : Type*} (B : BDD X) (f : (X → Bool) → Bool) : Prop :=
  ∀ x : X → Bool, 0 < B.acceptCount x B.start ↔ f x = true

end DDNNFNeg


