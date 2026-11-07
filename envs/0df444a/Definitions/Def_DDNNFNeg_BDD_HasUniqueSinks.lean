-- Prove2me | Definitions.Def_DDNNFNeg_BDD_HasUniqueSinks
-- name    : DDNNFNeg_BDD_HasUniqueSinks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:22:17.246341+00:00
-- url     : https://prove2.me/theorems/fcca8f5d-59fc-47ee-a6b9-1731644c0b59
-- title:
--   Branching program with at most one sink of each label
-- statement:
--   A branching program has **unique sinks** if it has at most one sink labelled $0$ and at most one sink labelled $1$, as in Definition 3.2 ("sinks labeled 1 and 0").
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 3.2, p.9

import Mathlib
import Definitions.Def_DDNNFNeg_BDD

namespace DDNNFNeg

/-- The branching program `B` has at most one sink of each label `0`, `1`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 3.2, p.9: "sinks labeled 1 and 0"). -/
def BDD.HasUniqueSinks {X : Type*} (B : BDD X) : Prop :=
  ∀ (i j : Fin B.size) (b : Bool), B.node i = .sink b → B.node j = .sink b → i = j

end DDNNFNeg


