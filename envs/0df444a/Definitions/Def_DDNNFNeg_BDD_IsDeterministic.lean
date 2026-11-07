-- Prove2me | Definitions.Def_DDNNFNeg_BDD_IsDeterministic
-- name    : DDNNFNeg_BDD_IsDeterministic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:22:00.009321+00:00
-- url     : https://prove2.me/theorems/0e797dc1-7c7c-4032-9ab1-ea3a046cb5f5
-- title:
--   Branching program without nondeterministic vertices
-- statement:
--   A branching program is **deterministic** if it has no nondeterministic ($\vee$) vertices. A read-once deterministic branching program is an **FBDD**.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 3.2, p.9

import Mathlib
import Definitions.Def_DDNNFNeg_BDD

namespace DDNNFNeg

/-- The branching program `B` has no nondeterministic vertices (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 3.2, p.9: "An
FBDD is an nFBDD without any nondeterministic vertices"): no vertex is labelled `∨`. -/
def BDD.IsDeterministic {X : Type*} (B : BDD X) : Prop :=
  ∀ (k l r : Fin B.size), B.node k ≠ .choice l r

end DDNNFNeg


