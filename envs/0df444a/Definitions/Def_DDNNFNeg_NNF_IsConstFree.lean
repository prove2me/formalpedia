-- Prove2me | Definitions.Def_DDNNFNeg_NNF_IsConstFree
-- name    : DDNNFNeg_NNF_IsConstFree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:06.939279+00:00
-- url     : https://prove2.me/theorems/eba03999-8cf3-46b0-a679-a5c8021804f9
-- title:
--   NNF without constant leaves
-- statement:
--   An NNF is **constant-free** if none of its gates is a constant leaf, so that every input gate is labelled by a variable or its negation. This is the paper's definition of an NNF.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.1, p.8

import Mathlib
import Definitions.Def_DDNNFNeg_NNF

namespace DDNNFNeg

/-- The NNF `C` has no constant leaves: every input gate is labelled by a variable or its
negation, as in the paper's definition of an NNF (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.1, p.8). -/
def NNF.IsConstFree {X : Type*} (C : NNF X) : Prop :=
  ∀ (k : Fin C.size) (b : Bool), C.gate k ≠ .const b

end DDNNFNeg


