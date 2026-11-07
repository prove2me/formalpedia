-- Prove2me | Definitions.Def_DDNNFNeg_NNF_Computes
-- name    : DDNNFNeg_NNF_Computes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:17.802231+00:00
-- url     : https://prove2.me/theorems/b5f17ae6-e902-4525-81b2-fe450c4568be
-- title:
--   An NNF computes $f$
-- statement:
--   An NNF $C$ over $X$ **computes** the Boolean function $f : \{0,1\}^X \to \{0,1\}$ if its output gate takes the value $f(x)$ on every assignment $x \in \{0,1\}^X$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.1, p.8

import Mathlib
import Definitions.Def_DDNNFNeg_NNF_eval

namespace DDNNFNeg

/-- The NNF `C` computes the Boolean function `f : {0,1}^X → {0,1}`: its output gate takes
the value `f x` on every assignment `x` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.1, p.8). -/
def NNF.Computes {X : Type*} (C : NNF X) (f : (X → Bool) → Bool) : Prop :=
  ∀ x : X → Bool, C.eval x C.out = f x

end DDNNFNeg


