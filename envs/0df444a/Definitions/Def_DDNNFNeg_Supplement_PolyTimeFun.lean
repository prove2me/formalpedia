-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_PolyTimeFun
-- name    : DDNNFNeg_Supplement_PolyTimeFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:45:57.007064+00:00
-- url     : https://prove2.me/theorems/bde41d80-b8bd-432a-aeee-db724d3b3a29
-- title:
--   Polynomial-time computable function on binary strings
-- statement:
--   A function $A : \{0,1\}^* \to \{0,1\}^*$ is **computable in deterministic polynomial time** if some Turing machine outputs $A(x)$ on every input $x$ within $p(|x|)$ steps, for a polynomial $p$.
--
--   **Formalization Note** The machine model is Mathlib's multi-stack Turing machines (`FinTM2`, `Turing.TM2ComputableInPolyTime`) with the identity encoding of binary strings.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §4, pp.9–11

import Mathlib

namespace DDNNFNeg.Supplement

/-- The function `A : {0,1}* → {0,1}*` is computable in deterministic polynomial time
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §4, pp.9–11): some (multi-stack) Turing machine of Mathlib's `FinTM2` model outputs `A x`
on input `x` within `p(|x|)` steps, for a polynomial `p`.

**Formalization Note** The input and output alphabet is `Bool` and the encodings are the
identity on binary strings (`Turing.TM2ComputableInPolyTime id id A`). -/
def PolyTimeFun (A : List Bool → List Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    (id : List Bool → List Bool) A)

end DDNNFNeg.Supplement


