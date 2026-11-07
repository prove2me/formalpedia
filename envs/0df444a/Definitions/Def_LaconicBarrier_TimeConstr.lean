-- Prove2me | Definitions.Def_LaconicBarrier_TimeConstr
-- name    : LaconicBarrier_TimeConstr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:35.079637+00:00
-- url     : https://prove2.me/theorems/3298b611-9c88-441c-bbb0-191a35d99f38
-- title:
--   Time-constructible resource bounds
-- statement:
--   A resource bound $B$ on an index set is **time-constructible** if one machine computes $1^{B(i)}$ from the encoded index $i$ within $(B(i) + N_i + 2)^c$ steps for a constant $c$, where $N_i$ is the length of the encoded index. For bounds $B(\lambda, n)$ of two numbers the index is the pair, encoded as $(1^\lambda, 1^n)$.
--
--   The paper assumes all its resource bounds are time-constructible; the theorems of the mission state this assumption explicitly wherever a verifier must compute a bound.
--
--   **Formalization Note** Computing the bound in time polynomial in the bound and the input is weaker than the classical $O(B)$; every bound in the mission's statements is polynomially robust.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.1, p.15 (standing assumption: "all resource bounds … are time-constructible")

import Mathlib
import Definitions.Def_LaconicBarrier_PolyTimeOn

namespace LaconicBarrier

open KarpLiptonOM

/-- A resource bound `B` on an index type is **time-constructible**: one machine computes `1^{B(i)}`
from the encoded index within `(B(i) + N + 2)^c` steps, `N` the length of the encoded index (Jain,
Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.1, p.15: "Throughout, we
assume that all resource bounds … are time-constructible").

**Formalization Note** The paper does not fix the notion; computing the bound in time polynomial in
the bound and the input (rather than `O(B)`) is the weaker requirement, and every bound used in the
mission's statements is polynomially robust. For a bound `B(λ, n)` of two numbers the index is the
pair and its encoding is `(1^λ, 1^n)`. -/
def TimeConstr {ι : Type*} (enc : ι → List (List Bool)) (B : ι → ℕ) : Prop :=
  ∃ c : ℕ, TimeOn enc (fun i => unary (B i)) (fun i => (B i + (tupleEnc (enc i)).length + 2) ^ c)

end LaconicBarrier


