-- Prove2me | Definitions.Def_AggCG_encodeRatVec
-- name    : AggCG_encodeRatVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:25.361212+00:00
-- url     : https://prove2.me/theorems/fc0cec9d-7a68-4565-9908-32d0e14fea51
-- title:
--   The binary code of a rational vector
-- statement:
--   A rational vector is coded coordinate by coordinate with the published self-delimiting binary code of rationals: a sign bit, then the absolute numerator and the denominator, each in binary.
--
--   This is how an algorithm's returned multiplier vector, and an NP certificate, are written: "a rational point of polynomial binary length" (p.51).
--
--   **Formalization Note** Binary rather than the unary list code of the Cook–Levin layer, since a unary output would shrink the class of algorithms that the approximation clauses cover.
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), proof of Theorem I.3, p.51 (PDF p.52)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace AggCG

/-- A rational vector in binary, coordinates in order, each by the published `encRat`: sign bit, absolute numerator and denominator, in self-delimiting binary (Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), p.51, PDF p.52: "a rational point of polynomial binary length").

**Formalization Note** Binary, since a unary output code would shrink the class of algorithms that the approximation clauses cover. The length `m` is known from the context, so it is not repeated. -/
def encodeRatVec {m : ℕ} (q : Fin m → ℚ) : List Bool :=
  (List.ofFn q).flatMap QAlgorithms.LocalHamiltonian.encRat

end AggCG


