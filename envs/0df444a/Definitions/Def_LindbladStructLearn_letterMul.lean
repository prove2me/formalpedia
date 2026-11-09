-- Prove2me | Definitions.Def_LindbladStructLearn_letterMul
-- name    : LindbladStructLearn_letterMul
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:52.70354+00:00
-- url     : https://prove2.me/theorems/2a67d3f5-c0b4-4d70-9074-aafb90c0279f
-- title:
--   Product of single-qubit Pauli letters (Pauli part)
-- statement:
--   Encode the single-qubit Paulis $I, X, Y, Z$ as the letters $0,1,2,3$. For letters $a, b$, `letterMul a b` is the letter of the Pauli part $\mathcal P(\sigma_a\sigma_b)$ of the product, so that $\sigma_a\sigma_b = c(\sigma_a\sigma_b)\,\sigma_{\mathrm{letterMul}(a,b)}$; in this encoding it is the bitwise exclusive or of $a$ and $b$.
--
--   It is the single-site building block of the product of $n$-qubit Paulis.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, Eq. (2.2), p.13

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Product of single-qubit Pauli letters up to phase (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, Eq. (2.2), p.13): the letter
`𝒫(σ_a σ_b)`, with the encoding `0 = I, 1 = X, 2 = Y, 3 = Z`.

**Formalization Note** Letters are `Fin 4` with `0 = I, 1 = X, 2 = Y, 3 = Z`, the encoding of
the reused `LindbladTolerant.Testing.onePauli`. The table is `a xor b`. -/
def letterMul : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

end LindbladStructLearn


