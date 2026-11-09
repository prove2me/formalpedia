-- Prove2me | Definitions.Def_LindbladStructLearn_toIdx
-- name    : LindbladStructLearn_toIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:06.43431+00:00
-- url     : https://prove2.me/theorems/669efc9a-2e2e-4404-ae42-c6de215fc804
-- title:
--   Restriction of a coefficient vector to the $k$-local terms
-- statement:
--   The vector $\lambda \in \mathbb C^m$ of a coefficient vector: its entries on the $k$-local pairs with $P_1 \ne I$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.1, p.13; Definition 2.2, p.14

import Mathlib
import Definitions.Def_LindbladStructLearn_Idx

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The vector `λ ∈ ℂ^m` of a coefficient vector: its entries on the `k`-local pairs with
`P₁ ≠ I` (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.1, p.13 and Definition 2.2, p.14). -/
def toIdx {n k : ℕ} (x : Pauli n × Pauli n → ℂ) : Idx n k → ℂ := fun a => x a.1

end LindbladStructLearn


