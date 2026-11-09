-- Prove2me | Definitions.Def_LindbladStructLearn_ext
-- name    : LindbladStructLearn_ext
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:16.150268+00:00
-- url     : https://prove2.me/theorems/36da7eea-8b68-43f1-8dc0-86a09a0861dd
-- title:
--   Zero extension of a vector on the $k$-local terms
-- statement:
--   A vector $x \in \mathbb C^m$ indexed by the $k$-local pairs with $P_1 \ne I$ is extended by $0$ to a coefficient vector on all pairs. This is how $\mathcal L_x$, $\|x\|_{B_1}$ and $\deg(x)$ are applied to $x \in \mathbb C^m$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.1, Definition 2.2, p.14

import Mathlib
import Definitions.Def_LindbladStructLearn_Idx

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- A vector on the `k`-local pairs, extended by zero to all pairs (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.1, Definition 2.2,
p.14: `λ ∈ ℂ^m` indexes the terms of `L_λ`). Used to apply `L_x`, `‖·‖_B1` and `deg` to `x ∈ ℂ^m`. -/
def ext {n k : ℕ} (x : Idx n k → ℂ) : Pauli n × Pauli n → ℂ := fun P =>
  if h : P.1 ≠ 0 ∧ (pairSupport P).card ≤ k then x ⟨P, h⟩ else 0

end LindbladStructLearn


