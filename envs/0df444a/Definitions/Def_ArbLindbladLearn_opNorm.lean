-- Prove2me | Definitions.Def_ArbLindbladLearn_opNorm
-- name    : ArbLindbladLearn_opNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:28.277774+00:00
-- url     : https://prove2.me/theorems/17cb3f74-5810-4473-8165-c371a8b3b955
-- title:
--   Operator (spectral) norm $\|A\|_\infty$
-- statement:
--   For an operator $A$ on $\mathcal H=(\mathbb C^2)^{\otimes n}$, $\|A\|_\infty$ is the operator norm: the largest singular value, i.e. the norm of $A$ as a linear map on the Euclidean space $\mathbb C^{2^n}$.
--
--   All matrix norms of the paper are Schatten norms, and $\|\cdot\|_\infty$ is the one used for the dynamical strength.
--
--   **Formalization Note** This is not Mathlib's default entrywise sup norm on `Matrix`.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), §2.1, p.11

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The operator (spectral, Schatten-`∞`) norm `‖A‖_∞` of an `n`-qubit operator (§2.1,
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.11): the norm of `A` as a continuous linear map on
the Euclidean space `ℂ^{2ⁿ}`.

**Formalization Note** This is not Mathlib's default `Matrix` norm (the entrywise sup norm). -/
def opNorm {n : ℕ} (A : Op (Qubits n)) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Qubits n) A‖

end ArbLindbladLearn


