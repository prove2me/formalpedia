-- Prove2me | Definitions.Def_Zeta23_LinAlg_PosIndex
-- name    : Zeta23_LinAlg_PosIndex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T19:59:40.302517+00:00
-- url     : https://prove2.me/theorems/09c40c91-3982-4335-88ca-48abc57e56a9
-- title:
--   Positive index $n_+(A)$, real trace, and Frobenius norm of a Hermitian matrix
-- statement:
--   This bundle sets up the basic spectral invariants of a Hermitian matrix used in the linear-algebra part of the project (paper §3). Throughout, $A$ is an $n \times n$ matrix over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ (an `RCLike` field), and `hA` is a proof that $A$ is Hermitian.
--
--   The central definition is the **positive index**
--   $$n_+(A) \;:=\; \#\{\, i : \lambda_i(A) > 0 \,\},$$
--   the number of strictly positive eigenvalues of $A$ (counted over Mathlib's eigenvalue enumeration `hA.eigenvalues`); by Sylvester's law of inertia this equals the maximal dimension of a subspace on which the form $x \mapsto x^{H} A x$ is positive definite. Alongside it the file defines the real-valued trace $\operatorname{rtrace}(A) := \operatorname{Re} \operatorname{tr}(A)$ (for Hermitian $A$ this is the full trace, which is real), the squared Frobenius norm $\|A\|_F^2 := \operatorname{Re}\operatorname{tr}(A^{H}A) = \sum_{i,j}|A_{ij}|^2$ (`frobSq`), and a canonical reindexing equivalence `eigEquiv` : $\mathrm{Fin}(\#n) \simeq n$ aligning the two eigenvalue enumerations.
--
--   These definitions are part of the self-contained `RHLinalg` development accompanying §3 of the paper. They underpin the rank–trace inequality [lem:ranktrace] and the inertia arguments by which the matrix-variational method converts trace information about the mollified Gram matrix into a lower bound for the number of critical-line zeros.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/PosIndex.lean, docstring tag [lem:ranktrace]

import Mathlib.Analysis.Matrix.PosDef

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/

/-!
# Positive index of a Hermitian matrix

For a Hermitian matrix `A` over `𝕜 = ℝ` or `ℂ`, the *positive index*
`n₊(A)` is the number of strictly positive eigenvalues. By Sylvester's law
of inertia this equals the maximal dimension of a subspace on which the
Hermitian form `x ↦ xᴴ A x` is positive definite.

This file defines `posIndex` via the eigenvalue count, together with the
real-valued trace `rtrace` and squared Frobenius norm `frobSq` needed for
the rank–trace inequality (paper §3, `lem:ranktrace`).
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index `n₊(A)` of a Hermitian matrix: the number of strictly
positive eigenvalues. Equivalently (Sylvester's law of inertia), the maximal
dimension of a subspace on which the form `x ↦ xᴴAx` is positive definite. -/
def posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℕ :=
  #{i | 0 < hA.eigenvalues i}





/-- Real part of the trace. For a Hermitian matrix this is the full trace,
since the trace of a Hermitian matrix is real. -/
def rtrace (A : Matrix n n 𝕜) : ℝ := RCLike.re A.trace

/-- Squared Frobenius norm, `‖A‖_F² = Re tr(AᴴA) = ∑ᵢⱼ |Aᵢⱼ|²`. -/
def frobSq (A : Matrix n n 𝕜) : ℝ := RCLike.re (Aᴴ * A).trace


section Reindex

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)

/-- The canonical equivalence `Fin (card n) ≃ n` under which
`eigenvalues (e k) = eigenvalues₀ k`. -/
def eigEquiv : Fin (Fintype.card n) ≃ n :=
  Fintype.equivOfCardEq (Fintype.card_fin _)




end Reindex


end RHLinalg


