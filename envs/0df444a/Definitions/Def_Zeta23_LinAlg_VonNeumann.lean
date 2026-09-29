-- Prove2me | Definitions.Def_Zeta23_LinAlg_VonNeumann
-- name    : Zeta23_LinAlg_VonNeumann
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:00:47.032014+00:00
-- url     : https://prove2.me/theorems/35b92113-e29f-460e-83a3-b23a85219ff2
-- title:
--   Entrywise squared-norm matrix $S_{ij} = \|W_{ij}\|^2$ for von Neumann's trace inequality
-- statement:
--   This bundle contains a single auxiliary definition for the proof of von Neumann's trace inequality: for a matrix $W$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, `normSqMatrix W` is the real matrix with entries
--   $$S_{ij} \;:=\; \|W_{ij}\|^2 .$$
--
--   Its role: diagonalizing Hermitian $A = U_a D_a U_a^{H}$ and $B = U_b D_b U_b^{H}$ and setting $W := U_a^{H} U_b$ (unitary), one computes $\operatorname{tr}(AB) = \sum_{k,l} a_k \|W_{kl}\|^2 b_l$. When $W$ is unitary the matrix $S$ is doubly stochastic, so by Birkhoff–von Neumann it is a convex combination of permutation matrices, and the rearrangement inequality yields von Neumann's bound $\operatorname{Re}\operatorname{tr}(AB) \le \sum_i a_i b_i$ for eigenvalues sorted in decreasing order.
--
--   The trace inequality proved with this definition is part of the `RHLinalg` linear-algebra layer (paper §3) feeding the matrix-variational lower bound for the proportion of critical-line zeros.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/VonNeumann.lean

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_PosIndex

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
# Von Neumann's trace inequality

For Hermitian `A, B` with eigenvalues sorted in decreasing order
`a₀ ≥ a₁ ≥ …` and `b₀ ≥ b₁ ≥ …`,

  `Re tr(AB) ≤ ∑ᵢ aᵢ bᵢ`.

## Proof outline

Diagonalise `A = Uₐ Dₐ Uₐᴴ` and `B = Uᵦ Dᵦ Uᵦᴴ`. Setting `W := Uₐᴴ Uᵦ`
(unitary), a direct calculation gives

  `tr(AB) = tr(Dₐ W Dᵦ Wᴴ) = ∑ₖₗ aₖ · ‖Wₖₗ‖² · bₗ`.

The matrix `Sₖₗ := ‖Wₖₗ‖²` is doubly stochastic over `ℝ` (rows and columns
of a unitary matrix are unit vectors). By **Birkhoff–von Neumann**
(`exists_eq_sum_perm_of_mem_doublyStochastic`) every doubly stochastic
matrix is a convex combination of permutation matrices: `S = ∑_σ w_σ P_σ`.
For each permutation `σ`, `∑ₖ aₖ b_{σ k} ≤ ∑ₖ aₖ bₖ` by the **rearrangement
inequality** (`Monovary.sum_mul_comp_perm_le_sum_mul`), since both `a` and
`b` are antitone (hence monovary). Averaging over `σ` with weights `w_σ`
gives the result.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise squared-norm `‖Wᵢⱼ‖²` of a matrix, as a real matrix. -/
def normSqMatrix (W : Matrix n n 𝕜) : Matrix n n ℝ :=
  Matrix.of fun i j => ‖W i j‖ ^ 2

section Bilinear



end Bilinear

section Rearrangement



end Rearrangement


end RHLinalg


