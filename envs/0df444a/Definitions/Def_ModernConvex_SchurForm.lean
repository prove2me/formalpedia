-- Prove2me | Definitions.Def_ModernConvex_SchurForm
-- name    : ModernConvex_SchurForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:28:23.171273+00:00
-- url     : https://prove2.me/theorems/17f1ea5a-50fd-4545-8f4c-4e70de7d1cff
-- title:
--   The Schur form at a pivot: eliminating one coordinate from a quadratic form
-- statement:
--   **The Schur form at a pivot.** For a real symmetric matrix $M$ of order $n$ and an index $i$, the Schur form at $i$ is the quadratic form on the remaining coordinates
--   $$Q_i(v)=\sum_{j\ne i}\sum_{k\ne i}v_jv_kM_{jk}-\frac{1}{M_{ii}}\Big(\sum_{j\ne i}M_{ij}v_j\Big)^2 .$$
--   It is the quadratic form of the Schur complement $M_{/i}=M_{\ne i}-M_{\ne i,i}M_{ii}^{-1}M_{i,\ne i}$ of $M$ at $i$, but it is written as a form rather than as a matrix: that way no block inverse and no index bookkeeping between $\mathbb{R}^{n-1}$ and $\mathbb{R}^n$ is needed.
--
--   The form does not depend on the $i$-th coordinate of $v$ — it only involves coordinates $j\ne i$ — which is exactly what makes the elimination step work: the $i$-th coordinate can be used to cancel the square in the identity
--   $$v^{\mathsf T}Mv=M_{ii}\Big(v_i+\frac{1}{M_{ii}}\sum_{j\ne i}M_{ij}v_j\Big)^2+Q_i(v).$$
--   This is the recursive step of the rational PSD oracle: given $M$, either the form $Q_i$ is nonnegative for all $v$ — and then $M\succeq0$ when $M_{ii}>0$ — or a negative value of $Q_i$ yields a direction of negative quadratic form for $M$.
-- source:
--   Schur complement / symmetric Gaussian elimination at a 1x1 pivot; the elimination step of the symmetric-elimination PSD test, in the form used by Bubeck arXiv:1405.4980v2 Thm 2.4's separation oracle.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

/-!
# The Schur form at a pivot

For a symmetric matrix `M` and an index `i`, the **Schur form** at `i` is the quadratic form on
the remaining coordinates obtained by eliminating `i`:

  `schurForm M i v = Σ_{j,k≠i} v j v k M j k − (M i i)⁻¹ (Σ_{j≠i} M i j v j)²`.

It does not depend on `v i`, and completing the square gives

  `v ᵀ M v = M i i (v i + (M i i)⁻¹ Σ_{j≠i} M i j v j)² + schurForm M i v`.

This is the elimination step of the PSD oracle, stated on quadratic forms rather than on the Schur
complement matrix, so that no block inverse is ever needed.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- The Schur form of `M` at the index `i`, on the remaining coordinates. -/
noncomputable def schurForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (v : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i, v j * (M j k * v k)
    - (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j) ^ 2

end ModernConvex.Relaxations


