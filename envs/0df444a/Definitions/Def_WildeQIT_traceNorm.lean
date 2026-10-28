-- Prove2me | Definitions.Def_WildeQIT_traceNorm
-- name    : WildeQIT_traceNorm
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T03:51:19.886281+00:00
-- url     : https://prove2.me/theorems/12e38c10-56de-44d5-9dad-1340e7ee9991
-- title:
--   Trace norm (Schatten 1-norm) $\|M\|_1 = \mathrm{Tr}\{|M|\}$
-- statement:
--   **Definition 9.1.1 (Trace Norm).** The *trace norm* or *Schatten 1-norm* $\|M\|_1$ of an operator $M \in \mathcal{L}(\mathcal{H}, \mathcal{H}')$ is defined as
--
--   $$
--   \|M\|_1 \equiv \mathrm{Tr}\{|M|\},
--   $$
--
--   where $|M| \equiv \sqrt{M^\dagger M}$.
--
--   The trace norm is the basic distance-measure primitive of Chapter 9: the trace distance between two operators is the trace norm of their difference, and all of its properties (non-negativity, homogeneity, the triangle inequality, isometric invariance, convexity, the variational characterization over unitaries) are stated in terms of it.
--
--   **Formalization Note.** Operators $M \in \mathcal{L}(\mathcal{H}, \mathcal{H}')$ on finite-dimensional spaces are matrices `M : Matrix m n ℂ` indexed by finite types `m` (rows, $\mathcal{H}'$) and `n` (columns, $\mathcal{H}$); rectangular matrices are allowed. $M^\dagger$ is `Mᴴ`, and $\sqrt{M^\dagger M}$ is Mathlib's continuous-functional-calculus square root `CFC.sqrt (Mᴴ * M)` of the positive semidefinite matrix $M^\dagger M$ (with the Loewner order `open scoped MatrixOrder`). The trace of that positive semidefinite matrix is a real number; `WildeQIT.traceNorm M : ℝ` is its real part.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §9.1.1 "Trace Norm", Definition 9.1.1 (Trace Norm).

import Mathlib.Analysis.Matrix.Order

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.1.1, Definition 9.1.1 (Trace Norm).

The trace norm (Schatten 1-norm) of an operator `M ∈ L(H, H')` is
`‖M‖₁ ≡ Tr{|M|}`, where `|M| ≡ √(M†M)`.

Operators are finite-dimensional matrices over `ℂ`; `Mᴴ` is the conjugate transpose (`M†`),
and `CFC.sqrt` is Mathlib's positive square root of a positive semidefinite matrix.
-/

open Matrix
open scoped MatrixOrder

namespace WildeQIT

/-- **Definition 9.1.1 (Trace Norm).** `‖M‖₁ = Tr{|M|}` with `|M| = √(M†M)`,
for a (possibly rectangular) matrix `M : Matrix m n ℂ`. The trace of the positive
semidefinite matrix `√(M†M)` is a real number; we take its real part to land in `ℝ`. -/
noncomputable def traceNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (Mᴴ * M))).re

end WildeQIT


