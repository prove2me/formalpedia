-- Prove2me | Definitions.Def_DistQuantumQuery_traceNorm
-- name    : DistQuantumQuery_traceNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:02.699901+00:00
-- url     : https://prove2.me/theorems/bb0cfb65-1e13-4b80-9fb4-9ce944d07ede
-- title:
--   Operator norm $\|A\|$, Hilbert–Schmidt inner product $\langle A,B\rangle=\mathrm{Tr}[A^\dagger B]$, trace norm $\|A\|_{\mathrm{tr}}$ and root fidelity $F(A,B)=\|\sqrt A\sqrt B\|_1$
-- statement:
--   For complex matrices indexed by finite sets this module fixes four standard quantities.
--
--   1. The **operator (spectral) norm** $\|A\|=\|A\|_\infty=\max_i s_i(A)$, the largest singular value.
--   2. The **Hilbert–Schmidt inner product** $\langle A,B\rangle:=\mathrm{Tr}[A^\dagger B]$, conjugate-linear in $A$.
--   3. The **trace norm**
--   $$
--   \|A\|_{\mathrm{tr}}=\|A\|_1=\mathrm{Tr}\big[\sqrt{A^\dagger A}\big]=\sum_i s_i(A),
--   $$
--   the sum of the singular values of $A$ (not halved).
--   4. The **root fidelity** of positive semidefinite $A,B$, $F(A,B):=\|\sqrt A\sqrt B\|_1$ (the non-squared fidelity).
--
--   These are the norms in which the paper's adversary measures, relaxed targets and fidelity conditions are stated.
--
--   **Formalization Note** The operator norm is Mathlib's L2 operator norm on matrices. Singular values are square roots of the eigenvalues of $A^\dagger A$. The square root $\sqrt A$ uses the Hermitian functional calculus and is $0$ on a non-Hermitian argument; the fidelity is only applied to positive semidefinite matrices.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), §2.1 p.11 (⟨A,B⟩), §2.2.1 p.12 (Schatten norms, operator norm), §2.2.3 p.13 (fidelity)

import Mathlib

open scoped Matrix

namespace DistQuantumQuery

/-- The **operator (spectral) norm** `‖A‖ = ‖A‖_∞ = max_i s_i(A)` of a complex matrix
(Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835, held version,
sha256 6334ffaf…, §2.2.1, p.12: "Throughout the paper, we use ∥A∥ to denote the operator norm ∥A∥∞").

**Formalization Note** This is Mathlib's L2 operator norm on matrices
(`Matrix.instL2OpNormedAddCommGroup`), the norm of the induced linear map on Euclidean space,
named here so that no other matrix norm instance is picked up. -/
noncomputable def opNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ :=
  @Norm.norm (Matrix m n ℂ) (Matrix.instL2OpNormedAddCommGroup).toNorm A

/-- The **Hilbert–Schmidt inner product** `⟨A, B⟩ := Tr[A†B]` (arXiv:2610.06835, held version,
§2.1, p.11), conjugate-linear in the first argument. -/
noncomputable def hsInner {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) : ℂ :=
  Matrix.trace (Aᴴ * B)

/-- The **trace norm** `‖A‖_tr := ‖A‖₁ = Tr[√(A†A)] = Σ_i s_i(A)`, the sum of the singular values
of `A` (arXiv:2610.06835, held version, sha256 6334ffaf…, §2.2.1, p.12).

**Formalization Note** The singular values are the square roots of the eigenvalues of the
positive semidefinite matrix `AᴴA` (Mathlib's `IsHermitian.eigenvalues`). The norm is **not**
halved. -/
noncomputable def traceNorm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The positive square root `√A` of a Hermitian (in all uses: positive semidefinite) matrix,
by the Hermitian functional calculus.

**Formalization Note** On a non-Hermitian argument the value is `0`; the fidelity below is only
ever applied to positive semidefinite matrices. -/
noncomputable def psdSqrt {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Matrix n n ℂ :=
  if h : A.IsHermitian then h.cfc Real.sqrt else 0

/-- The (root, non-squared) **fidelity** `F(A, B) := ‖√A √B‖₁` of positive semidefinite matrices
(arXiv:2610.06835, held version, sha256 6334ffaf…, §2.2.3, p.13).

**Formalization Note** `‖·‖₁` is the trace norm `traceNorm`; `√·` is `psdSqrt`. -/
noncomputable def fidelity {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) : ℝ :=
  traceNorm (psdSqrt A * psdSqrt B)

end DistQuantumQuery


