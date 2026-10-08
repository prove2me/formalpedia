-- Prove2me | Definitions.Def_MatrixTail_Master_Model
-- name    : MatrixTail_Master_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:34.104579+00:00
-- url     : https://prove2.me/theorems/342f6731-69f7-490e-aa9c-a31e67ffd436
-- title:
--   §2 — complex Hermitian matrices, λmax, matrix exp/log, trace exponential, entrywise expectation
-- statement:
--   This file fixes the matrix and probability conventions of Tropp's *User-Friendly Tail Bounds for Sums of Random Matrices* (§2). All matrices are $d\times d$ arrays of **complex** numbers; a self-adjoint (Hermitian) matrix $A$ has real eigenvalues.
--
--   1. **Random matrices.** The space of $d\times d$ complex matrices carries the Borel σ-algebra of its $d^2$ entries, so a random matrix is a measurable map $X:\Omega\to\mathbb C^{d\times d}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$, and independence of a family of random matrices is independence of these maps.
--   2. **Largest eigenvalue.** $\lambda_{\max}(A)$ is the supremum of the real spectrum of $A$; for Hermitian $A$ and $d\ge 1$ it is the algebraically largest eigenvalue.
--   3. **Matrix functions.** For a Hermitian $A = Q\Lambda Q^*$ and $f:\mathbb R\to\mathbb R$, $f(A) := Q f(\Lambda) Q^*$ (display (2.1)). In particular
--   $$e^{A} := Q e^{\Lambda} Q^*, \qquad \log A := Q \log(\Lambda) Q^* \quad (A \text{ positive definite}),$$
--   so that $\log(e^A) = A$ for every Hermitian $A$ (display (2.7)).
--   4. **Trace exponential.** $\operatorname{tr} e^{A}$, a real number for Hermitian $A$.
--   5. **Expectation.** For a random matrix $X$, $\mathbb E X$ is the matrix of the expectations of its entries, and $X$ is called *integrable* when every entry is integrable.
--
--   These objects carry the whole of §3: the matrix moment generating function $\mathbb E e^{\theta X}$, the cumulant generating function $\log \mathbb E e^{\theta X}$, and the tail probability of $\lambda_{\max}$.
--
--   **Formalization Note.** Matrix functions are Mathlib's continuous functional calculus `cfc` on Hermitian matrices; outside the Hermitian matrices (for `exp`) and the positive-definite cone (for `log`) the values are not the paper's and are never used. Integrability is a separate predicate, because Lean's integral of a non-integrable function is $0$; statements assume it exactly where the paper takes an expectation (the standing regularity assumption of §2.2).
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, pp. 7–9, §§2.1–2.5, (2.1), (2.7)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Master

/-- The Borel (product) σ-algebra on `d × d` complex matrices, so that a random matrix is a measurable map
`Ω → Matrix (Fin d) (Fin d) ℂ` and `iIndepFun` applies to families of random matrices.
Tropp, *User-Friendly Tail Bounds for Sums of Random Matrices*, arXiv:1004.4389v7, §2.2, p. 7.

**Formalization Note.** Matrices are complex (§2.1, p. 7: "A matrix is a finite, two-dimensional array of
complex numbers"); the σ-algebra is the product of the Borel σ-algebras of the `d²` complex entries. -/
noncomputable instance instMeasurableSpaceMat (d : ℕ) : MeasurableSpace (Matrix (Fin d) (Fin d) ℂ) := by
  unfold Matrix; infer_instance

/-- `λmax(A)`, the algebraically largest eigenvalue of a self-adjoint matrix (arXiv:1004.4389v7, §2.1, p. 7):
the supremum of its real spectrum. For a Hermitian matrix with `d ≥ 1` this is its largest eigenvalue.

**Formalization Note.** For `d = 0` the spectrum is empty and this is `sSup ∅ = 0`; every statement using
`lambdaMax` therefore assumes `[NeZero d]`. -/
noncomputable def lambdaMax {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := sSup (spectrum ℝ A)

/-- `e^A`, by the spectral definition (2.1) with `f = exp` (arXiv:1004.4389v7, §2.4, p. 8), i.e. Mathlib's
continuous functional calculus `cfc Real.exp A`. On a Hermitian matrix this is the matrix exponential; on a
non-Hermitian matrix `cfc` returns the junk value `0`, so it is only applied to Hermitian matrices. -/
noncomputable def mexp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ := cfc Real.exp A

/-- `log A` on the positive-definite cone, by (2.1) with `f = log`, i.e. `cfc Real.log A`; it is the inverse of
`mexp` there (arXiv:1004.4389v7, §2.5, display (2.7), p. 8). Outside the positive-definite cone the value is
not the paper's object (Mathlib's `Real.log` sends `0` to `0`), and no statement uses it there. -/
noncomputable def mlog {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ := cfc Real.log A

/-- The trace exponential `tr e^A` (arXiv:1004.4389v7, §2.4, p. 8): the real part of the trace of `mexp A`,
which is real for Hermitian `A`. -/
noncomputable def trExp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace (mexp A)).re

/-- `E X`, the entrywise expectation of a random matrix `X : Ω → Matrix (Fin d) (Fin d) ℂ` under `P`
(arXiv:1004.4389v7, §2.2 and §2.7, pp. 7–9). If an entry is not integrable, Lean's Bochner integral gives
`0` for it, so statements taking `mean` also assume `MatIntegrable`. -/
noncomputable def mean {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => ∫ ω, X ω i j ∂P

/-- Every entry of the random matrix `X` is integrable under `P`: the §2.2 (p. 7) standing assumption that
"all random variables are sufficiently regular that we are justified in computing expectations", made
explicit for one random matrix. -/
def MatIntegrable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ i j, Integrable (fun ω => X ω i j) P

end MatrixTail.Master


