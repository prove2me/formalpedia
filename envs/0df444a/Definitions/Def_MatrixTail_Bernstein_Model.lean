-- Prove2me | Definitions.Def_MatrixTail_Bernstein_Model
-- name    : MatrixTail_Bernstein_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:09:30.263983+00:00
-- url     : https://prove2.me/theorems/8db1e403-26ce-4d7d-ace5-cfdcf77dd7fe
-- title:
--   §2 and Theorem 6.1 — complex Hermitian matrices, λmax, spectral norm, matrix exp/log, trace exponential, entrywise expectation, Bennett's function h
-- statement:
--   This file fixes the objects in which Tropp's matrix Bennett and Bernstein inequalities are stated.
--
--   Matrices are $d\times d$ arrays of complex numbers (§2.1). A random matrix is a measurable map $X:\Omega\to\mathbb C^{d\times d}$, where the matrix space carries the Borel (product) $\sigma$-algebra of its entries.
--
--   1. For a self-adjoint (Hermitian) matrix $A$, $\lambda_{\max}(A)$ is its algebraically largest eigenvalue, defined as the supremum of its real spectrum.
--   2. $\|A\|$ is the spectral norm, the operator norm of $A$ acting on $\mathbb C^d$ with the Euclidean norm.
--   3. $e^{A}$ and $\log A$ are defined spectrally: if $A=\sum_i \lambda_i u_iu_i^*$ then $f(A)=\sum_i f(\lambda_i)u_iu_i^*$ for $f=\exp$ and, on positive-definite matrices, $f=\log$ (display (2.1)).
--   4. The trace exponential is $\operatorname{tr} e^{A}$, a real number for Hermitian $A$.
--   5. The expectation of a random matrix is taken entrywise, $(\mathbb E X)_{ij}=\mathbb E X_{ij}$, and a random matrix is called integrable when each of its entries is integrable.
--   6. Bennett's function is
--   $$h(u)=(1+u)\log(1+u)-u,\qquad u\ge 0 .$$
--
--   Every statement of the mission is written with these objects; $h$ appears in the matrix Bennett inequality, Theorem 6.1(i).
--
--   **Formalization Note** The matrix functions use Mathlib's continuous functional calculus `cfc`, which agrees with the spectral definition on Hermitian matrices. The semidefinite order $A\preccurlyeq B$ is Mathlib's `MatrixOrder` (that is, $B-A$ is positive semidefinite) and is not redefined. Integrability of the entries is the paper's standing §2.2 regularity ("all random variables are sufficiently regular") made explicit; each theorem states it exactly where an expectation is taken.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, pp. 7–9, §§2.1–2.4, display (2.1); p. 24, Theorem 6.1 (definition of h)

import Mathlib
import Definitions.Def_MatrixTail_Gaussian_Model
import Definitions.Def_MatrixTail_Master_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Bernstein

/-- Bennett's function `h(u) := (1 + u) log(1 + u) − u` for `u ≥ 0` (Theorem 6.1, p. 24). It is only ever
evaluated at `u ≥ 0`, where `Real.log (1 + u)` is the genuine logarithm. -/
noncomputable def bennettH (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) - u

end MatrixTail.Bernstein


