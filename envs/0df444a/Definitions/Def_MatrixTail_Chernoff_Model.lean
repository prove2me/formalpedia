-- Prove2me | Definitions.Def_MatrixTail_Chernoff_Model
-- name    : MatrixTail_Chernoff_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:10:28.954915+00:00
-- url     : https://prove2.me/theorems/f46674cc-a29a-42d9-aefb-2a2c90fabcb4
-- title:
--   §2 and Theorem 5.1 — complex Hermitian matrices, λmax/λmin, matrix exp/log, trace exponential, entrywise expectation, binary divergence D(a‖u)
-- statement:
--   This file fixes the objects in which the matrix Chernoff inequalities are stated. Throughout, a **matrix** is a $d\times d$ array of complex numbers (Tropp, §2.1), and a **random matrix** is a measurable map $X:\Omega\to\mathbb C^{d\times d}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$, where $\mathbb C^{d\times d}$ carries its Borel (product) $\sigma$-algebra.
--
--   1. For a self-adjoint (Hermitian) matrix $A$, $\lambda_{\max}(A)$ and $\lambda_{\min}(A)$ are the algebraically largest and smallest eigenvalues, i.e. the supremum and infimum of the real spectrum of $A$.
--   2. The **matrix exponential** $e^A$ and the **matrix logarithm** $\log A$ are defined by the spectral rule (2.1): if $A = Q\Lambda Q^*$ is an eigen-decomposition, then $f(A) = Q f(\Lambda) Q^*$ with $f=\exp$, resp. $f=\log$. The logarithm is used only on positive-definite matrices, where it inverts the exponential (2.7).
--   3. The **trace exponential** is $A\mapsto \operatorname{tr} e^{A}$, a real number for Hermitian $A$.
--   4. The **expectation** $\mathbb E X$ of a random matrix is taken entrywise, $(\mathbb E X)_{ij} = \mathbb E[X_{ij}]$; a random matrix is called integrable when all its entries are.
--   5. The **binary information divergence** is
--   $$\mathrm D(a\,\|\,u) := a\big(\log a-\log u\big) + (1-a)\big(\log(1-a)-\log(1-u)\big),\qquad a,u\in[0,1].$$
--
--   These are the shared vocabulary of every statement in the mission: the master tail bound, its corollary with a single logarithm, the Chernoff mgf bound and the two Chernoff inequalities.
--
--   **Formalization Note** $\lambda_{\max}$ and $\lambda_{\min}$ are `sSup`/`sInf` of `spectrum ℝ A`; for $d=0$ the spectrum is empty and both are $0$, so every theorem assumes $d\ge 1$. The exponential and logarithm are Mathlib's continuous functional calculus `cfc`. In Lean $\log 0 = 0$; the convention $0\log 0 = 0$ is reproduced, and where the true divergence is $+\infty$ (at $u\in\{0,1\}$, $a\neq u$) Lean's value is finite, which in Theorem 5.1 only makes the bound weaker.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, pp. 7–8, §§2.1–2.5, (2.1), (2.7); p. 20, Theorem 5.1 (binary information divergence)

import Mathlib
import Definitions.Def_MatrixTail_Master_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Chernoff

/-- `λmin(A)`, the algebraically smallest eigenvalue of a self-adjoint matrix (Tropp, arXiv:1004.4389v7,
§2.1, p. 7): the infimum of its real spectrum. -/
noncomputable def lambdaMin {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := sInf (spectrum ℝ A)

/-- The binary information divergence
`D(a ‖ u) := a(log a − log u) + (1 − a)(log(1 − a) − log(1 − u))` for `a, u ∈ [0, 1]`
(Tropp, arXiv:1004.4389v7, Theorem 5.1, p. 20).

Formalization Note: Lean's `Real.log 0 = 0`. The convention `0 · log 0 = 0` is reproduced because
`0 * _ = 0`. Where the true divergence is `+∞` (`u ∈ {0, 1}` with `a ≠ u`), Lean's value is finite; in
every use in Theorem 5.1 this only makes the bound `d · e^{−n D}` larger (weaker), never stronger. -/
noncomputable def binDiv (a u : ℝ) : ℝ :=
  a * (Real.log a - Real.log u) + (1 - a) * (Real.log (1 - a) - Real.log (1 - u))

end MatrixTail.Chernoff


