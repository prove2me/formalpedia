-- Prove2me | Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
-- name    : MomentPolytopes_QuantumFunctionals_Spectra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:01:50.370037+00:00
-- url     : https://prove2.me/theorems/6ad0f12c-b52c-4e56-97e9-5b13e8441b05
-- title:
--   Frobenius norm, sorted spectra, Shannon and von Neumann entropy, and the affine-invariant distance on positive-definite matrices
-- statement:
--   For a square complex matrix $A$, the **Frobenius norm** is $\|A\|_F=\big(\sum_{i,j}|A_{ij}|^2\big)^{1/2}$.
--
--   For a Hermitian $m\times m$ matrix $A$, $\operatorname{spec}A\in\mathbb R^m_{\downarrow}$ lists its eigenvalues with multiplicity in **nonincreasing** order, $\operatorname{spec}A_1\ge\operatorname{spec}A_2\ge\dots\ge\operatorname{spec}A_m$, where $\mathbb R^m_\downarrow=\{x\in\mathbb R^m\mid x_1\ge\dots\ge x_m\}$.
--
--   The **Shannon entropy** of a vector $p\in\mathbb R^m$ is $H(p)=-\sum_i p_i\log p_i$ with the natural logarithm and $0\log 0=0$. The **von Neumann entropy** of a positive-semidefinite matrix $X$ of any trace is
--   $$H(X)=-\operatorname{tr}[X\log X]=H(\operatorname{spec}X).$$
--
--   On positive-definite matrices, the **affine-invariant distance** is
--   $$d(x,y)=\big\|\log\big(x^{-1/2}\,y\,x^{-1/2}\big)\big\|_F ,$$
--   and for Hermitian $X$ and real $t$, $e^{tX}$ is the matrix exponential.
--
--   **Formalization Note** `spec` is built from Mathlib's antitone `eigenvalues₀`; on a non-Hermitian matrix it returns the junk value $0$, and it is only applied to Hermitian matrices. Matrix powers, logarithms and exponentials are the continuous functional calculus `cfc` of a Hermitian matrix (`Real.log 0 = 0`, so `cfc Real.log` is the logarithm on the support). The modes and eigenvalue positions are `Fin`-indexed (0-based).
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 13 (spec, ℝ^n_↓); §2.2, p. 14 (d(x, y), Frobenius norm); Example 3.8 (a), p. 19 and eq. (7.4), p. 54 (entropies)

import Mathlib

set_option autoImplicit false

namespace MomentPolytopes.QuantumFunctionals

/-- Frobenius (Hilbert–Schmidt) norm `‖A‖_F = (∑_{i,j} |A_{ij}|²)^{1/2}` of a square complex
matrix (Doğan–Sakabe–Walter, arXiv:2609.06633, §2.2, p. 14). -/
noncomputable def frobNorm {m : Type} [Fintype m] (A : Matrix m m ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2)

/-- `spec A`: the eigenvalues of a Hermitian `m × m` matrix listed in **nonincreasing** order,
`spec A 0 ≥ spec A 1 ≥ ⋯` (p. 13 and Example 2.1, p. 16: `spec : H → ℝ^{n_1}_↓ × ⋯`).
Built from Mathlib's `eigenvalues₀`, which is antitone. It is only applied to Hermitian
matrices; on a non-Hermitian matrix it returns the junk value `0`. -/
noncomputable def spec {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Fin m → ℝ :=
  if h : A.IsHermitian then fun i => h.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm i)
  else 0

/-- Shannon entropy `H(p) = -∑_i p_i log p_i` with natural logarithm and `0 log 0 = 0`
(eq. (7.4), p. 54). Defined for every real vector through `Real.negMulLog`. -/
noncomputable def shannonEntropy {m : ℕ} (p : Fin m → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- Von Neumann entropy `H(X) = -tr[X log X]` of a positive-semidefinite matrix of **any trace**
(p. 54; Example 3.8 (a), p. 19), computed as the Shannon entropy of its spectrum
(`0 log 0 = 0`). -/
noncomputable def vnEntropy {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  shannonEntropy (spec X)

/-- Affine-invariant Riemannian distance on positive-definite matrices,
`d(x, y) = ‖log(x^{-1/2} y x^{-1/2})‖_F` (§2.2, p. 14). Matrix powers and the logarithm are
the continuous functional calculus of a Hermitian matrix. -/
noncomputable def pdDist {m : Type} [Fintype m] [DecidableEq m] (x y : Matrix m m ℂ) : ℝ :=
  frobNorm (cfc Real.log
    (cfc (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) x * y * cfc (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) x))

/-- Matrix exponential `e^{tX}` of a Hermitian matrix `X`, through the functional calculus. -/
noncomputable def hermExp {m : Type} [Fintype m] [DecidableEq m] (t : ℝ) (X : Matrix m m ℂ) :
    Matrix m m ℂ :=
  cfc (fun s : ℝ => Real.exp (t * s)) X

end MomentPolytopes.QuantumFunctionals


