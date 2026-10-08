-- Prove2me | Definitions.Def_UnivESD_Universality_Basic
-- name    : UnivESD_Universality_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:10.554919+00:00
-- url     : https://prove2.me/theorems/38ee3615-d22c-4966-ac66-de069237bb3b
-- title:
--   The ESD $\mu_A$, the Hilbert–Schmidt norm, singular values, row distances, normalized log-determinants, $m_\mu$ and $g_\mu$
-- statement:
--   This file fixes the deterministic objects of Tao and Vu's universality paper.
--
--   1. **Empirical spectral distribution.** For an $n\times n$ complex matrix $A$ with eigenvalues $\lambda_1,\dots,\lambda_n$ (the roots of the characteristic polynomial, repeated according to algebraic multiplicity),
--   $$\mu_A=\frac1n\sum_{i=1}^n\delta_{\lambda_i},$$
--   a discrete probability measure on $\mathbb C$ whose distribution function is $\mu_A(s,t)=\frac1n\,|\{1\le i\le n:\ \mathrm{Re}\,\lambda_i\le s,\ \mathrm{Im}\,\lambda_i\le t\}|$.
--   2. **Normalization.** The scalar $1/\sqrt n$; the paper always studies $\mu_{\frac{1}{\sqrt n}A_n}$.
--   3. **Hilbert–Schmidt norm.** $\|A\|_2^2=\mathrm{trace}(AA^*)=\sum_{i,j}|a_{ij}|^2$.
--   4. **Singular values.** For an $m\times n$ complex matrix $A$, $\sigma_1(A)\ge\sigma_2(A)\ge\cdots\ge0$, indexed from $1$ as in the paper.
--   5. **Rows and distances.** The rows $X_1,\dots,X_m\in\mathbb C^n$ of $A$; $V_i=\mathrm{span}(X_1,\dots,X_{i-1})$; $W_j=\mathrm{span}(X_i: i\ne j)$; and $\mathrm{dist}(X_i,V_i)$ in the Euclidean norm.
--   6. **Normalized log-determinant.** $\frac1n\log\bigl|\det\bigl(\frac1{\sqrt n}A-zI\bigr)\bigr|$.
--   7. **Characteristic function and Stieltjes-like transform** of a measure $\mu$ on $\mathbb C$:
--   $$m_\mu(u,v)=\int_{\mathbb C}e^{iu\,\mathrm{Re}(z)+iv\,\mathrm{Im}(z)}\,d\mu(z),\qquad g_\mu(z)=2\,\mathrm{Re}\int_{\mathbb C}\frac{z-w}{|z-w|^2}\,d\mu(w).$$
--
--   These are the objects in which the replacement principle, Girko's identity and the linear-algebra lemmas of Appendix A are stated.
--
--   **Formalization Note.** Eigenvalues are the multiset of roots of the characteristic polynomial, so multiplicities are kept; for $n=0$ the ESD is the zero measure, which is harmless because every statement is asymptotic in $n$. Singular values are Mathlib's `LinearMap.singularValues` of $A$ acting $\mathbb C^n\to\mathbb C^m$, which is zero-based; `singVal A i` is the paper's $\sigma_i(A)$ for $i\ge1$ (for $m\le n$ the first $m$ values are the paper's $\sigma_1,\dots,\sigma_m$ and the rest vanish). In Lean $\log 0=0$ and $x/0=0$: at an atom $w=z$ the integrand of $g_\mu$ is $0$, which for an ESD changes $g$ only at finitely many points; statements that use the log-determinant or row distances say explicitly what happens when they vanish.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2024 (PDF 2) ESD; p. 2027 (PDF 5) Hilbert–Schmidt norm; p. 2035 (PDF 13) and p. 2044 (PDF 22) singular values and row distances; p. 2038–2039 (PDF 16–17) m and g, (3.6); p. 2059 (PDF 37) W_j

import Mathlib

open MeasureTheory

namespace UnivESD.Universality

/-- The empirical spectral distribution (ESD) of an `n × n` complex matrix,
`μ_A = (1/n) ∑_{i=1}^n δ_{λ_i}`, where `λ_1, …, λ_n` are the roots of the characteristic
polynomial counted with algebraic multiplicity (Tao–Vu, p. 2024). For `n = 0` it is the zero
measure; every statement using it is asymptotic in `n`. -/
noncomputable def esd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Measure ℂ :=
  ((n : ENNReal)⁻¹) • (A.charpoly.roots.map Measure.dirac).sum

/-- The normalizing scalar `1/√n`, as a complex number. -/
noncomputable def invSqrt (n : ℕ) : ℂ := ((Real.sqrt n : ℝ) : ℂ)⁻¹

/-- The squared Hilbert–Schmidt (Frobenius) norm `‖A‖₂² = ∑_{i,j} |a_ij|²` (p. 2027). -/
noncomputable def hsNormSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- The `i`-th singular value `σ_i(A)` of an `m × n` complex matrix, **one-based** as in the
paper (`σ_1(A) ≥ σ_2(A) ≥ ⋯ ≥ 0`): `singVal A i` is Mathlib's zero-based
`LinearMap.singularValues (i - 1)` of `A` acting `ℂⁿ → ℂᵐ`. Meaningful for `i ≥ 1`. -/
noncomputable def singVal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues (i - 1)

/-- The `i`-th row of a matrix, as a vector of the Euclidean space `ℂⁿ`. -/
def row {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (A i)

/-- `V_i`: the span of the rows strictly before row `i` (the paper's span of `X_1, …, X_{i-1}`). -/
noncomputable def prevSpan {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ (row A '' Set.Iio i)

/-- `W_j`: the span of all rows other than row `j`. -/
noncomputable def otherSpan {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (j : Fin m) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ (row A '' {i | i ≠ j})

/-- `dist(X_i, V_i)`: the Euclidean distance from row `i` to the span of the earlier rows. -/
noncomputable def rowDist {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) : ℝ :=
  Metric.infDist (row A i) (prevSpan A i : Set (EuclideanSpace ℂ (Fin n)))

/-- The normalized log-determinant `(1/n) log |det((1/√n) A - zI)|`. (`Real.log 0 = 0` in Lean;
every statement using it says what happens when the determinant vanishes.) -/
noncomputable def normLogDet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : ℝ :=
  (1 / (n : ℝ)) * Real.log ‖(invSqrt n • A - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖

/-- The characteristic function `m_μ(u, v) = ∫ e^{iu Re z + iv Im z} dμ(z)` of a measure on `ℂ`
(p. 2038). -/
noncomputable def charFn (μ : Measure ℂ) (u v : ℝ) : ℂ :=
  ∫ z, Complex.exp (Complex.I * ((u : ℂ) * z.re + (v : ℂ) * z.im)) ∂μ

/-- The Stieltjes-like transform `g_μ(z) = 2 Re ∫ (z - w)/|z - w|² dμ(w)` (p. 2039, (3.6)).
At an atom `w = z` the integrand is `0` in Lean (`x / 0 = 0`); for the ESD this affects
finitely many `z` only. -/
noncomputable def stieltjesG (μ : Measure ℂ) (z : ℂ) : ℝ :=
  2 * (∫ w, (z - w) / ((‖z - w‖ ^ 2 : ℝ) : ℂ) ∂μ).re

end UnivESD.Universality


