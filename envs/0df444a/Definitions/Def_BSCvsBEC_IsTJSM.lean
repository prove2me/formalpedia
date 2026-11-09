-- Prove2me | Definitions.Def_BSCvsBEC_IsTJSM
-- name    : BSCvsBEC_IsTJSM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:36.60676+00:00
-- url     : https://prove2.me/theorems/a42f4aeb-468e-4e3f-b6d0-32f7b9de9a35
-- title:
--   Heinävaara's transform $H(f)$ and tracial joint spectral measures
-- statement:
--   For a function $f:\mathbb R\to\mathbb R$, **Heinävaara's transform** is
--   $$H(f)(x):=\int_0^1\frac{1-t}{t}\,f(xt)\,dt.$$
--   A test function is **admissible** if it is measurable, $f(0)=0$, and $\int_{-M}^{M}|f(t)/t|\,dt<\infty$ for every $M>0$.
--
--   Given Hermitian matrices $A,B\in\mathbb C^{n\times n}$, a (positive) measure $\mu$ on $\mathbb R^2$ is a **tracial joint spectral measure** for $(A,B)$ if for every admissible $f$ and all $x,y\in\mathbb R$, the function $(a,b)\mapsto f(xa+yb)$ is $\mu$-integrable and
--   $$\operatorname{Tr}H(f)(xA+yB)=\int_{\mathbb R^2}f(xa+yb)\,d\mu(a,b).$$
--   Here $H(f)(xA+yB)$ is the function $H(f)$ applied to the Hermitian matrix $xA+yB$ by the functional calculus.
--
--   Heinävaara's theorem (Theorem 2.12 of the paper) asserts that such a measure exists for every Hermitian pair; the paper uses it to lift scalar two-point inequalities to matrix-valued functions.
--
--   **Formalization Note** The trace of a Hermitian matrix is real, and its real part is compared. Equation (58) is read as integrability together with equality, because Lean's integral of a non-integrable function is $0$. The finiteness $\int_{-M}^M|f(t)/t|\,dt<\infty$ is integrability of $t\mapsto f(t)/t$ on $[-M,M]$.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 2.12, eqs. (57)–(58), pp.11–12

import Mathlib

namespace BSCvsBEC

open MeasureTheory

/-- Heinävaara's transform `H(f)(x) := ∫₀¹ ((1 − t)/t) f(xt) dt`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), Theorem 2.12, eq. (57), p.12. -/
noncomputable def heinH (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) / t * f (x * t)

/-- The test functions of Theorem 2.12 (p.12): "a measurable `f` on `ℝ` with `f(0) = 0` which
satisfies `∫_{−M}^{M} |f(t)/t| dt < ∞` for every `M > 0`".

**Formalization Note.** Finiteness of `∫_{−M}^{M} |f(t)/t| dt` is integrability of `t ↦ f(t)/t` on
`[−M, M]` (Lean's `f 0 / 0 = 0` changes the integrand on a null set only). -/
def IsAdmissible (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ f 0 = 0 ∧ ∀ M : ℝ, 0 < M → IntegrableOn (fun t => f t / t) (Set.Icc (-M) M)

/-- A tracial joint spectral measure of the Hermitian pair `(A, B)`: a (positive) measure `μ` on `ℝ²`
such that for every admissible `f` and all `x, y ∈ ℝ`,
`Tr H(f)(xA + yB) = ∫_{ℝ²} f(xa + yb) dμ(a, b)` (eq. (58)).
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), Theorem 2.12, pp.11–12.

**Formalization Note.** `H(f)(xA + yB)` is the Hermitian functional calculus `cfc (heinH f)`, and its
trace is real, so its real part is compared. Equation (58) is read as: the integrand is
`μ`-integrable **and** the integral equals the trace (Lean's integral of a non-integrable function is
`0`). -/
def IsTJSM {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (μ : Measure (ℝ × ℝ)) :
    Prop :=
  ∀ f : ℝ → ℝ, IsAdmissible f → ∀ x y : ℝ,
    Integrable (fun p : ℝ × ℝ => f (x * p.1 + y * p.2)) μ ∧
      (Matrix.trace (cfc (heinH f) (x • A + y • B))).re = ∫ p, f (x * p.1 + y * p.2) ∂μ

end BSCvsBEC


