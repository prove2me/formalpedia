-- Prove2me | Definitions.Def_LCAntiConc_IsStrengthenedAC
-- name    : LCAntiConc_IsStrengthenedAC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:37.582631+00:00
-- url     : https://prove2.me/theorems/4ca747fb-1c3a-4d7d-9a5c-2be65c2447eb
-- title:
--   Definition 4.1 — $\delta$-strengthened anti-concentration at degree $m$
-- statement:
--   Let $\delta>0$, $m\in\mathbb N$ and $A$ a constant, and let $G\sim N(0,1)$ be independent of the random vector $X\in\mathbb R^d$. $X$ is **$\delta$-strengthened anti-concentrated at degree $m$**, witnessed by a polynomial $q$ of degree at most $m$, if for all $c\in\mathbb R^d$ with $\|c\|\le1$:
--
--   1. $q\ge0$ and $q(t)\ge1$ for $|t|\le\delta$;
--   2. $\displaystyle\mathop{\mathbb E}_{X,G}\,q\big(\langle c,X\rangle+\sqrt{1-\|c\|^2}\,G\big)\le A\,\delta$;
--   3. for $r\in\{1,2\}$ and all $\rho\in[0,1]$ there is a degree-$2m$ sum-of-squares proof
--
--   $$\{\|v\|^2=1\}\vdash_{2m}\ \mathop{\mathbb E}_{X,G}\,q^{(r)}\Big(\langle X,c\rangle+\rho\langle X,v-c\rangle+\sqrt{1-\rho^2}\sqrt{1-\|c\|^2}\,G\Big)^2\le A\,\delta^{-2r}.$$
--
--   The first two properties say that $q$ captures the indicator of $[-\delta,\delta]$ along one-dimensional marginals smoothed by Gaussian noise; the third bounds the derivatives of $q$ along the interpolation path used in the proof of Theorem 4.2.
--
--   **Formalization Note** The page calls the centre $\mu$; it is renamed $c$ here. The page's $O(\delta)$ and $O(\delta^{-2r})$ are the one constant $A$. "Degree-$m$ polynomial" is read as $\deg q\le m$. In item 3 the argument is a polynomial in $v$ with coefficients depending on $(X,G)$, and the expectation is the coefficientwise expectation polynomial, taken inside the sum-of-squares statement. Items 2 and 3 require the expectations to exist (integrability). $(X,G)$ has law $\mu\otimes N(0,1)$.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Definition 4.1, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_LCAntiConc_SphereSoSLe
import Definitions.Def_LCAntiConc_polyExpect
import Definitions.Def_LCAntiConc_PolyIntegrable
import Definitions.Def_LCAntiConc_linForm

namespace LCAntiConc

open MeasureTheory ProbabilityTheory

/-- **Definition 4.1** (strengthened anti-concentration), with its `O(δ)` and `O(δ^{-2r})` as one
explicit constant `A`, for the polynomial `q`: a random vector `X ∈ ℝ^d` (law `μ`) is
`δ`-strengthened anti-concentrated at degree `m`, witnessed by `q` of degree at most `m`, if for
all `c ∈ ℝ^d` with `‖c‖ ≤ 1`, and with `G ∼ N(0, 1)` independent of `X`:
1. `q ≥ 0` and `q(t) ≥ 1` for `|t| ≤ δ`;
2. `𝔼_{X,G} q(⟨c, X⟩ + √(1 - ‖c‖²) G) ≤ A δ`;
3. for `r ∈ {1, 2}` and all `ρ ∈ [0, 1]`, there is a degree-`2m` sum-of-squares proof
   `{‖v‖² = 1} ⊢ 𝔼_{X,G} q^{(r)}(⟨X, c⟩ + ρ⟨X, v - c⟩ + √(1-ρ²)√(1-‖c‖²) G)² ≤ A δ^{-2r}`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Definition 4.1, p.17 (PDF p.19).

**Formalization Note** The page's centre `μ` is renamed `c` (the law is `μ`). The pair `(X, G)`
has law `μ ⊗ N(0, 1)`. "Degree-`m` polynomial" is read as `deg q ≤ m`. In item 3 the argument is
a polynomial in the formal variable `v` whose coefficients depend on `(x, g)`, and the expectation
is the coefficientwise expectation polynomial (`polyExpect`), inside the sum-of-squares statement.
Item 2 and item 3 require the expectations to exist (integrability). -/
def IsStrengthenedAC {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (δ : ℝ) (m : ℕ) (A : ℝ)
    (q : Polynomial ℝ) : Prop :=
  q.natDegree ≤ m ∧ (∀ t, 0 ≤ q.eval t) ∧ (∀ t, |t| ≤ δ → 1 ≤ q.eval t) ∧
  (∀ c : EuclideanSpace ℝ (Fin d), ‖c‖ ≤ 1 →
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
      q.eval (inner ℝ c p.1 + Real.sqrt (1 - ‖c‖ ^ 2) * p.2)) (μ.prod (gaussianReal 0 1)) ∧
    ∫ p : EuclideanSpace ℝ (Fin d) × ℝ,
      q.eval (inner ℝ c p.1 + Real.sqrt (1 - ‖c‖ ^ 2) * p.2) ∂(μ.prod (gaussianReal 0 1))
        ≤ A * δ) ∧
  ∀ c : EuclideanSpace ℝ (Fin d), ‖c‖ ≤ 1 → ∀ r : ℕ, (r = 1 ∨ r = 2) →
    ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
      PolyIntegrable (μ.prod (gaussianReal 0 1)) (fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
        (Polynomial.aeval (MvPolynomial.C (inner ℝ p.1 c) +
            MvPolynomial.C ρ * (linForm p.1 - MvPolynomial.C (inner ℝ p.1 c)) +
            MvPolynomial.C (Real.sqrt (1 - ρ ^ 2) * Real.sqrt (1 - ‖c‖ ^ 2) * p.2))
          ((⇑Polynomial.derivative)^[r] q)) ^ 2) ∧
      SphereSoSLe (2 * m)
        (polyExpect (μ.prod (gaussianReal 0 1)) (fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
          (Polynomial.aeval (MvPolynomial.C (inner ℝ p.1 c) +
              MvPolynomial.C ρ * (linForm p.1 - MvPolynomial.C (inner ℝ p.1 c)) +
              MvPolynomial.C (Real.sqrt (1 - ρ ^ 2) * Real.sqrt (1 - ‖c‖ ^ 2) * p.2))
            ((⇑Polynomial.derivative)^[r] q)) ^ 2))
        (A * δ ^ (-(2 * (r : ℤ))))

end LCAntiConc


