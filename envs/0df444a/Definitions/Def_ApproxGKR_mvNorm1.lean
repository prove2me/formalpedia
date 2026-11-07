-- Prove2me | Definitions.Def_ApproxGKR_mvNorm1
-- name    : ApproxGKR_mvNorm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:00.766278+00:00
-- url     : https://prove2.me/theorems/b24d7c86-1d86-4b60-bf35-db7715809ea6
-- title:
--   Coefficient norm $\|f\|_1$ of a complex polynomial
-- statement:
--   For a complex polynomial $f$ in any number of variables, the **coefficient norm** $\|f\|_1$ is the sum of the moduli of its coefficients:
--   $$\|f\|_1=\sum_{s}|[x^s]f|.$$
--   The same quantity is defined for univariate polynomials. The coefficient norm bounds $|f(z)|$ at every point whose coordinates have modulus at most one, which is how the protocol controls the magnitudes of all quantities on the unit torus. The paper assumes $\|\widetilde{\mathrm{add}}_i\|_1,\|\widetilde{\mathrm{mult}}_i\|_1\le B_W$.
--
--   **Formalization Note** The sum runs over the support of the polynomial (the monomials with nonzero coefficient).
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §2.1, p.5; §C.1, p.32

import Mathlib

namespace ApproxGKR

/-- The coefficient norm `‖f‖₁` of a multivariate complex polynomial: the sum of the moduli of
its coefficients.

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §2.1, p.5: "For any polynomial `f` over `C`, `∥f∥₁` is the sum of the moduli
of its coefficients"; §C.1, p.32.

**Formalization Note** The sum runs over `MvPolynomial.support`, i.e. over the monomials with a
nonzero coefficient; the zero coefficients contribute nothing either way. -/
noncomputable def mvNorm1 {σ : Type*} (f : MvPolynomial σ ℂ) : ℝ :=
  ∑ s ∈ f.support, ‖f.coeff s‖

/-- The coefficient norm `‖f‖₁` of a univariate complex polynomial (§2.1, p.5), the sum of the
moduli of its coefficients over `Polynomial.support`. -/
noncomputable def polyNorm1 (f : Polynomial ℂ) : ℝ :=
  ∑ n ∈ f.support, ‖f.coeff n‖

end ApproxGKR


