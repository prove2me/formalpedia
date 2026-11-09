-- Prove2me | Definitions.Def_KSPolySign_bernsteinCoeff
-- name    : KSPolySign_bernsteinCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:32:57.403647+00:00
-- url     : https://prove2.me/theorems/bda5636b-4db2-4f82-a9bf-1f982f55d1fc
-- title:
--   Tensor-product Bernstein coefficients on a box
-- statement:
--   Let $P$ be a polynomial in $x_1,\dots,x_d$, let $\prod_j[a_j,b_j]$ be a box, and let $n_1,\dots,n_d$ be degree bounds. Substitute $x_j=a_j+(b_j-a_j)u_j$ and write $P(x)=\sum_\nu A_\nu u^\nu$. For a multi-index $\mu$ with $0\le\mu_j\le n_j$, the **Bernstein coefficient** is
--   $$B_\mu = \sum_{\nu\le\mu} A_\nu \prod_{j=1}^d \frac{\binom{\mu_j}{\nu_j}}{\binom{n_j}{\nu_j}}.$$
--   Lemma A.1 shows that these finitely many numbers enclose the range of $P$ on the box.
--
--   **Formalization Note** Real coefficients (the paper uses rational ones). The sum runs over the monomials of the substituted polynomial with $\nu_j\le\mu_j$ for all $j$; all other $A_\nu$ vanish.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma A.1, p.71 (PDF p.71)

import Mathlib
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Tensor-product Bernstein coefficients on a box.** For a polynomial `P` in `x_1, …, x_d`, a box
`∏_j [a_j, b_j]` and degree bounds `n_j`, substitute `x_j = a_j + (b_j − a_j)u_j`, write the result as
`∑_ν A_ν u^ν`, and set
`B_μ = ∑_{ν ≤ μ} A_ν ∏_j C(μ_j, ν_j)/C(n_j, ν_j)`.
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma A.1, p.71 (PDF p.71).

**Formalization Note** `P` is an `MvPolynomial` with real coefficients (the paper's are rational);
the substituted polynomial is `bind₁` of the affine substitution, and `A_ν` is its coefficient. The
sum over `ν ≤ μ` runs over the monomials of the substituted polynomial with `ν_j ≤ μ_j` for every `j`
(the other `A_ν` are `0`). -/
noncomputable def bernsteinCoeff {d : ℕ} (P : MvPolynomial (Fin d) ℝ) (a b : Fin d → ℝ) (N : Fin d → ℕ)
    (μ : Fin d → ℕ) : ℝ :=
  let Q : MvPolynomial (Fin d) ℝ :=
    MvPolynomial.bind₁ (fun j => MvPolynomial.C (a j) + MvPolynomial.C (b j - a j) * MvPolynomial.X j) P
  ∑ ν ∈ Q.support.filter (fun ν => ∀ j, ν j ≤ μ j),
    Q.coeff ν * ∏ j, ((μ j).choose (ν j) : ℝ) / ((N j).choose (ν j) : ℝ)

end KSPolySign


