-- Prove2me | Definitions.Def_KUMultimodular_densePoly
-- name    : KUMultimodular_densePoly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:57:07.345121+00:00
-- url     : https://prove2.me/theorems/17a6bb85-2b54-423c-a549-208eea8a9e5e
-- title:
--   Dense multivariate polynomials from coefficient tables
-- statement:
--   Let $R$ be a commutative ring and $m, d \in \mathbb N$. A polynomial $f \in R[X_0,\dots,X_{m-1}]$ with degree at most $d-1$ in each variable is given by its table of coefficients $c(a) \in R$, one for each exponent vector $a = (a_0,\dots,a_{m-1}) \in \{0,\dots,d-1\}^m$:
--   $$f = \sum_{a \in \{0,\dots,d-1\}^m} c(a)\, X_0^{a_0} X_1^{a_1} \cdots X_{m-1}^{a_{m-1}}.$$
--   The exponent vectors are listed in lexicographic order, the exponent of $X_0$ most significant; this is the order in which a dense coefficient list stores them.
--
--   Kedlaya and Umans always represent polynomials explicitly by the list of their coefficients; Problem 2.1 (multivariate multipoint evaluation) takes such an $f$ and points $\alpha_0,\dots,\alpha_{N-1} \in R^m$ and asks for the values $f(\alpha_i)$.
--
--   **Formalization Note** `densePoly c : MvPolynomial (Fin m) R` for `c : (Fin m → Fin d) → R`; `lexEnum d m` lists `Fin m → Fin d` in lexicographic order.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), §2.1 Problem 2.1, p. 7, and §2.2, p. 8 (dense coefficient representation)

import Mathlib

namespace KUMultimodular

/-- **Dense polynomial from its coefficient table** (Kedlaya–Umans, Dagstuhl Seminar Proceedings
08381 (2008), §2.1 Problem 2.1, p. 7, and §2.2, p. 8: "polynomials are always represented
explicitly by a list of their coefficients"). An `m`-variate polynomial with degree at most `d - 1`
in each variable is given by its table of coefficients `c a`, one for every exponent vector
`a ∈ {0, …, d-1}^m`; `densePoly c = Σ_a c a · X_0^{a_0} ⋯ X_{m-1}^{a_{m-1}}`. -/
noncomputable def densePoly {R : Type*} [CommSemiring R] {m d : ℕ} (c : (Fin m → Fin d) → R) :
    MvPolynomial (Fin m) R :=
  ∑ a, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun j => (a j : ℕ))) (c a)

/-- The exponent vectors `{0, …, d-1}^m` in lexicographic order, the exponent of `X_0` most
significant: the order in which a dense coefficient list stores the coefficients. -/
def lexEnum (d : ℕ) : (m : ℕ) → List (Fin m → Fin d)
  | 0 => [Fin.elim0]
  | m + 1 => (List.finRange d).flatMap (fun i => (lexEnum d m).map (Fin.cons i))

end KUMultimodular


