-- Prove2me | Definitions.Def_ApproxDegComp_sqfreePoly
-- name    : ApproxDegComp_sqfreePoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:49.889336+00:00
-- url     : https://prove2.me/theorems/99c3efe3-7145-4b28-84e1-747ec10c8ac4
-- title:
--   Squarefree extraction $\mathcal S(P)$ of a polynomial
-- statement:
--   For a monomial $x_1^{a_1}\cdots x_n^{a_n}$ define $\mathcal S(x^a)=x^a$ if every $a_i\in\{0,1\}$ and $\mathcal S(x^a)=0$ otherwise, and extend linearly: for $P=\sum_j c_j m_j$ with distinct monomials $m_j$,
--
--   $$\mathcal S(P)=\sum_j c_j\,\mathcal S(m_j).$$
--
--   So $\mathcal S$ deletes every monomial in which some variable has exponent at least two. This differs from Boolean multilinearization, which would replace each positive exponent by one: for example $\mathcal S(x_1^2)=0$ while $\mathcal S(x_1x_2)=x_1x_2$.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Definition 19, p.14

import Mathlib

namespace ApproxDegComp

/-- **Squarefree extraction of a polynomial** `S(P)` (Definition 19, p.14).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 19, p.14: "For a monomial (x₁^{a₁} ⋯ xₙ^{aₙ}) … define S(x₁^{a₁} ⋯ xₙ^{aₙ}) =
(x₁^{a₁} ⋯ xₙ^{aₙ}) if aᵢ ∈ {0, 1} for every i ∈ [n], 0 otherwise. Then for a polynomial
P = Σⱼ cⱼmⱼ … define S(P) = Σⱼ cⱼ S(mⱼ)." The page adds: "it deletes every monomial in which
some variable has exponent at least two".

**Formalization Note** `S(P)` keeps exactly the monomials of `P` whose exponents are all at
most 1, with their coefficients, and drops the others. This is not Boolean multilinearization
(which would replace positive exponents by 1). -/
noncomputable def sqfreePoly {ι : Type} (P : MvPolynomial ι ℝ) : MvPolynomial ι ℝ := by
  classical
  exact ∑ s ∈ P.support.filter (fun s => ∀ i, s i ≤ 1), MvPolynomial.monomial s (P.coeff s)

end ApproxDegComp


