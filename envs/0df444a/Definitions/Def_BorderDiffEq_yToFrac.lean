-- Prove2me | Definitions.Def_BorderDiffEq_yToFrac
-- name    : BorderDiffEq_yToFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:17.920202+00:00
-- url     : https://prove2.me/theorems/113b1644-22be-4d61-8403-ddc7bd870c9a
-- title:
--   Moving $y$ into the coefficient field: $K[y,x]\to K(y)[x]$
-- statement:
--   Let $K$ be a field and $K(y)$ the field of rational functions in $y=(y_1,\dots,y_n)$. The $K$-algebra map
--   $$
--   K[y,x]\longrightarrow K(y)[x],\qquad y_l\mapsto y_l\in K(y),\quad x_l\mapsto x_l,
--   $$
--   views a polynomial in $(y,x)$ as a polynomial in $x$ with coefficients in $K(y)$. Applied coefficientwise in $z$ it views a polynomial in $(y,z,x)$ as an element of $K(y)[x][z]$, the ring in which Lemma 5.3 and Proposition 5.4 state their results ("a polynomial in $F(y)[x,z]$", "$b_j\in F(y)[z,x]$").
--
--   **Formalization Note** $y_l$ = `X (Sum.inl l)`, $x_l$ = `X (Sum.inr l)`; $K(y)$ is `FractionRing (MvPolynomial σ K)`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 5.3, p.32; Proposition 5.4, p.34

import Mathlib

namespace BorderDiffEq

/-- **Moving `y` into the coefficient field `F(y)`** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), Lemma 5.3, p.32 ("a polynomial in `F(y)[x, z]`"), and Proposition 5.4, p.34
("`b₀, …, b_r ∈ F(y)[z, x]`")): the `K`-algebra map
`K[y, x] → F(y)[x]`, `yₗ ↦ yₗ ∈ K(y)`, `xₗ ↦ xₗ`, where `K(y)` is the field of rational functions
in `y`.

**Formalization Note.** `yₗ = X (Sum.inl l)`, `xₗ = X (Sum.inr l)`; `K(y)` is
`FractionRing (MvPolynomial σ K)`. Applied coefficientwise (`Polynomial.map`) it views a polynomial
in `(y, z, x)` as a polynomial in `(z, x)` over `K(y)`. -/
noncomputable def yToFrac {K : Type} [Field K] {σ : Type} :
    MvPolynomial (σ ⊕ σ) K →ₐ[K] MvPolynomial σ (FractionRing (MvPolynomial σ K)) :=
  MvPolynomial.aeval
    (Sum.elim
      (fun l => MvPolynomial.C (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        (MvPolynomial.X l)))
      MvPolynomial.X)

end BorderDiffEq


