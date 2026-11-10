-- Prove2me | Definitions.Def_BorderDiffEq_epsCoeff
-- name    : BorderDiffEq_epsCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:23.177735+00:00
-- url     : https://prove2.me/theorems/a2780763-3ea7-423c-b611-e12215954c8d
-- title:
--   The $\varepsilon^m$-coefficient $\lim_{\varepsilon\to0}\varepsilon^{-m}P$
-- statement:
--   For a polynomial $P$ in $(y,z,x)$ with coefficients in $F((\varepsilon))$ and $m\in\mathbb Z$, $\mathrm{coeff}_{\varepsilon^m}(P)$ is the polynomial over $F$ obtained by replacing every coefficient of $P$ by its $\varepsilon^m$-coefficient. When $\mathrm{val}_\varepsilon(P)\ge m$, the paper writes
--   $$
--   \lim_{\varepsilon\to0}\varepsilon^{-m}P:=\mathrm{coeff}_{\varepsilon^m}(P).
--   $$
--   With $m=\mathrm{val}_\varepsilon(P)$ this is the lowest $\varepsilon$-part of $P$; it is how the coefficients $b_j$ of the limiting differential equation are obtained (Lemma 5.1).
--
--   **Formalization Note** The input is a polynomial in $z$ over `MvPolynomial ι (LaurentSeries F)`, the output a polynomial in $z$ over `MvPolynomial ι F`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §4, p.23, Notation

import Mathlib

namespace BorderDiffEq

/-- **The `ε^m`-coefficient `coeff_{ε^m}(P)` of a polynomial over `F((ε))`**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), §4, p.23, "Notation": "If
`val_ε(A) ≥ m`, we write `lim_{ε→0} ε^{-m} A := coeff_{ε^m}(A)`"): the polynomial over `F` obtained
by taking the coefficient of `ε^m` in every coefficient of `P`.

**Formalization Note.** `P` is a polynomial in `z` over `MvPolynomial ι (LaurentSeries F)`; the
result is a polynomial in `z` over `MvPolynomial ι F`. It equals `lim_{ε→0} ε^{-m} P` whenever
`epsVal P ≥ m`. -/
noncomputable def epsCoeff {F : Type} [Field F] {ι : Type} (m : ℤ)
    (P : Polynomial (MvPolynomial ι (LaurentSeries F))) : Polynomial (MvPolynomial ι F) :=
  ∑ i ∈ P.support, Polynomial.monomial i
    (∑ μ ∈ (P.coeff i).support, MvPolynomial.monomial μ (((P.coeff i).coeff μ).coeff m))

end BorderDiffEq


