-- Prove2me | Definitions.Def_BorderDiffEq_epsVal
-- name    : BorderDiffEq_epsVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:18.957977+00:00
-- url     : https://prove2.me/theorems/69211230-0632-4140-9ece-e4960b230014
-- title:
--   The $\varepsilon$-valuation $\mathrm{val}_\varepsilon$ of a polynomial over $F((\varepsilon))$
-- statement:
--   For $A=\sum_j a_j\varepsilon^j\in F((\varepsilon))$ nonzero, $\mathrm{val}_\varepsilon(A)=\min\{j : a_j\neq0\}$, and $\mathrm{val}_\varepsilon(0)=\infty$. For a polynomial $P$ in variables $(y,z,x)$ with coefficients in $F((\varepsilon))$,
--   $$
--   \mathrm{val}_\varepsilon(P)=\min_{\text{coefficients } c \text{ of } P}\mathrm{val}_\varepsilon(c),
--   $$
--   the least power of $\varepsilon$ occurring in $P$; $\mathrm{val}_\varepsilon(P)=\infty$ exactly when $P=0$. This is how the paper uses $\mathrm{val}_\varepsilon$ for polynomials in Lemmas 4.4, 4.5 and 5.1.
--
--   **Formalization Note** $P$ is a polynomial in $z$ over `MvPolynomial ι (LaurentSeries F)`; the value is the minimum of `HahnSeries.orderTop` over all coefficients, in `WithTop ℤ`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §4, p.23, Notation

import Mathlib

namespace BorderDiffEq

/-- **The `ε`-valuation `val_ε` of a polynomial over `F((ε))`** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), §4, p.23, "Notation"; used for polynomials in Lemmas 4.4, 4.5, 5.1): for a
polynomial `P` in `(y, z, x)` with coefficients in `F((ε))`, `val_ε(P)` is the least exponent of
`ε` occurring in any of its coefficients, and `val_ε(0) = ∞`.

**Formalization Note.** `P` is a univariate polynomial in `z` over `MvPolynomial ι (LaurentSeries F)`
(as in `shift`). The value is the minimum of `HahnSeries.orderTop` over all coefficients, in
`WithTop ℤ`, with `⊤` exactly for `P = 0`. -/
noncomputable def epsVal {F : Type} [Field F] {ι : Type}
    (P : Polynomial (MvPolynomial ι (LaurentSeries F))) : WithTop ℤ :=
  P.support.inf fun i => (P.coeff i).support.inf fun μ => ((P.coeff i).coeff μ).orderTop

end BorderDiffEq


