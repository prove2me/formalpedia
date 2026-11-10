-- Prove2me | Definitions.Def_BorderDiffEq_IsEpsApprox
-- name    : BorderDiffEq_IsEpsApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:34.468584+00:00
-- url     : https://prove2.me/theorems/c53df573-5251-46db-9026-b626b6156899
-- title:
--   $g=f+O(\varepsilon)$: $g=f+\varepsilon S$ with $S\in F[[\varepsilon]][x]$
-- statement:
--   Let $F$ be a field, $g$ a polynomial with coefficients in $F((\varepsilon))$ and $f$ a polynomial with coefficients in $F$, in the same variables. We say $g=f+O(\varepsilon)$ if
--   $$
--   g=f+\varepsilon\,S\qquad\text{for some polynomial } S \text{ with coefficients in } F[[\varepsilon]] .
--   $$
--   Equivalently, every coefficient of $g$ has no negative powers of $\varepsilon$, and setting $\varepsilon=0$ in $g$ gives $f$.
--
--   This is the paper's border condition "$f+\varepsilon g$ with $g\in F[\varepsilon][x]$" (p.23) and its "$f_\varepsilon=f+O(\varepsilon)$" (Lemma 5.1, Proposition 5.4).
--
--   **Formalization Note** Requiring $S\in F[[\varepsilon]][x]$, not $S\in F((\varepsilon))[x]$, is essential: otherwise every $g$ would qualify. Since $F[\varepsilon]\subset F[[\varepsilon]]$, the paper's condition is a special case.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §4, p.23 (border); Lemma 5.1, p.31 and Proposition 5.4, p.34 (f + O(ε))

import Mathlib
import Definitions.Def_BorderDiffEq_eps

namespace BorderDiffEq

/-- **`g = f + O(ε)`, i.e. `g = f + ε·S` with `S` having no negative powers of `ε`**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), §4, p.23 ("f + εg … g ∈ F[ε][x]"),
Lemma 5.1, p.31, and Proposition 5.4, p.34 ("f_ε = f + O(ε)")): a polynomial `g` over `F((ε))`
equals `f + ε·S` where `f` is a polynomial over `F` and `S` is a polynomial whose coefficients are
formal power series in `ε`.

**Formalization Note.** `f` is mapped into `F((ε))[x]` by the inclusion `F → F((ε))` and `S` by the
inclusion `F[[ε]] → F((ε))`. Requiring `S ∈ F[[ε]][x]` (and not `S ∈ F((ε))[x]`) is essential:
otherwise every `g` would qualify. This covers the paper's `g ∈ F[ε][x]` (since
`F[ε] ⊂ F[[ε]]`) and its `f + O(ε)`. -/
def IsEpsApprox {F : Type} [Field F] {σ : Type}
    (g : MvPolynomial σ (LaurentSeries F)) (f : MvPolynomial σ F) : Prop :=
  ∃ S : MvPolynomial σ (PowerSeries F),
    g = MvPolynomial.map (algebraMap F (LaurentSeries F)) f +
      MvPolynomial.C (eps F) * MvPolynomial.map (algebraMap (PowerSeries F) (LaurentSeries F)) S

end BorderDiffEq


