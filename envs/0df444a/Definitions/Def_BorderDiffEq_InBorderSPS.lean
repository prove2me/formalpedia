-- Prove2me | Definitions.Def_BorderDiffEq_InBorderSPS
-- name    : BorderDiffEq_InBorderSPS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:34.096616+00:00
-- url     : https://prove2.me/theorems/44961232-7ec4-4a27-91fd-74aca3da7c7e
-- title:
--   The border $\overline{\Sigma^{[k]}\Pi\Sigma(s)}$ of size-$s$ depth-3 circuits
-- statement:
--   Let $F$ be a field and $f\in F[x_1,\dots,x_n]$. Then $f\in\overline{\Sigma^{[k]}\Pi\Sigma(s)}$, the **border** of depth-3 circuits of top fan-in $k$ and size $s$, if there is a depth-3 circuit $\Phi$ whose constants lie in $F((\varepsilon))$, with top fan-in at most $k$ and size at most $s$, such that
--   $$
--   \Phi=f+\varepsilon\,S\qquad\text{for some polynomial } S\in F[[\varepsilon]][x].
--   $$
--   In words: $f$ is the limit as $\varepsilon\to0$ of polynomials computed by small depth-3 circuits.
--
--   **Formalization Note** Variables are `Fin n`. Constants in $F((\varepsilon))$ and $S\in F[[\varepsilon]][x]$ contain the paper's constants in $F(\varepsilon)$ and $g\in F[\varepsilon][x]$. "Top fan-in $k$" is read as "at most $k$". The size is the factor-counting size of `SPS`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §2.1, p.7 (definition of the border); §4, p.23

import Mathlib
import Definitions.Def_BorderDiffEq_SPS
import Definitions.Def_BorderDiffEq_IsEpsApprox

namespace BorderDiffEq

/-- **The border of size-`s` depth-3 circuits of top fan-in `k`, `f ∈ cl(Σ^{[k]}ΠΣ(s))`**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), §2.1, p.7, and §4, p.23): a polynomial
`f ∈ F[x₁, …, xₙ]` is in the border if some ΣΠΣ circuit with at most `k` product gates and size at
most `s`, whose constants are in `F((ε))`, computes `f + ε·S` for a polynomial `S` with coefficients
in `F[[ε]]`.

**Formalization Note.** Variables are `Fin n`. Constants in `F((ε))` (Mathlib `LaurentSeries F`)
and `S ∈ F[[ε]][x]` cover the paper's constants in `F(ε)` and `g ∈ F[ε][x]`. The circuit size is
`SPS.size` (factors counted with multiplicity, so the size bounds the formal degree). "Top fan-in
`k`" is read as "at most `k`". -/
def InBorderSPS (F : Type) [Field F] (n k s : ℕ) (f : MvPolynomial (Fin n) F) : Prop :=
  ∃ Φ : SPS (LaurentSeries F) (Fin n), Φ.topFanIn ≤ k ∧ Φ.size ≤ s ∧ IsEpsApprox Φ.eval f

end BorderDiffEq


