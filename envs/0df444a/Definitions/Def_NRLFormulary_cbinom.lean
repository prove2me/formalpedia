-- Prove2me | Definitions.Def_NRLFormulary_cbinom
-- name    : NRLFormulary_cbinom
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T17:43:30.83595+00:00
-- url     : https://prove2.me/theorems/00ad6eed-09fe-4638-906a-c4a8a2c4e42e
-- title:
--   Generalized binomial coefficient $\binom{w}{k}$ with complex upper index
-- statement:
--   For a complex number $w$ and a natural number $k$, the **generalized binomial coefficient** is
--
--   $$\binom{w}{k} \;=\; \frac{1}{k!}\prod_{j=0}^{k-1}(w-j) \;=\; \frac{w(w-1)\cdots(w-k+1)}{k!},$$
--
--   the falling factorial of length $k$ starting at $w$, divided by $k!$. The product over an empty range is $1$, so $\binom{w}{0} = 1$ for every $w$.
--
--   This is the coefficient appearing throughout the Rothe-Hagen identity, where the upper index $x + kz$ is an arbitrary complex number while the lower index stays a natural number. For a natural number $w$ it agrees with the ordinary binomial coefficient, and as a function of $w$ it is a polynomial of degree $k$; both facts make it the standard vehicle for binomial identities with complex parameters.
--
--   **Formalization Note.** The denominator is the factorial of $k$ coerced into $\mathbb{C}$, which is never zero, so no division-by-zero convention is involved.
-- source:
--   J. D. Huba, NRL Plasma Formulary, Naval Research Laboratory, 2013, p. 3, section "Numerical and Algebraic", the Rothe-Hagen identity ("good for all complex x, y, z except when singular"), footnote 2: H. W. Gould, "Note on Some Binomial Coefficient Identities of Rosenbaum", J. Math. Phys. 10, 49 (1969); H. W. Gould and J. Kaucky, "Evaluation of a Class of Binomial Coefficient Summations", J. Comb. Theory 1, 233 (1966). https://www.nrl.navy.mil/News-Media/Publications/NRL-Plasma-Formulary/

import Mathlib

namespace NRLFormulary

/-- The generalized binomial coefficient with a complex upper index:
`cbinom w k = w (w - 1) ⋯ (w - k + 1) / k!`. -/
noncomputable def cbinom (w : ℂ) (k : ℕ) : ℂ :=
  (∏ j ∈ Finset.range k, (w - (j : ℂ))) / (Nat.factorial k : ℂ)

end NRLFormulary


