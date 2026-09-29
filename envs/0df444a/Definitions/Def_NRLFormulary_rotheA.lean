-- Prove2me | Definitions.Def_NRLFormulary_rotheA
-- name    : NRLFormulary_rotheA
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T17:44:16.588901+00:00
-- url     : https://prove2.me/theorems/5ab1a7e1-e7a7-4c47-a58e-2534c70915cf
-- title:
--   Rothe factor $A_k(x,z)$ in singularity-free (polynomial) form
-- statement:
--   For complex numbers $x, z$ and a natural number $k$, the **Rothe factor** is
--
--   $$A_k(x,z) \;=\; \frac{x}{x+kz}\binom{x+kz}{k},$$
--
--   the quantity summed in the Rothe-Hagen identity. The denominator $x+kz$ cancels against the first factor of the falling factorial, so $A_k$ is in fact a polynomial in $x$ and $z$, and this definition records that polynomial form:
--
--   $$A_0(x,z) = 1, \qquad A_k(x,z) = \frac{x\,(x+kz-1)(x+kz-2)\cdots(x+kz-k+1)}{k!} \quad (k \ge 1).$$
--
--   Working with the polynomial form removes the exceptional locus $x + kz = 0$ on which the quotient form is undefined, which is what allows the Rothe-Hagen identity to be stated without side conditions. The two forms agree wherever $x+kz \ne 0$.
--
--   **Formalization Note.** The function is defined by cases on the lower index, with the value $1$ at $0$; for a successor index $k+1$ the displayed product has $k$ factors.
-- source:
--   J. D. Huba, NRL Plasma Formulary, Naval Research Laboratory, 2013, p. 3, section "Numerical and Algebraic", the Rothe-Hagen identity ("good for all complex x, y, z except when singular"), footnote 2: H. W. Gould, "Note on Some Binomial Coefficient Identities of Rosenbaum", J. Math. Phys. 10, 49 (1969); H. W. Gould and J. Kaucky, "Evaluation of a Class of Binomial Coefficient Summations", J. Comb. Theory 1, 233 (1966). https://www.nrl.navy.mil/News-Media/Publications/NRL-Plasma-Formulary/

import Mathlib

namespace NRLFormulary

/-- The singularity-free form of the Rothe factor
`x / (x + k z) * cbinom (x + k z) k`, in which the factor `x + k z` has been
cancelled: `rotheA x z 0 = 1` and, for `k + 1 ≥ 1`,
`rotheA x z (k+1) = x (x + (k+1) z - 1) ⋯ (x + (k+1) z - k) / (k+1)!`. -/
noncomputable def rotheA (x z : ℂ) : ℕ → ℂ
  | 0 => 1
  | (k + 1) =>
      x * (∏ j ∈ Finset.range k, (x + ((k : ℂ) + 1) * z - ((j : ℂ) + 1))) /
        (Nat.factorial (k + 1) : ℂ)

end NRLFormulary


