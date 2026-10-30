-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch05_ch05ParameterDomain
-- name    : RamanujanLostNotebook_PartII_ch05_ch05ParameterDomain
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:45:43.932549+00:00
-- url     : https://prove2.me/theorems/32139edf-cc2d-494f-87f6-66358ab52a66
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 5: ch05ParameterDomain
-- statement:
--   Ordinary convergence and absence of reciprocal-product poles for the
--   Bailey transforms (5.2.3) and (5.2.4). Use base=q² and base=q respectively.
--   The condition |q²/(rho₁ rho₂)|<1 gives geometric convergence of the left row.
--   The factor conditions exclude precisely zeros of the right denominator products.
--   For 0<|q|<1, this set approaches (q,-q) from a nonempty open region; it is
--   not a convergence assumption on the boundary's divergent printed series.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 5.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Ordinary convergence and absence of reciprocal-product poles for the
Bailey transforms (5.2.3) and (5.2.4). Use base=q² and base=q respectively.
The condition |q²/(rho₁ rho₂)|<1 gives geometric convergence of the left row.
The factor conditions exclude precisely zeros of the right denominator products.
For 0<|q|<1, this set approaches (q,-q) from a nonempty open region; it is
not a convergence assumption on the boundary's divergent printed series. -/
def ch05ParameterDomain (q base : ℂ) : Set (ℂ × ℂ) :=
  {rho | rho.1 ≠ 0 ∧ rho.2 ≠ 0 ∧ ‖q ^ 2 / (rho.1 * rho.2)‖ < 1 ∧
    ∀ k : ℕ, (q ^ 2 / rho.1) * base ^ k ≠ 1 ∧
      (q ^ 2 / rho.2) * base ^ k ≠ 1}

end RamanujanLostNotebook.PartII

end


