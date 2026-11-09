-- Prove2me | Definitions.Def_SATotalCoeffLB_coeffNorm
-- name    : SATotalCoeffLB_coeffNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:20:23.332914+00:00
-- url     : https://prove2.me/theorems/8c5524c7-0970-4f55-bdc0-89e5e3baee93
-- title:
--   Coefficient norm $\|f\|_1$
-- statement:
--   For $f$ in the Boolean quotient ring over a finite set $V$, the **coefficient norm** is the sum of the absolute values of the coefficients of its multilinear representative:
--
--   $$
--   \|f\|_1 = \sum_{S \subseteq V} \bigl|\widehat f(S)\bigr|.
--   $$
--
--   The lower bound of Theorem 3 is a lower bound on $\sum_{i<j} \|C_{ij}\|_1$, the total coefficient size of the multipliers of the AND checks.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.9 (Theorem 3), p.24 (Coefficient Norm)

import Mathlib
import Definitions.Def_SATotalCoeffLB_coeff

namespace SATotalCoeffLB

/-- **The coefficient norm `‖f‖₁`**: the sum of the absolute values of the coefficients of the
multilinear polynomial `f` (Theorem 3, p.9, and "Coefficient Norm", p.24, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)),
`‖f‖₁ = ∑_{S ⊆ V} |coeff f S|`. -/
noncomputable def coeffNorm {V : Type*} [Fintype V] [DecidableEq V] (f : CubeFn V) : ℝ :=
  ∑ S : Finset V, |coeff f S|

end SATotalCoeffLB


