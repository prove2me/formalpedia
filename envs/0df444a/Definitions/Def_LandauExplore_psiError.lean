-- Prove2me | Definitions.Def_LandauExplore_psiError
-- name    : LandauExplore_psiError
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-01T00:27:55.932113+00:00
-- url     : https://prove2.me/theorems/dfabbb1b-c905-46b3-bdac-99228c0dc326
-- title:
--   Psi-error hypothesis in von Koch form
-- statement:
--   For a real constant $C$, the psi-error hypothesis asserts that for all real $x \geq 2$, the Chebyshev function $\psi(x)$ satisfies $|\psi(x) - x| \leq C\sqrt{x}(\log x)^2$. This is the von Koch form of the error term in Chebyshev's theorem, stated here as an explicit hypothesis rather than as a proved fact: it is the conditional input for the theta-error bridge, and it is not claimed unconditionally.

import Mathlib.NumberTheory.Chebyshev

namespace LandauExplore

/-- An explicit psi-error hypothesis, in von Koch form: the Chebyshev function psi stays within C * sqrt(x) * (log x)^2 of x for x >= 2. -/
def psiError (C : ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2

end LandauExplore


