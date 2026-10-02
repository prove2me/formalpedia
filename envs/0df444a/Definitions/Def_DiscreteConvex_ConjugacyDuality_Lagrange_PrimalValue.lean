-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_PrimalValue
-- name    : DiscreteConvex_ConjugacyDuality_Lagrange_PrimalValue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:12:48.258973+00:00
-- url     : https://prove2.me/theorems/24588dc0-c734-4b3a-8d24-7e0d2b4d7898
-- title:
--   Primal objective recovered at zero perturbation (Eq. 8.54)
-- statement:
--   The **primal objective** $f(x) = F(x,0)$ recovered from the perturbation $F$ at the zero perturbation.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.54).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.54)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.236, Eq. (8.52)-(8.54): the primal objective
recovered from a perturbation function at zero perturbation, in
`DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- The **primal objective** `f(x) = F(x,0)` (Eq. (8.54)) recovered from the perturbation
`F : Zⱽ × Z^U → Z ∪ {+∞}` at the zero perturbation. -/
def PrimalValue {V U : Type*} [Zero (U → ℤ)] (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) (x : V → ℤ) :
    WithTop ℝ :=
  F x 0

end DiscreteConvex.ConjugacyDuality.Lagrange


