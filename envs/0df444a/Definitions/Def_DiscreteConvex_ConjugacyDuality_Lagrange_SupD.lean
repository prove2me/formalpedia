-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_SupD
-- name    : DiscreteConvex_ConjugacyDuality_Lagrange_SupD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:14:14.706501+00:00
-- url     : https://prove2.me/theorems/419c9c9a-9b2d-451d-a869-d903f5017f4f
-- title:
--   Dual optimal value
-- statement:
--   $\sup(D) = \sup\{g(y) : y \in \mathbb Z^U\}$, the optimal value of the dual problem $D$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_DualObjective

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.237: the dual optimal value, in
`DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- `sup(D) = sup\{g(y) : y ∈ Z^U\}`, the optimal value of the dual problem `D`. -/
noncomputable def SupD {V U : Type*} [Fintype U] (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) : EReal :=
  sSup {v : EReal | ∃ y : U → ℤ, v = DualObjective F y}

end DiscreteConvex.ConjugacyDuality.Lagrange


