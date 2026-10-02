-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_DualObjective
-- name    : DiscreteConvex_ConjugacyDuality_Lagrange_DualObjective
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:13:30.177788+00:00
-- url     : https://prove2.me/theorems/48aaf3ef-347d-497a-9602-816d5323dafc
-- title:
--   Dual objective function (Eq. 8.60)
-- statement:
--   The **dual objective** $g(y) = \inf\{K(x,y) : x \in \mathbb Z^V\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237, Eq. (8.60).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237, Eq. (8.60)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_LagrangianKernel

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.237, Eq. (8.60): the dual objective function,
in `DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- The **dual objective** `g(y) = inf\{K(x,y) : x ∈ Zⱽ\}` (Eq. (8.60)). -/
noncomputable def DualObjective {V U : Type*} [Fintype U]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) (y : U → ℤ) : EReal :=
  sInf {v : EReal | ∃ x : V → ℤ, v = LagrangianKernel F x y}

end DiscreteConvex.ConjugacyDuality.Lagrange


