-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_OptD
-- name    : DiscreteConvex_ConjugacyDuality_Lagrange_OptD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:15:16.932021+00:00
-- url     : https://prove2.me/theorems/e411aa2b-d21a-438d-9ab4-9b230f377bd8
-- title:
--   Dual optimal solution set
-- statement:
--   $\operatorname{opt}(D) = \{y \in \mathbb Z^U : g(y) = \sup(D)\}$, the optimal solution set of the dual problem.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_DualObjective
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_SupD

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.237: the dual optimal solution set, in
`DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- `opt(D) = \{y ∈ Z^U : g(y) = sup(D)\}`, the optimal solution set of the dual problem. -/
noncomputable def OptD {V U : Type*} [Fintype U] (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) :
    Set (U → ℤ) :=
  {y | DualObjective F y = SupD F}

end DiscreteConvex.ConjugacyDuality.Lagrange


