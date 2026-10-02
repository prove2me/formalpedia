-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_OptP
-- name    : DiscreteConvex_ConjugacyDuality_Lagrange_OptP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:14:06.080566+00:00
-- url     : https://prove2.me/theorems/da86b82b-a972-489a-9809-fdb07e0c7674
-- title:
--   Primal optimal solution set
-- statement:
--   $\operatorname{opt}(P) = \{x \in \mathbb Z^V : f(x) = \inf(P)\}$, the optimal solution set of the primal problem.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.237

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_PrimalValue
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_InfP

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.237: the primal optimal solution set, in
`DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

open DiscreteConvex.ConjugacyDuality

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- `opt(P) = \{x ∈ Zⱽ : f(x) = inf(P)\}`, the optimal solution set of the primal problem. -/
noncomputable def OptP {V U : Type*} [Fintype U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) : Set (V → ℤ) :=
  {x | ToEReal (PrimalValue F x) = InfP F}

end DiscreteConvex.ConjugacyDuality.Lagrange


