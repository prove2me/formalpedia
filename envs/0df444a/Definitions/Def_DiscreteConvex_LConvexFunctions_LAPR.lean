-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_LAPR
-- name    : DiscreteConvex_LConvexFunctions_LAPR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:14:22.818716+00:00
-- url     : https://prove2.me/theorems/51237da6-0678-4651-b576-4e01063f669d
-- title:
--   The approach property (L-natural-APR[Z])
-- statement:
--   Axiom **(L$^\natural$-APR[Z])**: for any $p,q \in \mathbb Z^V$ with $\operatorname{supp}^+(p-q) \ne \emptyset$, $g(p)+g(q) \ge g(p-\chi_X) + g(q+\chi_X)$, where $X = \arg\max_v\{p(v)-q(v)\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, axiom (L♮-APR[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, axiom (L♮-APR[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_LConvexFunctions_ArgMaxDiff
import Definitions.Def_DiscreteConvex_LConvexFunctions_IndicatorVec

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.180, axiom (L♮-APR[Z]): the approach
property, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- Axiom **(L♮-APR[Z])**: for any `p, q ∈ Zⱽ` with `supp⁺(p-q) ≠ ∅`,
`g(p) + g(q) ≥ g(p - χ_X) + g(q + χ_X)`, where `X = arg max_v \{p(v) - q(v)\}`. -/
def LAPR {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, (SuppPos p q).Nonempty →
    g p + g q ≥ g (fun v => p v - IndicatorVec (ArgMaxDiff p q) v) +
      g (fun v => q v + IndicatorVec (ArgMaxDiff p q) v)

end DiscreteConvex.LConvexFunctions


