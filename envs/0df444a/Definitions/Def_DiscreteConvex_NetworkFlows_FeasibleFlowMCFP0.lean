-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_FeasibleFlowMCFP0
-- name    : DiscreteConvex_NetworkFlows_FeasibleFlowMCFP0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:14:55.330956+00:00
-- url     : https://prove2.me/theorems/97eec3b9-42d4-4f6b-a480-5eea3bf5465e
-- title:
--   Feasibility for the minimum cost flow problem MCFP0 (Eqs. 9.12-9.13)
-- statement:
--   A flow $\xi : A \to \mathbb R$ is **feasible for MCFP0** with upper capacity $\bar c$, lower capacity $\underline c$, and supply $x$ if it meets the capacity constraint $\underline c(a) \le \xi(a) \le \bar c(a)$ for all $a \in A$ (9.12) and has boundary $x$, i.e. $\partial\xi = x$ (9.13).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.248, Eqs. (9.12)-(9.13).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.248, Eqs. (9.12)-(9.13)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_Boundary

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.248, Eqs. (9.12)-(9.13): feasibility for the
minimum cost flow problem MCFP0, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- A flow `ξ : A → ℝ` is **feasible for MCFP0** with upper capacity `c̄`, lower capacity `c`,
and supply `x` if it meets the capacity constraint (9.12) and has boundary `x` (9.13). -/
def FeasibleFlowMCFP0 {V A : Type*} [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (x : V → ℝ)
    (ξ : A → ℝ) : Prop :=
  (∀ a : A, cLower a ≤ (ξ a : WithBot ℝ) ∧ (ξ a : WithTop ℝ) ≤ cUpper a) ∧
    ∀ v : V, Boundary tail head ξ v = x v

end DiscreteConvex.NetworkFlows


