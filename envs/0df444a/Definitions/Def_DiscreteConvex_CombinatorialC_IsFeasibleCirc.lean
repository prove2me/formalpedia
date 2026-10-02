-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_IsFeasibleCirc
-- name    : DiscreteConvex_CombinatorialC_IsFeasibleCirc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:41:25.196462+00:00
-- url     : https://prove2.me/theorems/927b4e24-8742-49d5-bb14-3953c20e2e90
-- title:
--   Feasible circulation
-- statement:
--   $0\le\xi(a)\le c(a)$ for every arc, and $\partial\xi(v)=0$ at every vertex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.82-83, Eqs. (2.51)-(2.52).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.82-83, Eqs. (2.51)-(2.52)

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_Boundary

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, pp.82-83, Eqs. (2.51)-(2.52): a feasible
circulation, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `ξ` is a **feasible circulation** for capacity `c`: `0 ≤ ξ(a) ≤ c(a)` for every arc
(Eq. (2.51)) and `∂ξ(v) = 0` at every vertex (Eq. (2.52), conservation). -/
def IsFeasibleCirc {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (c xi : A → ℝ) : Prop :=
  (∀ a, 0 ≤ xi a ∧ xi a ≤ c a) ∧ ∀ v, Boundary src dst xi v = 0

end DiscreteConvex.CombinatorialC


