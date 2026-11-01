-- Prove2me | Definitions.Def_FracMPGA_Assumption4
-- name    : FracMPGA_Assumption4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:47.776988+00:00
-- url     : https://prove2.me/theorems/01f122b0-5e3f-45ce-b2e0-27bd74cc8fb2
-- title:
--   Assumption 4: $g^*$ calm on $\operatorname{dom} g^*$
-- statement:
--   **Assumption 4.** The Fenchel conjugate $g^*$ satisfies the calmness condition on $\operatorname{dom}g^*=\{y:g^*(y)<+\infty\}$.
--
--   It is used for the relative error bound (Proposition 6.3), through the Fréchet quotient rule of Proposition 2.1(ii). It holds when $g^*$ is the indicator of a set, as for the paper's models (2) and (3).
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §6.1, p.26, Assumption 4

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_FracMPGA_Problem
import Definitions.Def_FracMPGA_IsCalmOn

namespace FracMPGA

/-- **Assumption 4** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.26: "The function `g*` satisfies
calmness condition on `dom(g*)`", with `g*` the Fenchel conjugate of `g` and
`dom(g*) = {y : g*(y) < +∞}`. -/
def Assumption4 {n N : ℕ} (P : Problem n N) : Prop :=
  IsCalmOn (ConvexOptimization.fenchelConjugate P.g)
    {y | ConvexOptimization.fenchelConjugate P.g y ≠ ⊤}

end FracMPGA


