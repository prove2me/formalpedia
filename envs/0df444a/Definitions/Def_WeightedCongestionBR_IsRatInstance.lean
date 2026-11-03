-- Prove2me | Definitions.Def_WeightedCongestionBR_IsRatInstance
-- name    : WeightedCongestionBR_IsRatInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:52.21842+00:00
-- url     : https://prove2.me/theorems/283ddb29-097e-44f0-8ff9-4893b2a53ad6
-- title:
--   Rational instance of a game
-- statement:
--   A game is a rational instance with data $(w,a)$ if its weights are the rationals $w_u$, the coefficients $a_{e,\nu}$ are nonnegative, and
--
--   $$
--   c_e(x)=\sum_{\nu=0}^d a_{e,\nu}x^\nu\qquad\text{for every load }x\ge0 .
--   $$
--
--   Such a game is a polynomial congestion game of degree $d$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 4, p.18

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_RatData
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- A game is a **rational instance** of degree `d` with data `D` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Theorem 4, p.18): its weights
are the rationals `D.w`, its coefficients `D.a` are nonnegative, and every cost is
`c_e(x) = ∑_{ν=0}^d a_{e,ν} x^ν` on loads `x ≥ 0`. Such a game is polynomial of degree `d`. -/
def IsRatInstance {n r d : ℕ} (G : Game n r) (D : RatData n r d) : Prop :=
  (∀ u, (G.demand u : ℝ) = (D.w u : ℝ)) ∧ (∀ e ν, 0 ≤ D.a e ν) ∧
    ∀ (e : Fin r) (x : ℝ≥0), G.cost e x = ∑ ν : Fin (d + 1), (D.a e ν : ℝ) * (x : ℝ) ^ (ν : ℕ)

end WeightedCongestionBR


