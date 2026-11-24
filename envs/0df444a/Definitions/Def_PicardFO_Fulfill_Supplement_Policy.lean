-- Prove2me | Definitions.Def_PicardFO_Fulfill_Supplement_Policy
-- name    : PicardFO_Fulfill_Supplement_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:06:46.199368+00:00
-- url     : https://prove2.me/theorems/9f8e371f-2342-4f8c-8013-4dff58f6ece5
-- title:
--   Arbitrary local policies and numerical warehouse (s,S) rule (13)
-- statement:
--   For every retailer $n$, let $\pi_n(x,w)$ be an arbitrary real-valued function of its local inventory and exogenous data. For every local stock $x\le c_n$ and every disturbance $w$ with $n(w)=n$ it must satisfy
--   $$
--   0\le\pi_n(x,w),\qquad (x-d(w))^++\pi_n(x,w)\le c_n.
--   $$
--   The warehouse uses the conventional parameters $0\le s\le S\le c_0$, with nonnegative retailer capacities $c_n\le s$ and nonnegative demands. For request $q=\pi_{n(w)}(x_{n(w)},w)$ its numerical replenishment is
--   $$
--   u=\begin{cases}S-(x_0-q)^+&x_0-q\le s,\\0&x_0-q>s.\end{cases}
--   $$
--   Together with (12), this gives precisely the warehouse state rule (13). No monotonicity, continuity or probabilistic condition is imposed on local policies. No lower bound on the initial warehouse stock is assumed.
--
--   **Formalization Note** Nonnegative demand and capacities, and ordered feasible $(s,S)$ levels, spell out the operational meaning of demand, storage capacities and order-up-to policy. Local inventory is allowed to be any real number below its capacity, including negative values. On invalid data the numerical formula still returns a real pair without asserting feasibility.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, pp. 14–15, Appendix B.2, eq. (13)

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Supplement_Model

namespace PicardFO.Fulfill.Supplement

/-- Arbitrary local retailer policies and warehouse (s,S) parameters. -/
structure Policy (N : ℕ) (Ω : Type*) where
  request : Fin N → ℝ → Ω → ℝ
  s : ℝ
  S : ℝ

namespace Policy
variable {N : ℕ} {Ω : Type*}

/-- Standing policy/capacity conventions of B.1--B.2; no initial-stock lower bound.
The local constraints bind `π_n(x, w)` at disturbances `w` whose order is for retailer `n`,
the only arguments at which `π_n` is ever evaluated. -/
def Admissible (P : Policy N Ω) (D : Model N Ω) : Prop :=
  0 ≤ P.s ∧ P.s ≤ P.S ∧ P.S ≤ D.warehouseCap ∧
  (∀ n, 0 ≤ D.retailerCap n ∧ D.retailerCap n ≤ P.s) ∧
  (∀ w, 0 ≤ D.demand w) ∧
  ∀ n x w, D.retailer w = n → x ≤ D.retailerCap n →
    0 ≤ P.request n x w ∧
      max (x - D.demand w) 0 + P.request n x w ≤ D.retailerCap n

/-- The numerical quantity implementing (13) under transition (12).
In particular this is not a Boolean reset command. -/
noncomputable def action (P : Policy N Ω) (D : Model N Ω) (x : Stock N) (w : Ω) : Action :=
  let q := P.request (D.retailer w) (x.retailer (D.retailer w)) w
  (if x.warehouse - q ≤ P.s then P.S - max (x.warehouse - q) 0 else 0, q)

end Policy
end PicardFO.Fulfill.Supplement


