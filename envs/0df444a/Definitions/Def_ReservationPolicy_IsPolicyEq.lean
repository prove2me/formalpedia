-- Prove2me | Definitions.Def_ReservationPolicy_IsPolicyEq
-- name    : ReservationPolicy_IsPolicyEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:02.333608+00:00
-- url     : https://prove2.me/theorems/d3d960fc-ba59-40f2-8331-3002d8c22a3f
-- title:
--   Equilibrium under a transfer of $s$ seats
-- statement:
--   Let $b$ be the benchmark outcome in which type $x$ invests. An outcome $o$ is an equilibrium under a transfer of $s$ seats when
--
--   1. type-$x$ students invest, and the type-$x$ group is consistent at the cutoff $d_x$ and the type-$y$ group at the cutoff $d_y$;
--   2. investing is optimal for type $x$ at $(d_x,r_{x,s})$;
--   3. total seats clear, $z=\alpha\rho_{x,s}+(1-\alpha)\rho_{y,s}$;
--   4. the seats lost by type $x$ and gained by type $y$ both equal $s$:
--   $$
--   \alpha\rho_x(b)-\alpha\rho_{x,s}=(1-\alpha)\rho_{y,s}-(1-\alpha)\rho_y(b)=s.
--   $$
--   These are the conditions (17)–(23) of the paper.
--
--   **Formalization Note** The paper does not discuss a policy game in which type $x$ stops investing. This predicate is the investing branch (17).
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (17)–(23), pp.19–20

import Mathlib
import Definitions.Def_ReservationPolicy_InvestGroup
import Definitions.Def_ReservationPolicy_PlainGroup
import Definitions.Def_ReservationPolicy_InvestOptimal
import Definitions.Def_ReservationPolicy_PolicyOutcome_rhoX
import Definitions.Def_ReservationPolicy_PolicyOutcome_rhoY
import Definitions.Def_ReservationPolicy_Benchmark_rhoX
import Definitions.Def_ReservationPolicy_Benchmark_rhoY

namespace ReservationPolicy

/-- The equilibrium under a transfer of `s` seats, relative to the benchmark `b` in which type `x`
invests: type `x` invests, (17); each group is consistent at its own cutoff, (18)–(20); total
seats clear, (22); and the type-`x` admissions fall and the type-`y` admissions rise by `s` from
the benchmark, (23). Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eqs. (17)–(23), pp.19–20
(PDF 19–20).

**Formalization Note** The paper does not treat the policy game without investment. The policy
game here is its investing branch, (17), and investing is part of the equilibrium; it remains
a best response for every feasible `s` when `κ < κ*`. -/
def IsPolicyEq (P : Params) (b : Benchmark) (s : ℝ) (o : PolicyOutcome) : Prop :=
  InvestGroup P o.ex o.dx o.rx ∧ PlainGroup P o.ey o.dy o.ry ∧
    InvestOptimal P o.dx o.rx o.ex ∧
    P.z = P.α * o.rhoX + (1 - P.α) * o.rhoY P ∧
    P.α * b.rhoX - P.α * o.rhoX = s ∧
    (1 - P.α) * o.rhoY P - (1 - P.α) * b.rhoY P = s

end ReservationPolicy


