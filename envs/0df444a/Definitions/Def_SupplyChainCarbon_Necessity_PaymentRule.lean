-- Prove2me | Definitions.Def_SupplyChainCarbon_Necessity_PaymentRule
-- name    : SupplyChainCarbon_Necessity_PaymentRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:34:42.155772+00:00
-- url     : https://prove2.me/theorems/3eb2a3fe-f030-413e-a51c-2b04f94db7d1
-- title:
--   Footprint-only payments, transfers and participation
-- statement:
--   At a given real carbon price $p$, a payment rule consists of functions $h_n,\widehat f_n,g_n:F\to\mathbb R$, each differentiable on $F$, such that for every $\phi\in F$,
--
--   $$h_n(\phi)=p\widehat f_n(\phi)+g_n(\phi),\qquad\sum_n g_n(\phi)=0.$$
--
--   The transfers may have either sign. The allocation and transfers carry no monotonicity, convexity or balance restriction beyond these equations. Shape conditions on total payments are imposed separately by the theorems that need them.
--
--   For given reservation profits $\pi_n$, participation at a profile $e$ means
--
--   $$V_n(e_n)-h_n(f(e))\ge\pi_n\quad\text{for every }n.$$
--
--   The Nash predicate transparently reuses the published pure-game best-response definition: each block is feasible and every feasible replacement of a firm's entire block, with rivals fixed, gives that firm no larger payoff. Participation and Nash incentives are separate notions. This distinction prevents a marginal condition from being mistaken for a guarantee about arbitrary reservation profits.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, §3.3, pp. 10–11, Eqs. (3)–(4); §4, p. 11, Eq. (5)

import Definitions.Def_SupplyChainCarbon_Necessity_Technology

namespace SupplyChainCarbon.Necessity

/-- Equation (5), including balanced internal transfers, at the given price. -/
structure PaymentRule (N I : ℕ) (p : ℝ) where
  payment : Fin N → Footprint I → ℝ
  allocation : Fin N → Footprint I → ℝ
  transfer : Fin N → Footprint I → ℝ
  payment_diff : ∀ n, DifferentiableOn ℝ (payment n) (footprintOrthant I)
  allocation_diff : ∀ n, DifferentiableOn ℝ (allocation n) (footprintOrthant I)
  transfer_diff : ∀ n, DifferentiableOn ℝ (transfer n) (footprintOrthant I)
  payment_eq : ∀ φ ∈ footprintOrthant I, ∀ n, payment n φ = p * allocation n φ + transfer n φ
  transfers_balanced : ∀ φ ∈ footprintOrthant I, ∑ n, transfer n φ = 0

/-- Participation (3) is separate from Nash incentives. -/
def participation {N I : ℕ} {m : Fin N → ℕ} {p : ℝ}
    (C : Technology N I m) (R : PaymentRule N I p)
    (reservation : Fin N → ℝ) (e : Effort N m) : Prop :=
  ∀ n, reservation n ≤ profit C n (e n) - R.payment n (C.footprint e)

/-- The published full whole-block best-response predicate (4). -/
abbrev isNash {N I : ℕ} {m : Fin N → ℕ} {p : ℝ}
    (C : Technology N I m) (R : PaymentRule N I p) (e : Effort N m) : Prop :=
  CarbonDoubleCount.Planner.IsNash C.bound (profit C) C.footprint R.payment e

end SupplyChainCarbon.Necessity


