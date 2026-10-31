-- Prove2me | Definitions.Def_DarkKnights_Primitives
-- name    : DarkKnights_Primitives
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:57.984985+00:00
-- url     : https://prove2.me/theorems/51f3ffe7-b86c-4af8-8083-dabad6e71a9b
-- title:
--   Asset value $a=zk^\alpha$, uniform expectation, and the equity holders' default decision
-- statement:
--   The primitives shared by both models of the paper.
--
--   A firm with capital $k\ge 0$ has end-of-period asset value
--   $$
--   a(z,k)=z\,k^{\alpha},\qquad \alpha\in(0,1),
--   $$
--   eq. (1), where the profit shock is uniform, $z\sim U[0,Z]$ with $Z>0$. Expectations are
--   $$
--   \mathbb E[f]=\frac1Z\int_{[0,Z]} f(z)\,dz .
--   $$
--
--   After $z$ is drawn, the equity holders face debt with face value $d$ (the original face value $b$, or a reduced $b_n$ after an equity injection by the CDS dealer) and a lender holding CDS protection $r=hb$. They choose one of three actions:
--
--   1. **repay** $d$, with equity payoff $a-d$ and lender payoff $d$;
--   2. **renegotiate**, feasible iff $hb\le a$ (eq. (12)): the owner's take-it-or-leave-it offer pays the lender $b_r=hb$, with equity payoff $a-hb$;
--   3. **liquidate**, with equity payoff $0$ and lender payoff $0$ from the firm (the whole firm value is lost); liquidation is the credit event that triggers the CDS payment $hb$.
--
--   They take the action with the largest equity payoff, ties broken in the order repay, renegotiate, liquidate.
--
--   These objects define the default decision analysed in Lemma 1 and the payoffs of Table 3, on which both equilibrium models are built.
--
--   **Formalization Note** The tie-break is the paper's (p.15: "prefer repayment to renegotiation if $a-b_n\ge a-b_r$", "prefer repayment to liquidation if $a-b_n\ge 0$"; Lemma 1's weak inequalities). The renegotiated payment is $hb$ with the original $b$ even after a reduction to $b_n$ (p.15, footnote 25). $k^\alpha$ is `Real.rpow`. The text says the bargaining game is feasible "if and only if $hb<a$" on p.9 but derives the weak condition $hb\le a$ from its two constraints on p.9 and in eq. (12); the weak form is used.
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §1 eq. (1), p.7 (PDF 9); pp.8–9 (PDF 10–11); p.12 (PDF 14) U[0,Z]; §2 eq. (12) and following paragraph, p.15 (PDF 17); Table 3, p.35 (PDF 37); footnote 25, p.42 (PDF 44)

import Mathlib

open MeasureTheory

namespace DarkKnights

/-- Asset value `a(z, k) = z k^α`, eq. (1).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §1, eq. (1), p.7 (PDF p.9).

**Formalization Note** `k ^ α` is `Real.rpow`; the paper takes `k ≥ 0` and `α ∈ ]0,1[`, so
`0 ^ α = 0`. -/
noncomputable def assetValue (α z k : ℝ) : ℝ := z * k ^ α

/-- Expectation over the profit shock `z ∼ U[0, Z]` (§1, p.12, PDF p.14: "We assume that the
profitability shock z follows a uniform distribution, z ∼ U[0, Z]"), with `dΓ(z) = dz / Z`:
`E[f] = (1/Z) ∫_{[0,Z]} f(z) dz`.

**Formalization Note** This is the Bochner set integral over `Set.Icc 0 Z`; every paper integral
`∫_x^y … dΓ(z)` is a set integral over a subset of `[0, Z]`, never a (possibly reversed) interval
integral. -/
noncomputable def expect (Z : ℝ) (f : ℝ → ℝ) : ℝ := (1 / Z) * ∫ z in Set.Icc (0 : ℝ) Z, f z

/-- The equity holders' three actions at the end of the period (p.7, PDF p.9): repay the debt in
full, renegotiate it, or liquidate (file for bankruptcy; the whole firm value is lost). -/
inductive Action
  | repay
  | renegotiate
  | liquidate
  deriving DecidableEq

/-- The equity holders' default decision (§1, pp.7–9; §2, p.15, eq. (12) and the paragraph
after it; PDF pp.9–11, 17). The asset value is `a`, the face value of debt in force is `d`
(the original `b`, or `b_n` after an equity injection), and `r = h b` is the lender's CDS
protection, which is his outside option in renegotiation.

* repaying gives equity `a − d`;
* renegotiation is feasible iff `r ≤ a` (eq. (12)); the owner's take-it-or-leave-it offer is
  `b_r = r = h b` and gives equity `a − r`;
* liquidation gives equity `0`.

The equity holders take the action with the largest equity payoff, ties broken
repay ≻ renegotiate ≻ liquidate.

**Formalization Note** The tie-break is the paper's convention: p.15 "prefer repayment to
renegotiation if a − b_n ≥ a − b_r", "prefer repayment to liquidation if a − b_n ≥ 0", and
Lemma 1's weak inequalities. The renegotiation payment uses the original `b`
(`r = h b`) even after a reduction to `b_n` (p.15 and footnote 25, p.42). -/
noncomputable def defaultAction (a d r : ℝ) : Action :=
  if 0 ≤ a - d ∧ (r ≤ a → a - r ≤ a - d) then Action.repay
  else if r ≤ a ∧ 0 ≤ a - r then Action.renegotiate
  else Action.liquidate

/-- Equity payoff of the default decision: `a − d` (repay), `a − r` (renegotiate), `0`
(liquidate); p.8 (PDF p.10) and Table 3, p.35 (PDF p.37). -/
noncomputable def equityPayoff (a d r : ℝ) : ℝ :=
  match defaultAction a d r with
  | Action.repay => a - d
  | Action.renegotiate => a - r
  | Action.liquidate => 0

/-- The lender's payoff from the firm under the default decision: `d` (repay), `r = b_r`
(renegotiate), `0` (liquidate); p.8 (PDF p.10) and Table 3, p.35 (PDF p.37). The CDS payment
in liquidation is accounted separately. -/
noncomputable def debtPayoff (a d r : ℝ) : ℝ :=
  match defaultAction a d r with
  | Action.repay => d
  | Action.renegotiate => r
  | Action.liquidate => 0

/-- Indicator of liquidation, the credit event that triggers the CDS payment (p.11, PDF p.13):
`1` if the default decision is to liquidate, `0` otherwise. -/
noncomputable def liqInd (a d r : ℝ) : ℝ :=
  if defaultAction a d r = Action.liquidate then 1 else 0

end DarkKnights


