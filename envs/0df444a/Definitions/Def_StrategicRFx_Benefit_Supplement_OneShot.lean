-- Prove2me | Definitions.Def_StrategicRFx_Benefit_Supplement_OneShot
-- name    : StrategicRFx_Benefit_Supplement_OneShot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:08:00.773575+00:00
-- url     : https://prove2.me/theorems/1b5bd154-4a38-4d02-b4b2-add01a27d204
-- title:
--   §3.3 — nonnegative one-shot quotes, realized payoffs and pure Nash equilibrium
-- statement:
--   Each supplier chooses one nonnegative real profit quotation. Given a deterministic buyer response, the realized supplier payoffs come from the actual negotiation continuation. A pure Nash equilibrium forbids every unilateral deviation to another nonnegative real quotation:
--
--   $$u_1(x'_1,x_2)\le u_1(x_1,x_2),\qquad u_2(x_1,x'_2)\le u_2(x_1,x_2).$$
--
--   The general two-player normal-form pure Nash definition is imported from the published arbitrary-strategy definition, rather than duplicated. The separate priority predicate specifies the buyer's first two source tie preferences. Existence and the remaining technical refinement are not assumed. The one-shot object does not stand in for arbitrary tendering procedures in Theorem 6.
--
--   **Supplier tie preference** The general primary-profit Nash predicate is accompanied by the source p. 16 condition that, at equal own profit, no unilateral quote is preferred by the buyer. Buyer preference compares profit, then accept-both/early-acceptance priority. Ignoring this last tier could leave rejected zero-profit quotes falsely indifferent to accepted quotes.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), §3.3, p. 20

import Mathlib
import Definitions.Def_CompetingChains_Cournot_TwoPlayerGame
import Definitions.Def_StrategicRFx_Benefit_Supplement_Negotiation

namespace StrategicRFx.Benefit.Supplement

/-- One nonnegative profit quotation by each supplier, §3.3. -/
def quotePair (x y : NNReal) : Fin 2 → ℝ := fun i => if i = 0 then (x : ℝ) else (y : ℝ)

abbrev BuyerSelector := (Fin 2 → ℝ) → Negotiation

/-- The buyer's p. 16 priorities, without an assertion that a selector exists.
The ec18–ec21 technical refinement is a separate, still outstanding object. -/
def RespectsPriorities (P : Params) (β : BuyerSelector) : Prop :=
  ∀ t, (∀ i, 0 ≤ t i) → IsPriorityResponse P t (β t)

/-- Realized supplier profit comes from the chosen Nash continuation, rather
than from the buyer's maximum value alone. -/
def oneShotPayoff (P : Params) (β : BuyerSelector) (i : Fin 2) (x y : NNReal) : ℝ :=
  ((β (quotePair x y)).payoff P (quotePair x y)).2 i

/-- The buyer's preference between two quotation outcomes includes the
source's acceptance hierarchy at equal buyer profit, not just profit alone. -/
def BuyerPrefersQuotation (P : Params) (β : BuyerSelector)
    (new old : Fin 2 → ℝ) : Prop :=
  ((β old).payoff P old).1 < ((β new).payoff P new).1 ∨
    (((β new).payoff P new).1 = ((β old).payoff P old).1 ∧
      (β old).priority P old < (β new).priority P new)

/-- The published arbitrary-action primary-profit Nash definition is reused.
At equal supplier profit the source further requires the quote preferred
by the buyer, including accept-both/early-acceptance priority. Every real
nonnegative unilateral quote remains a feasible deviation. -/
def IsOneShotEquilibrium (P : Params) (β : BuyerSelector) (x y : NNReal) : Prop :=
  CompetingChains.Cournot.IsPureNash (oneShotPayoff P β 0) (oneShotPayoff P β 1) x y ∧
    (∀ x', oneShotPayoff P β 0 x' y = oneShotPayoff P β 0 x y →
      ¬ BuyerPrefersQuotation P β (quotePair x' y) (quotePair x y)) ∧
    (∀ y', oneShotPayoff P β 1 x y' = oneShotPayoff P β 1 x y →
      ¬ BuyerPrefersQuotation P β (quotePair x y') (quotePair x y))

end StrategicRFx.Benefit.Supplement


