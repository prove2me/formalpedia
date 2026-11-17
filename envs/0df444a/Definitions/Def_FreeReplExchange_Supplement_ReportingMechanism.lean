-- Prove2me | Definitions.Def_FreeReplExchange_Supplement_ReportingMechanism
-- name    : FreeReplExchange_Supplement_ReportingMechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:32:30.360253+00:00
-- url     : https://prove2.me/theorems/6ba85c94-9e65-43fb-b047-8bde1cd9cf59
-- title:
--   Holdings- and utility-reporting exchange environments
-- statement:
--   A **reporting mechanism** maps a reported initial allocation and reported utility family to a published exchange protocol. It is stable and MIC when it satisfies the published protocol rules, MIC, and stability on every reported instance within the utility bounds.
--
--   In the holdings-report game, an agent may hide any truly held good but may not report a good she lacks. The protocol runs on the report; realized holdings are the Boolean union of true initial holdings and reported-instance receipts, so receiving a hidden good creates no second copy. Payoff uses the true utility family. Truthful holdings reporting is a Nash equilibrium when no unilateral legal hiding report is profitable under accept-all.
--
--   In the utility-report game, initial holdings are truthful. A deviator may replace her whole utility row by any row that keeps the combined report within the model bounds. The protocol, MIC, and stability use the reported family, while payoff uses the true family. Truthful utility reporting is a Nash equilibrium when no such unilateral report is profitable under accept-all.
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), section 3.5, pp.24--25 (PDF pp.26--27), Theorems 5--6

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_IsExchangeProtocol

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- A reporting mechanism for section 3.5, pp. 24--25 (PDF pp. 26--27): after seeing the reported
initial allocation and reported utility family, the planner supplies a protocol for that reported
instance. -/
abbrev ReportingMechanism (A : Type*) (m : ℕ) :=
  (A → Fin m → Bool) → (A → A → Fin m → ℝ) → Protocol A m

/-- A reporting mechanism is a stable MIC exchange mechanism on every reported instance satisfying
the paper's utility bounds.  This is the meaning of "stable MIC exchange protocol" in Theorems 5
and 6, p. 25 (PDF p. 27). -/
def IsStableMICReportingMechanism {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (F : ReportingMechanism A m) : Prop :=
  ∀ (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ), SignCond U →
    IsExchangeProtocol x0 (F x0 U) ∧ IsMIC x0 U (F x0 U) ∧ IsStable x0 U (F x0 U)

/-- A holdings report is legal when it hides only truly held goods: `reported <= trueHoldings`
coordinatewise, section 3.5, p. 24 (PDF p. 26). -/
def LegalHoldingsReport {m : ℕ} (trueHoldings reported : Fin m → Bool) : Prop :=
  ∀ r, reported r = true → trueHoldings r = true

/-- The realized allocation after a run based on reported holdings.  True hidden goods remain held,
and a reported receipt of an already hidden good leaves one Boolean copy, section 3.5, p. 24
(PDF p. 26). -/
def realizedHoldings {A : Type*} {m : ℕ} (trueInitial reportedTerminal : A → Fin m → Bool) :
    A → Fin m → Bool :=
  fun i r => trueInitial i r || reportedTerminal i r

/-- Agent `i`'s true payoff from a holdings-report profile.  The protocol, MIC and stability use
the reported initial allocation; the realized allocation begins from the true holdings and utility
uses the truthful matrix, as specified before Theorem 5, pp. 24--25 (PDF pp. 26--27). -/
noncomputable def holdingsReportPayoff {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (trueInitial : A → Fin m → Bool) (U : A → A → Fin m → ℝ)
    (F : ReportingMechanism A m) (reported : A → Fin m → Bool) (i : A) : ℝ :=
  util U i (realizedHoldings trueInitial
    (xInf reported (F reported U) Finset.univ acceptAll))

/-- Truthful reporting of initial holdings is a Nash equilibrium when no agent can gain by
unilaterally hiding any subset of her truly held goods while all agents accept, section 3.5 and
Theorem 5, pp. 24--25 (PDF pp. 26--27). -/
def TruthfulHoldingsReportingNE {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (trueInitial : A → Fin m → Bool) (U : A → A → Fin m → ℝ)
    (F : ReportingMechanism A m) : Prop :=
  ∀ (i : A) (reporti : Fin m → Bool), LegalHoldingsReport (trueInitial i) reporti →
    holdingsReportPayoff trueInitial U F (Function.update trueInitial i reporti) i ≤
      holdingsReportPayoff trueInitial U F trueInitial i

/-- Agent `i`'s true payoff from a utility-report profile.  The protocol, MIC and stability use the
reported matrices, whereas payoff is evaluated by the true matrices, as specified before Theorem 6,
p. 25 (PDF p. 27). -/
noncomputable def utilityReportPayoff {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (trueU : A → A → Fin m → ℝ)
    (F : ReportingMechanism A m) (reportedU : A → A → Fin m → ℝ) (i : A) : ℝ :=
  util trueU i (xInf x0 (F x0 reportedU) Finset.univ acceptAll)

/-- Truthful utility-matrix reporting is a Nash equilibrium when no agent can gain by replacing her
matrix row by any other row for which the combined report remains within the model's utility bounds,
while every agent reports holdings truthfully and accepts, Theorem 6, p. 25 (PDF p. 27). -/
def TruthfulUtilityReportingNE {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (trueU : A → A → Fin m → ℝ)
    (F : ReportingMechanism A m) : Prop :=
  ∀ (i : A) (reporti : A → Fin m → ℝ), SignCond (Function.update trueU i reporti) →
    utilityReportPayoff x0 trueU F (Function.update trueU i reporti) i ≤
      utilityReportPayoff x0 trueU F trueU i

end FreeReplExchange.Supplement


