-- Prove2me | Definitions.Def_TradeAgentNV_winProb
-- name    : TradeAgentNV_winProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:29:32.130399+00:00
-- url     : https://prove2.me/theorems/d649f0c1-5dd4-4f54-af47-294c43881796
-- title:
--   Win probability $w(b)=P(Z\le b)$
-- statement:
--   The trade agent bids $b$ per unit for the seller's lot. The seller's **ask price** $Z$ is the minimum bid the seller accepts, a real random variable on a probability space $(\Omega,\mathcal F,P)$; the bid wins exactly when $Z\le b$. The **probability of winning** is the cdf of $Z$,
--   $$
--   w(b)=P(Z\le b).
--   $$
--   It is the paper's model of the bid outcome uncertainty.
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, §3.1, display (1), p.8

import Mathlib

open MeasureTheory

namespace TradeAgentNV

/-- The **probability of winning the bid** `w(b) = P(Z ≤ b)` (display (1), p.8) of
Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023): `Z` is the seller's ask price, a random variable on the probability space `(Ω, P)`,
and the agent's bid `b` wins exactly when `Z ≤ b`. So `w` is the cdf of `Z`.

**Formalization Note.** `P.real` is the real-valued measure; for a probability measure `P` it
takes values in `[0, 1]`. -/
noncomputable def winProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ) (b : ℝ) :
    ℝ :=
  P.real {ω | Z ω ≤ b}

end TradeAgentNV


