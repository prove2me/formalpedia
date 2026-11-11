-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Objectives
-- name    : MoneyBurningTrade_IndependentSurplus_Objectives
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:31.689059+00:00
-- url     : https://prove2.me/theorems/53a6a08a-33b7-4841-9235-68e6b23fe2eb
-- title:
--   Section 3.3 — traders’ surplus and joint-law expectations
-- statement:
--   At a profile $p=(s,b)$, write
--
--   $$\mathrm{TS}^b_M(p)=b x(p)-p_B(p),\quad \mathrm{TS}^s_M(p)=p_S(p)-s x(p),\quad \mathrm{TS}_M(p)=\mathrm{TS}^b_M(p)+\mathrm{TS}^s_M(p).$$
--
--   Money burnt is $p_B-p_S$, so $\mathrm{TS}_M=(b-s)x-(p_B-p_S)$. For any joint law $F$, the expected buyer, seller and total surplus are their corresponding integrals. They do not require independence. General nonnegative surplus expectations have an extended-nonnegative integral interface, allowing $+\infty$. The real integrals used on the bounded report square are accompanied by a finite-objectives conclusion certifying integrability of both transfers, both individual surpluses, their sum and GFT. The certificate is never imposed as an extra competitor hypothesis.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), §3.3, equations (11), (13), (15), printed p. 16–17 (PDF p. 17–18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Model

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- §3.3: buyer surplus above no trade, equal to buyer utility. -/
def buyerSurplus (M : SecondBestBT.Mechanism) (p : ℝ × ℝ) : ℝ :=
  p.2 * M.x p - M.pB p

/-- §3.3: seller surplus subtracts the seller's outside option. -/
def sellerSurplus (M : SecondBestBT.Mechanism) (p : ℝ × ℝ) : ℝ :=
  M.pS p - p.1 * M.x p

/-- Equation (15): money burnt is excluded from traders' surplus. -/
def tradersSurplus (M : SecondBestBT.Mechanism) (p : ℝ × ℝ) : ℝ :=
  buyerSurplus M p + sellerSurplus M p

/-- Equation (11): expected payment retained by neither trader. -/
def burntMoney (M : SecondBestBT.Mechanism) (p : ℝ × ℝ) : ℝ := M.pB p - M.pS p

/-- Equation (13), for general joint priors. -/
def gftPoint (M : SecondBestBT.Mechanism) (p : ℝ × ℝ) : ℝ := (p.2 - p.1) * M.x p

/-- Expected surplus for an arbitrary, potentially unbounded report interval.
For IR mechanisms the pointwise integrand is nonnegative, so this has the exact
extended expectation, including +∞. No finiteness or independence is imposed. -/
noncomputable def expectedSurplus (μ : Measure (ℝ × ℝ))
    (f : ℝ × ℝ → ℝ) : ENNReal := ∫⁻ p, ENNReal.ofReal (f p) ∂μ

/-- Real expected buyer surplus, used only with the finite-objective conclusions below. -/
noncomputable def buyerTS (μ : Measure (ℝ × ℝ)) (M : SecondBestBT.Mechanism) : ℝ :=
  ∫ p, buyerSurplus M p ∂μ

/-- Real expected seller surplus on the bounded instance. -/
noncomputable def sellerTS (μ : Measure (ℝ × ℝ)) (M : SecondBestBT.Mechanism) : ℝ :=
  ∫ p, sellerSurplus M p ∂μ

/-- Real expected total traders' surplus, for a joint law (not necessarily independent). -/
noncomputable def TS (μ : Measure (ℝ × ℝ)) (M : SecondBestBT.Mechanism) : ℝ :=
  ∫ p, tradersSurplus M p ∂μ

/-- Integrability is certified by theorem conclusions, never imposed on the competitor class.
This rules out the Bochner integral's default value for nonintegrable functions. -/
def FiniteObjectives (μ : Measure (ℝ × ℝ)) (M : SecondBestBT.Mechanism) : Prop :=
  Integrable M.pB μ ∧ Integrable M.pS μ ∧
  Integrable (buyerSurplus M) μ ∧ Integrable (sellerSurplus M) μ ∧
  Integrable (tradersSurplus M) μ ∧ Integrable (gftPoint M) μ

end MoneyBurningTrade.IndependentSurplus


