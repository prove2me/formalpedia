-- Prove2me | Definitions.Def_OutcomeRebate_Transfer_Supplement_CorrelatedBenefit
-- name    : OutcomeRebate_Transfer_Supplement_CorrelatedBenefit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:02:02.849385+00:00
-- url     : https://prove2.me/theorems/1d729792-d7ac-45d7-9337-62438c5b1900
-- title:
--   Appendix F — payer benefit kv, coverage response and equilibrium
-- statement:
--   The published patient model is unchanged. Let $k>0$ and replace the payer's constant benefit on success by $kv$, where the patient's success value is $v$. Write $S_U(\bar\beta,p)$ and $S_O(\bar\beta,p)$ for the published buyer sets. The new payer payoffs are
--
--   $$\Pi^U_{payer}=\frac n{\bar v}\int_{S_U(\bar\beta,p)}[q(kv-(1-\bar\beta)p)-(1-q)(1-\bar\beta)p]\,dv,$$
--   $$\Pi^O_{payer}=\frac n{\bar v}\int_{S_O(\bar\beta,p)}q(kv-(1-\bar\beta)p)\,dv.$$
--
--   Add the published patient payoff for each system to obtain its payer objective. Cover precisely when that objective is weakly greater with coverage than without. The share is then $\beta$ or $1$, and realized firm profit uses the published firm-profit function at that share. An equilibrium price maximizes it over all nonnegative prices. The old record coordinate $v'$ is unused.
--
--   This file also defines the exact constants of Theorems 4 and 5:
--
--   $$A=\frac{2}{\beta qz}\frac{\bar v+c\beta z}{3\bar v+c\beta z},\quad B=\frac{2}{q(\beta z+\bar v/\max\{c,\bar v/z\})},$$
--   $$A'=\frac2\beta\frac{\bar vq+\beta c}{3\bar vq+\beta c},\quad B'=\frac2{\beta+\bar v/\max\{c/q,\bar v\}},$$
--   $$\hat p_1=\frac{\bar vq(k+1)}{2-\beta zq(k+1)},\qquad \hat p_2=\frac{\bar v(k+1)}{2-\beta(k+1)}.$$
--
--   Quotient prices are used only in branches guaranteeing positive denominators. Appendix F.2's stray $z$ in outcome-based demand is read in agreement with §3.2.1 and its own profit formula: the published outcome-based buyers and demand have no $z$.
-- source:
--   Adida, Outcome-based pricing for new pharmaceuticals via rebates, accepted manuscript (Management Science, accepted Dec. 2019; eScholarship 0702h9wp), pp. 47–49 (PDF 48–50), Appendix F.1–F.2

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer.Supplement

open MeasureTheory

/-- Appendix F changes only the payer's benefit, to kv. P.vp is unused. -/
noncomputable def payerPayoffKU (P : Params) (k bb p : ℝ) : ℝ :=
  P.n / P.vbar * ∫ v in buyersU P bb p,
    (P.q * (k * v - (1 - bb) * p) - (1 - P.q) * (1 - bb) * p)
noncomputable def payerPayoffKO (P : Params) (k bb p : ℝ) : ℝ :=
  P.n / P.vbar * ∫ v in buyersO P bb p, P.q * (k * v - (1 - bb) * p)
noncomputable def payerObjKU (P : Params) (k bb p : ℝ) : ℝ :=
  payerPayoffKU P k bb p + patientPayoffU P bb p
noncomputable def payerObjKO (P : Params) (k bb p : ℝ) : ℝ :=
  payerPayoffKO P k bb p + patientPayoffO P bb p
def coversKU (P : Params) (k p : ℝ) : Prop := payerObjKU P k 1 p ≤ payerObjKU P k P.β p
def coversKO (P : Params) (k p : ℝ) : Prop := payerObjKO P k 1 p ≤ payerObjKO P k P.β p
open Classical in
noncomputable def shareKU (P : Params) (k p : ℝ) : ℝ := if coversKU P k p then P.β else 1
open Classical in
noncomputable def shareKO (P : Params) (k p : ℝ) : ℝ := if coversKO P k p then P.β else 1
noncomputable def realizedProfitKU (P : Params) (k p : ℝ) : ℝ := firmProfitU P (shareKU P k p) p
noncomputable def realizedProfitKO (P : Params) (k p : ℝ) : ℝ := firmProfitO P (shareKO P k p) p
def IsEqPriceKU (P : Params) (k p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ p' : ℝ, 0 ≤ p' → realizedProfitKU P k p' ≤ realizedProfitKU P k p
def IsEqPriceKO (P : Params) (k p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ p' : ℝ, 0 ≤ p' → realizedProfitKO P k p' ≤ realizedProfitKO P k p
noncomputable def thresholdA (P : Params) : ℝ :=
  (2 / (P.β * P.q * P.z)) * (P.vbar + P.c * P.β * P.z) / (3 * P.vbar + P.c * P.β * P.z)
noncomputable def thresholdB (P : Params) : ℝ :=
  2 / (P.q * (P.β * P.z + P.vbar / max P.c (P.vbar / P.z)))
noncomputable def thresholdAPrime (P : Params) : ℝ :=
  (2 / P.β) * (P.vbar * P.q + P.β * P.c) / (3 * P.vbar * P.q + P.β * P.c)
noncomputable def thresholdBPrime (P : Params) : ℝ :=
  2 / (P.β + P.vbar / max (P.c / P.q) P.vbar)
noncomputable def pHat1 (P : Params) (k : ℝ) : ℝ :=
  P.vbar * P.q * (k + 1) / (2 - P.β * P.z * P.q * (k + 1))
noncomputable def pHat2 (P : Params) (k : ℝ) : ℝ :=
  P.vbar * (k + 1) / (2 - P.β * (k + 1))

end OutcomeRebate.Transfer.Supplement


