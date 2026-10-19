-- Prove2me | Definitions.Def_FBAComp_AmazonGain_Model
-- name    : FBAComp_AmazonGain_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:22.088561+00:00
-- url     : https://prove2.me/theorems/1e273157-f93f-4733-8006-98e3b2edc4c5
-- title:
--   §3–§4.1 — demands, profits, equilibria and fee problem (5)
-- statement:
--   The model has Amazon, a third-party seller and an OEM supplier. Parameters are market bases $Q_A,Q_S$, service value $\alpha$, cross-price sensitivity $\beta$, service qualities $s_A>s_S$, commission $r$, fulfillment cost $c$, OEM cost $c_0$, and seller product cost $g$. Cross-service sensitivity $\eta$ varies separately. Without FBA the demands are
--
--   $$q_{A,N}=Q_A-p_A+\beta p_S+\alpha s_A-\eta s_S,\qquad q_{S,N}=Q_S-p_S+\beta p_A+\alpha s_S-\eta s_A.$$
--
--   With FBA the seller receives service quality $s_A$ and pays fee $T$ per sale. The four demands and six profit functions are those of equations (1)–(4) and §4.1. Amazon and the seller choose retail prices simultaneously after the OEM chooses a wholesale price. With FBA, Amazon chooses a fee first to maximize its profit subject to seller participation. The gain is Amazon's FBA profit minus its no-FBA profit.
--
--   **Formalization Note.** All prices and fees are real, and linear demands are not truncated. The fee problem includes nonnegative seller sales to exclude an algebraic negative-sales branch. The standing parameter regime adds positive market bases and seller service quality, nonnegative unit costs, and the separate interior predicate requires positive no-FBA seller sales throughout $(0,\alpha)$.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), pp. 9–13, §3, §4.1, equations (1)–(5)

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_PriceGame

namespace FBAComp.AmazonGain

/-- Primitive parameters of the price-and-service model, §3, pp. 9–11. `η`, fees, wholesale
prices, and retail prices are decisions or varying sensitivities, so are not fields. -/
structure Params where
  QA : ℝ
  QS : ℝ
  α : ℝ
  β : ℝ
  sA : ℝ
  sS : ℝ
  r : ℝ
  c : ℝ
  c0 : ℝ
  g : ℝ

/-- The parameter regime of §3, pp. 9–11, with the positive-service and market-base
conditions used in the proof of Proposition 2, p. 38, and nonnegative unit costs. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.α ∧ P.α < 1 ∧ 0 < P.β ∧ P.β < 1 ∧ 0 < P.r ∧ P.r < 1 ∧
  0 < P.sS ∧ P.sS < P.sA ∧ 0 < P.QA ∧ 0 < P.QS ∧
  0 ≤ P.c ∧ 0 ≤ P.c0 ∧ 0 ≤ P.g

/-- Amazon's demand without FBA, equation (1), p. 10. -/
def qAN (P : Params) (η pA pS : ℝ) : ℝ :=
  P.QA - pA + P.β * pS + P.α * P.sA - η * P.sS

/-- The seller's demand without FBA, equation (2), p. 10. -/
def qSN (P : Params) (η pA pS : ℝ) : ℝ :=
  P.QS - pS + P.β * pA + P.α * P.sS - η * P.sA

/-- Amazon's demand with FBA, equation (3), p. 10. -/
def qAF (P : Params) (η pA pS : ℝ) : ℝ :=
  P.QA - pA + P.β * pS + P.α * P.sA - η * P.sA

/-- The seller's demand with FBA, equation (4), p. 10. -/
def qSF (P : Params) (η pA pS : ℝ) : ℝ :=
  P.QS - pS + P.β * pA + P.α * P.sA - η * P.sA

/-- Amazon's no-FBA profit, §4.1, p. 12. -/
def profitAN (P : Params) (η w pA pS : ℝ) : ℝ :=
  (pA - w - P.c) * qAN P η pA pS + P.r * pS * qSN P η pA pS

/-- The seller's no-FBA profit, §4.1, p. 12. -/
def profitSN (P : Params) (η pA pS : ℝ) : ℝ :=
  ((1 - P.r) * pS - P.g - P.c) * qSN P η pA pS

/-- The OEM's no-FBA profit, §4.1, p. 12. -/
def profitMN (P : Params) (η w pA pS : ℝ) : ℝ :=
  (w - P.c0) * qAN P η pA pS

/-- Amazon's FBA profit, §4.1, p. 13. -/
def profitAF (P : Params) (η T w pA pS : ℝ) : ℝ :=
  (pA - w - P.c) * qAF P η pA pS + (P.r * pS + T - P.c) * qSF P η pA pS

/-- The seller's FBA profit, §4.1, p. 13. -/
def profitSF (P : Params) (η T pA pS : ℝ) : ℝ :=
  ((1 - P.r) * pS - P.g - T) * qSF P η pA pS

/-- The OEM's FBA profit, §4.1, p. 13. -/
def profitMF (P : Params) (η w pA pS : ℝ) : ℝ :=
  (w - P.c0) * qAF P η pA pS

/-- Simultaneous retail-price Nash equilibrium without FBA, §4.1, p. 12. -/
def IsPriceNE_N (P : Params) (η w pA pS : ℝ) : Prop :=
  (PriceGame.mk (profitAN P η w) (profitSN P η)).IsNash pA pS

/-- No-FBA subgame-perfect outcome: the OEM chooses `w` anticipating the price Nash
equilibrium, §3 p. 11 and §4.1 p. 12. -/
def IsEqN (P : Params) (η w pA pS : ℝ) : Prop :=
  IsPriceNE_N P η w pA pS ∧
  ∀ w' pA' pS', IsPriceNE_N P η w' pA' pS' →
    profitMN P η w' pA' pS' ≤ profitMN P η w pA pS

/-- Simultaneous retail-price Nash equilibrium with FBA at fee `T`, §4.1, p. 13. -/
def IsPriceNE_F (P : Params) (η T w pA pS : ℝ) : Prop :=
  (PriceGame.mk (profitAF P η T w) (profitSF P η T)).IsNash pA pS

/-- FBA subgame outcome after Amazon fixes fee `T`, §3 p. 11 and §4.1 p. 13. -/
def IsSubgameEqF (P : Params) (η T w pA pS : ℝ) : Prop :=
  IsPriceNE_F P η T w pA pS ∧
  ∀ w' pA' pS', IsPriceNE_F P η T w' pA' pS' →
    profitMF P η w' pA' pS' ≤ profitMF P η w pA pS

/-- Amazon's fee problem (5), §4.1, p. 13. The seller must earn at least its no-FBA
benchmark `ΠSN0`. The added nonnegative-sales clause excludes negative-sales equilibria
that the algebraic participation inequality alone admits. -/
def IsFeeOptimal (P : Params) (η benchmark T w pA pS : ℝ) : Prop :=
  IsSubgameEqF P η T w pA pS ∧
  benchmark ≤ profitSF P η T pA pS ∧ 0 ≤ qSF P η pA pS ∧
  ∀ T' w' pA' pS', IsSubgameEqF P η T' w' pA' pS' →
    benchmark ≤ profitSF P η T' pA' pS' → 0 ≤ qSF P η pA' pS' →
    profitAF P η T' w' pA' pS' ≤ profitAF P η T w pA pS

/-- Unconstrained Amazon fee maximizer in the FBA subgame, used in the proof of
Lemma A.3, p. 35, to define the paper's unprinted `T̃`. -/
def IsUnconstrainedFeeOptimal (P : Params) (η T w pA pS : ℝ) : Prop :=
  IsSubgameEqF P η T w pA pS ∧
  ∀ T' w' pA' pS', IsSubgameEqF P η T' w' pA' pS' →
    profitAF P η T' w' pA' pS' ≤ profitAF P η T w pA pS

/-- Amazon's gain from FBA at given no-FBA and FBA outcomes, Proposition 2, p. 19. -/
def gain (P : Params) (η wN pAN pSN T wF pAF pSF : ℝ) : ℝ :=
  profitAF P η T wF pAF pSF - profitAN P η wN pAN pSN

/-- Added interior condition: for every `η ∈ (0, α)`, the seller's no-FBA
equilibrium sales are positive. It excludes the negative-sales branch of participation
used implicitly in Proposition 1 and Lemma A.3, pp. 18, 35–37. -/
def Interior (P : Params) : Prop :=
  ∀ η ∈ Set.Ioo 0 P.α, ∀ w pA pS,
    IsEqN P η w pA pS → 0 < qSN P η pA pS

end FBAComp.AmazonGain


