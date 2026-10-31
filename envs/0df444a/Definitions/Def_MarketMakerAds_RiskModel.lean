-- Prove2me | Definitions.Def_MarketMakerAds_RiskModel
-- name    : MarketMakerAds_RiskModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:00.973704+00:00
-- url     : https://prove2.me/theorems/a7330dea-737a-46a9-9328-e2672c9c4180
-- title:
--   Risk-aversion models of the buyers (mean-variance $\beta$ or CARA $\alpha$)
-- statement:
--   All buyers share one **risk-aversion model**, one of two:
--
--   1. the **mean-variance** model with parameter $\beta$, and
--   2. the **CARA** (constant absolute risk aversion) model with parameter $\alpha$.
--
--   The paper's standing range is $\alpha\ge0$ and $\beta\ge0$. Three parameter ranges are named:
--
--   - *nonnegative*: $\beta\ge0$, resp. $\alpha\ge0$ (the paper's range, used for Theorems 1 and 2);
--   - *admissible*: $\beta\ge0$, resp. $\alpha>0$ (the range on which the Market-Maker price $p^*_M=\frac1\alpha\log\mathbf E[e^{\alpha p}]$ is defined);
--   - *positive*: $\beta>0$, resp. $\alpha>0$.
--
--   Every utility of the paper is then one function of the model.
--
--   **Formalization Note** The model is an inductive type with two constructors; the three ranges are predicates on it.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, §3.3, p.12, eq. (1) and the sentence below it

import Mathlib

namespace MarketMakerAds

/-- **Risk-aversion model of the buyers** (mean-variance with parameter `β`, or CARA with
parameter `α`).
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, §3.3, p.12,
eq. (1): "We consider two popular utility models to capture buyers' risk aversion … where α ≥ 0
and β ≥ 0 are the parameters of each model".

All buyers share one model (homogeneous risk aversion, §5, p.15).

**Formalization Note** The two models are one inductive type, so every utility is one function
of the model (`riskUtility`). The parameter ranges are the predicates below. -/
inductive RiskModel
  /-- Mean-variance model with risk-aversion parameter `β`. -/
  | meanVariance (β : ℝ)
  /-- CARA (constant absolute risk aversion) model with parameter `α`. -/
  | cara (α : ℝ)

namespace RiskModel

/-- The paper's standing parameter range "α ≥ 0 and β ≥ 0" (p.12, below eq. (1)). -/
def IsNonneg : RiskModel → Prop
  | meanVariance β => 0 ≤ β
  | cara α => 0 ≤ α

/-- The range on which the Market-Maker price `p*_M` of eq. (3), p.17, is defined:
`β ≥ 0` for mean-variance and `α > 0` for CARA (eq. (3) divides by `α`). -/
def IsAdmissible : RiskModel → Prop
  | meanVariance β => 0 ≤ β
  | cara α => 0 < α

/-- Strictly positive risk aversion: `β > 0`, resp. `α > 0`. -/
def IsPositive : RiskModel → Prop
  | meanVariance β => 0 < β
  | cara α => 0 < α

end RiskModel

end MarketMakerAds


