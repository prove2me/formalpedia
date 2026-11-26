-- Prove2me | Definitions.Def_MarketMakerAds_Supplement_RiskFamily
-- name    : MarketMakerAds_Supplement_RiskFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:31:52.600267+00:00
-- url     : https://prove2.me/theorems/f18f0f0e-5b82-550a-b041-abee130cda45
-- title:
--   The utility model shared by all populations (mean-variance or CARA)
-- statement:
--   Under heterogeneous risk aversion all buyers use the **same utility model**, either the mean-variance model or the CARA model, but each population has its own risk-aversion parameter. A **risk family** is one of the two models; the family together with a parameter $\theta$ gives the risk model with parameter $\beta=\theta$ (mean-variance) or $\alpha=\theta$ (CARA).
--
--   This is what lets a market with $k$ populations be described by one family and $k$ parameters $\theta_1\le\cdots\le\theta_k$, as in §6 of the paper.
--
--   **Formalization Note** A two-constructor type with a map to the published risk models; a market mixing CARA and mean-variance populations, which §6 does not consider, cannot be expressed.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, §6, p.19 (k populations with α1 ≤ … ≤ αk, resp. β1 ≤ … ≤ βk)

import Mathlib
import Definitions.Def_MarketMakerAds_RiskModel

namespace MarketMakerAds

namespace Supplement

/-- **The model family shared by all populations** (mean-variance or CARA).
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, §6, p.19: "We
assume that there are k populations of buyers with α1 ≤ α2 ≤ … ≤ αk (resp. β1 ≤ β2 ≤ … ≤ βk) for
CARA (resp. Mean-variance)": every population uses the same utility model, with its own parameter.

`RiskFamily.toModel fam θ` is the published `RiskModel` of the family `fam` with parameter `θ`
(`.meanVariance θ`, resp. `.cara θ`).

**Formalization Note** The family is a two-constructor type, so a heterogeneous market is one family
plus one parameter per population; mixing CARA and mean-variance populations, which §6 does not
consider, cannot be expressed. -/
inductive RiskFamily
  /-- All populations use the mean-variance model; the parameter is `β`. -/
  | meanVariance
  /-- All populations use the CARA model; the parameter is `α`. -/
  | cara
  deriving DecidableEq

/-- The risk model of the family `fam` with parameter `θ` (`β` for mean-variance, `α` for CARA). -/
def RiskFamily.toModel : RiskFamily → ℝ → RiskModel
  | .meanVariance, θ => .meanVariance θ
  | .cara, θ => .cara θ

end Supplement

end MarketMakerAds


