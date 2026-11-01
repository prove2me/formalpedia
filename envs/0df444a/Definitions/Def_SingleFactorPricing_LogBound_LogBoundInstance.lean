-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_LogBoundInstance
-- name    : SingleFactorPricing_LogBound_LogBoundInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:00.380195+00:00
-- url     : https://prove2.me/theorems/c649a45a-96f5-4d6a-865e-ed40f296a390
-- title:
--   The hypotheses of Theorem 1
-- statement:
--   The data $(\mu,d,f,\bar p,q_{\min},q_{\max},\mathcal R^f)$ form an **instance of Theorem 1** when
--
--   1. demand is non-negative at every $p\ge0$ (p.2);
--   2. $f$ is a positive vector (p.3);
--   3. A0 holds for $\bar p$, including its optimality (p.3);
--   4. A1 holds (p.4);
--   5. the regularity in the type holds (remark on p.5);
--   6. $q_{\min}>0$, and $q_{\min},q_{\max}$ are the infimum and supremum of the ratios $\bar p_{t,i}/f_i$ (p.4 and the remark on p.5);
--   7. $\mathcal R^f$ is the supremum of $R(qf)$ over $q>0$ (p.3).
--
--   Gathering them in one predicate lets the bound and its tightness be stated about exactly the same class of objects.
--
--   **Formalization Note** $0<q_{\min}$ is listed because it does not follow from pointwise positivity over an infinite type space; it is the p.5 condition that $q_{\min}$ is bounded away from zero. For finitely many types A0 gives it.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, pp.2–5

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_AssumptionA0
import Definitions.Def_SingleFactorPricing_LogBound_AssumptionA1
import Definitions.Def_SingleFactorPricing_LogBound_priceRatios
import Definitions.Def_SingleFactorPricing_LogBound_IsSingleFactorOptimum
import Definitions.Def_SingleFactorPricing_LogBound_TypeRegularity

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **The hypotheses of Theorem 1, with the objects they fix.** Gallego, Berbeglia,
arXiv:2102.03038v2, §2, pp.2–5: non-negative demand (p.2), a positive vector `f` (p.3), optimal
prices under A0 (p.3), A1 (p.4), `q_min` and `q_max` (p.4), `Rᶠ` (p.3), and for a general type space
the remark on p.5.

**Formalization Note.** Non-negativity is for `p ≥ 0` only. `0 < qmin` is a hypothesis because for
an infinite type space it does not follow from pointwise positivity; it is the p.5 condition "`q_min`
is bounded away from zero". For finitely many types it follows from A0. -/
structure LogBoundInstance {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (pbar : T → N → ℝ) (qmin qmax Rf : ℝ) : Prop where
  /-- "We assume that all demand functions are non-negative." -/
  demand_nonneg : ∀ t (p : N → ℝ), (∀ i, 0 ≤ p i) → ∀ i, 0 ≤ d t p i
  /-- `f` is a positive vector. -/
  factor_pos : ∀ i, 0 < f i
  /-- A0, with the optimality of `pbar`. -/
  a0 : AssumptionA0 d pbar
  /-- A1. -/
  a1 : AssumptionA1 μ d f pbar
  /-- Regularity in the type. -/
  regular : TypeRegularity μ d f pbar
  /-- `q_min` is bounded away from zero. -/
  qmin_pos : 0 < qmin
  /-- `q_min` is the infimum of the ratios `p̄_ij/f_i`. -/
  isGLB_qmin : IsGLB (priceRatios f pbar) qmin
  /-- `q_max` is the supremum of the ratios `p̄_ij/f_i`. -/
  isLUB_qmax : IsLUB (priceRatios f pbar) qmax
  /-- `Rf` is `Rᶠ`. -/
  isOptimum : IsSingleFactorOptimum μ d f Rf

end SingleFactorPricing.LogBound


