-- Prove2me | Definitions.Def_RobustFcstAgg_InfoStruct
-- name    : RobustFcstAgg_InfoStruct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:02.428658+00:00
-- url     : https://prove2.me/theorems/7e3a28bf-7e3e-4026-a9f0-2131b0b53340
-- title:
--   Partial-information instance $\mathcal D=(\mathcal D_T)_T$
-- statement:
--   A **partial-information instance** is a family $\mathcal D=(\mathcal D_T)_{\emptyset\ne T\subseteq[n]}$ of probability measures on $\mathbb R$, the laws of the signals $X_T$, such that for every $T$
--   $$\mathbb E_{\mathcal D}[X_T]=0,\qquad \mathrm{Var}_{\mathcal D}(X_T)=\mathbb E_{\mathcal D}[X_T^2]<\infty,$$
--   and $\mathrm{Var}_{\mathcal D}(X_T)>0$ for at least one $T$.
--
--   This is the class over which the worst-case error is taken. No other condition is imposed: the laws may be atomic, singular, Gaussian or point masses.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib
import Definitions.Def_RobustFcstAgg_Subs
open MeasureTheory

namespace RobustFcstAgg

/-- **Partial-information instance `D = (D_T)_T`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7: `X_T` is drawn from `D_T`,
with `E[X_T] = 0`, `E[X_T²] < ∞`, and some `T` with `Var(X_T) > 0`.

**Formalization Note.** No other condition is imposed: the laws may be atomic, singular, or a Dirac.
Independence of the signals is carried by `InfoStruct.jointLaw`, the product measure. -/
structure InfoStruct (n : ℕ) where
  /-- The law `D_T` of the signal `X_T`. -/
  law : Subs n → Measure ℝ
  isProb : ∀ T, IsProbabilityMeasure (law T)
  memLp : ∀ T, MemLp id 2 (law T)
  mean_zero : ∀ T, ∫ x, x ∂law T = 0
  nondeg : ∃ T, 0 < ∫ x, x ^ 2 ∂law T

instance InfoStruct.instIsProbabilityMeasureLaw {n : ℕ} (D : InfoStruct n) (T : Subs n) :
    IsProbabilityMeasure (D.law T) := D.isProb T

end RobustFcstAgg


