-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_essOscLog
-- name    : GraphNNSphere_Supplement_essOscLog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:43:00.586778+00:00
-- url     : https://prove2.me/theorems/7fcb261b-7067-4187-bbb2-97be010d19cc
-- title:
--   Essential oscillation $\operatorname{ess\,osc}_A\log f$
-- statement:
--   For a measurable set $A\subseteq S^{d-1}$, the **essential oscillation** of $\log f$ on $A$ is
--
--   $$\operatorname{ess\,osc}_A\log f=\operatorname*{ess\,sup}_A\log f-\operatorname*{ess\,inf}_A\log f,$$
--
--   with respect to surface measure restricted to $A$. A bound $\operatorname{ess\,osc}_A\log f\le\kappa d$ says that $f$ varies by at most a factor $e^{\kappa d}$ on $A$, after sets of surface measure zero are ignored.
--
--   **Formalization Note** The value is an extended real, with $\log 0=-\infty$. If $f$ vanishes on a part of $A$ of positive measure, or $\log f$ is essentially unbounded below there, the oscillation is $+\infty$. On a null set the oscillation is $-\infty$ (empty essential range), so a bound holds vacuously.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.5, p.18

import Mathlib
import Definitions.Def_GraphNNSphere_unif

open MeasureTheory

namespace GraphNNSphere

namespace Supplement

/-- `log f` with values in the extended reals, `log 0 = -∞` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §2.5, p.18). -/
noncomputable def logE {d : ℕ} (f : Sph d → ℝ) (x : Sph d) : EReal :=
  if f x ≤ 0 then ⊥ else ((Real.log (f x) : ℝ) : EReal)

/-- The essential oscillation `ess osc_A log f = ess sup_A log f - ess inf_A log f` with respect to
`σ_{d-1}` restricted to `A` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §2.5, p.18).

**Formalization Note** The value is in `EReal`. If `f` vanishes on a subset of `A` of positive
measure, or `log f` is essentially unbounded below on `A`, the essential infimum is `-∞` and the
oscillation is `+∞`. On a null set `A` it is `-∞` (empty essential range), so a bound on it
holds vacuously. -/
noncomputable def essOscLog (d : ℕ) (f : Sph d → ℝ) (A : Set (Sph d)) : EReal :=
  if unif d A = 0 then ⊥
  else if essInf (logE f) ((unif d).restrict A) = ⊥ then ⊤
  else essSup (logE f) ((unif d).restrict A) - essInf (logE f) ((unif d).restrict A)

end Supplement

end GraphNNSphere


