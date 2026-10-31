-- Prove2me | Definitions.Def_ScalarMultiRisk_priceSet
-- name    : ScalarMultiRisk_priceSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:51.627445+00:00
-- url     : https://prove2.me/theorems/d2a64c96-58fb-4a85-a713-52ee5a43a379
-- title:
--   The set $\mathcal S$ of eligible pricing processes, (4.3)
-- statement:
--   $\mathcal S$ is the set of processes $S=(S_t)_{t=0}^T$ with $S_t\in L^\infty_t(K_t^+)$ such that for all $t$ and all $i\in\{2,\dots,d\}$,
--
--   $$S_{t,1}=1,\qquad\|S_{t,i}\|_\infty\le\max\{\|e_i\|_{\mathbb K_T,0},1\}.$$
--
--   These are the bounded price processes in units of the cash asset that are consistent with the cones.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, (4.3), p.18

import Mathlib
import Definitions.Def_ScalarMultiRisk_pointwiseDual
import Definitions.Def_ScalarMultiRisk_normKK
import Definitions.Def_ScalarMultiRisk_Linfty

open MeasureTheory

namespace ScalarMultiRisk

/-- **The set `𝒮` of eligible pricing processes.** arXiv:1807.10694v5, (4.3), p.18:
`𝒮 := {S ∈ ∏_{t=0}^T L∞_t(K_t⁺) | ∀ t = 0, …, T, ∀ i ∈ {2, …, d} : S_{t,1} = 1,
‖S_{t,i}‖_∞ ≤ max{‖e_i‖_{𝕂_T,0}, 1}}`.

**Formalization Note.** `S_{t,1} = 1` holds a.s., and the essential-supremum bound is the same
as the a.s. bound. Asset 1 is index `0`; `i ∈ {2, …, d}` is `i ≠ 0`. -/
def priceSet {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d] (A : Market Ω T d) :
    Set (Fin (T + 1) → Ω → Fin d → ℝ) :=
  {S | ∀ t, S t ∈ Linfty A.toFilteredSpace t (pointwiseDual A t) ∧
    (∀ᵐ ω ∂A.P, S t ω 0 = 1) ∧
    ∀ i : Fin d, i ≠ 0 → ∀ᵐ ω ∂A.P, |S t ω i| ≤ max (normKK A i) 1}

end ScalarMultiRisk


