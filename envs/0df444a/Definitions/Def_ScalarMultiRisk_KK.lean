-- Prove2me | Definitions.Def_ScalarMultiRisk_KK
-- name    : ScalarMultiRisk_KK
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:38.812584+00:00
-- url     : https://prove2.me/theorems/bcee733a-1a5e-421e-8674-85f2b8d0560e
-- title:
--   The set $\mathbb K_t=\sum_{s=t}^T L^\infty_s(K_s)$
-- statement:
--   $\mathbb K_t=\sum_{s=t}^T L^\infty_s(K_s)$ is the Minkowski sum of the bounded $\mathcal F_s$-measurable selections of the cones $K_s$, for $s=t,\dots,T$. It is the set of portfolio changes available by trading from time $t$ on.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 3.1, p.7

import Mathlib
import Definitions.Def_ScalarMultiRisk_Market
import Definitions.Def_ScalarMultiRisk_Linfty

open MeasureTheory

namespace ScalarMultiRisk

/-- **The set `𝕂_t`.** arXiv:1807.10694v5, Definition 3.1, p.7: `𝕂_t = ∑_{s=t}^T L∞_s(K_s)`, the
Minkowski sum of the `F_s`-measurable bounded selections of the `K_s`.

**Formalization Note.** The Minkowski sum is taken on a.e.-classes. -/
def KK {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d) (t : Fin (T + 1)) :
    Set (Ω → Fin d → ℝ) :=
  {k | ∃ f : Fin (T + 1) → Ω → Fin d → ℝ,
    (∀ s, t ≤ s → f s ∈ Linfty A.toFilteredSpace s fun ω => (A.K s ω : Set (Fin d → ℝ))) ∧
      k =ᵐ[A.P] ∑ s ∈ Finset.Ici t, f s}

end ScalarMultiRisk


