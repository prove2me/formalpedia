-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ShadowIntervals
-- name    : ConsistentSubmodular_Randomized_AdaptivityGap_ShadowIntervals
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:38.285042+00:00
-- url     : https://prove2.me/theorems/2f8a259d-5898-4077-89fa-1b01a5e95305
-- title:
--   Value in hindsight and the left-endpoint law of an interval-selection instance
-- statement:
--   Let $I$ be an interval-selection instance with intervals $[\ell_j,r_j]$ and probabilities $p_j$, $j\in\{0,\dots,N\}$, and let $v(i,j)=\ell_j+|[\ell_i,r_i]\cap[\ell_j,\infty)|$ be the value of interval $i$ at realization $j$.
--
--   - `hindsight` $I\,j$: the value in hindsight $\max_iv(i,j)=\ell_j+d_j$, the right endpoint of the shadow interval $\hat I_j$; defined as the maximum over $i$ of $v(i,j)$.
--   - `leftLaw` $I$: the `LeftLaw` of the random left endpoint $\ell_J$, $J\sim p$, with weights $p_j$, endpoints $\ell_j$, and `low` the smallest left endpoint $\ell_j$ among indices with $p_j\ne0$, so that zero-probability realizations play no role.
--
--   The file also proves that the set of indices of positive probability is nonempty (since $\sum_jp_j=1$), which makes `low` well defined.
--
--   These definitions connect interval-selection instances to the law of the random left endpoint and its distribution function, ramp and inverse, which are used to analyze the shadow intervals and the adaptivity gap in Appendix A.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ShadowIntervals.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Shadow

variable {N : ℕ} (I : IntervalInstance N)

/-- The value in hindsight `max_i v(i, j) = ℓ_j + d_j`, the right endpoint of the shadow
interval `Î_j`. -/
def hindsight (j : Fin (N + 1)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => I.value i j

theorem support_nonempty : (Finset.univ.filter fun j => I.prob j ≠ 0).Nonempty := by
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := I.prob)
    (by rw [I.prob_sum]; exact one_ne_zero)
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩

/-- The law of the random left endpoint `ℓ_J`, `J ∼ p`. Its smallest point is the smallest left
endpoint of positive probability, so zero-probability realizations play no role. -/
def leftLaw : LeftLaw (Fin (N + 1)) where
  prob := I.prob
  left := I.left
  low := (Finset.univ.filter fun j => I.prob j ≠ 0).inf' (support_nonempty I) I.left
  prob_nonneg := I.prob_nonneg
  prob_sum := I.prob_sum
  low_le j hj := Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  atom := by
    obtain ⟨j, hj, hjl⟩ := Finset.exists_mem_eq_inf' (support_nonempty I) I.left
    exact ⟨j, (Finset.mem_filter.mp hj).2, hjl.ge⟩

end ConsistentSubmodular.Shadow

end


