-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_IntervalSelection
-- name    : ConsistentSubmodular_Randomized_AdaptivityGap_IntervalSelection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:12.004217+00:00
-- url     : https://prove2.me/theorems/44436819-5bc1-4939-aaa2-8989683b3dc4
-- title:
--   Interval instance of a window instance (proof of Lemma 2)
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$ (where $m$ is `W.lastStage`), objective $f$, arrival prefixes $R_0=\emptyset\subseteq R_1\subseteq\dots\subseteq R_m$, and candidates $O_0,\dots,O_m$. Let $p\in\Delta$ be a point of the simplex on $\{0,\dots,m\}$ together with a proof that $p$ is in the simplex (nonnegative entries summing to $1$).
--
--   - `windowIntervals W p hp` is the interval-selection instance with indices $0,\dots,m$ in which candidate $i$ gives the interval
--   $$[\ell_i, r_i] = [\,f(R_i),\; f(O_i\cup R_i)\,],$$
--   that is, the left endpoint is the value $f(R_i)$ of the arrivals alone and the right endpoint is the benchmark of stage $i$, and in which the probability distribution on the indices is $p$. The required conditions hold: $\ell_i\ge 0$ because $f$ is nonnegative, $\ell_i\le r_i$ because $f$ is monotone and $R_i\subseteq O_i\cup R_i$, and $p$ is a probability distribution.
--
--   This is the interval instance that appears in the proof of Lemma 2, which reduces the existence of addition-robust distributions to a lower bound on the adaptivity gap of interval selection.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/IntervalSelection.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_Minimax

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.IntervalSelection

section Window

variable {n : ℕ} (W : WindowInstance n)

/-- The interval instance in the proof of Lemma 2: candidate `i` gives the
interval `[f(R_i), f(O_i ∪ R_i)]`, and `p` is a distribution on the stages. -/
def windowIntervals (p : Point W.lastStage) (hp : IsSimplex p) : IntervalInstance W.lastStage where
  left i := W.objective.value (W.arrivals i)
  right i := W.benchmark i
  prob := p
  left_nonneg _ := W.objective.nonnegative _
  left_le_right _ := W.objective.monotone _ _ Finset.subset_union_right
  prob_nonneg := hp.1
  prob_sum := hp.2

end Window

end ConsistentSubmodular.IntervalSelection

end


