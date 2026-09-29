-- Prove2me | Definitions.Def_klucbFailureCount
-- name    : klucbFailureCount
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-07-29T02:25:48.296399+00:00
-- url     : https://prove2.me/theorems/ee964fd6-ab36-42b6-984e-45dcaf60f3c0
-- title:
--   KL-UCB selected-round failure counts
-- statement:
--   For a fixed optimal arm $a$, a comparison arm $i$, a horizon $n$, and a tolerance $\varepsilon>0$, this definition records the two selected-round counts used in the finite-time KL-UCB analysis.
--
--   At each round, let $U_j(t-1)$ be the KL-UCB index of arm $j$ computed from the preceding history, and let $\mu^\star$ be the optimal mean. The first component counts selections of arm $i$ made either during initialization or while
--
--   $$
--   U_a(t-1)\le \mu^\star-\varepsilon.
--   $$
--
--   The second component counts selections of arm $i$ after initialization for which
--
--   $$
--   \mu^\star-\varepsilon\le U_i(t-1).
--   $$
--
--   These counts provide a reusable formal version of the good-index/bad-index split in the proof of Theorem 10.6.
--
--   **Formalization Note** Each round uses the canonical prefix of the completed finite history, so the index depends only on observations available before that round. Both components are real-valued finite sums of indicator functions.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press, 2020, proof of Theorem 10.6, printed pp. 139–140; the split is the displayed chain bounding E[T_i(n)] by the optimal-index and suboptimal-index failure terms.

import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_banditHistoryPrefix

/-!
Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), proof of
Theorem 10.6, printed pp. 139--140.

For a fixed optimal arm `a` and suboptimal arm `i`, pulls of `i` are split
between rounds before all arms are initialized or on which the optimal index
is too low, and initialized rounds on which the selected suboptimal index
crosses the threshold `μ* - ε`.
-/

namespace BanditAlgorithm

/-- The two selected-round failure counts in the KL-UCB proof of
Theorem 10.6: initialization/optimal-index underestimation, and
selected-suboptimal-index overshoot. -/
noncomputable def klucbFailureCount {k n : ℕ}
    (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) : ℝ × ℝ :=
  let initialized := fun r : Fin n ↦
    ∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0
  let lowSelected := ∑ r : Fin n,
    if (h r).1 = i ∧
        (¬ initialized r ∨
          klucbIndex a (banditHistoryPrefixAt h r) ≤
            banditOptimalMean ν - ε) then (1 : ℝ) else 0
  let highSelected := ∑ r : Fin n,
    if initialized r ∧
        banditOptimalMean ν - ε ≤
          klucbIndex i (banditHistoryPrefixAt h r) ∧
        (h r).1 = i then (1 : ℝ) else 0
  (lowSelected, highSelected)

end BanditAlgorithm


