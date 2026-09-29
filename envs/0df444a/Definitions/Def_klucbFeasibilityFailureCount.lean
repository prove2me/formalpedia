-- Prove2me | Definitions.Def_klucbFeasibilityFailureCount
-- name    : klucbFeasibilityFailureCount
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-07-29T04:17:05.175208+00:00
-- url     : https://prove2.me/theorems/9a05dff3-bbe6-4bc2-b051-084a52076dbf
-- title:
--   KL-UCB feasibility failure counts
-- statement:
--   Fix a Bernoulli bandit, an optimal arm $a$, a candidate suboptimal arm $i$, and a tolerance $\varepsilon>0$. For every decision round $r$, let $H_r$ be the history available before the arm at round $r$ is selected, let $N_j(r)$ and $\widehat\mu_j(r)$ denote the pull count and empirical mean of arm $j$ in $H_r$, and put $q=\mu^\star-\varepsilon$.
--
--   The definition returns two selected-round counts. The first counts rounds on which arm \(i\) is selected and either initialization is incomplete or the optimal arm fails the one-sided KL feasibility test,
--
--   $$
--   \frac{\log f(r+1)}{N_a(r)}
--   <
--   \overline d\!\left(\widehat\mu_a(r),q\right).
--   $$
--
--   The second counts initialized rounds on which arm \(i\) is selected and that arm passes the corresponding threshold test,
--
--   $$
--   \overline d\!\left(\widehat\mu_i(r),q\right)
--   \le
--   \frac{\log f(r+1)}{N_i(r)}.
--   $$
--
--   Here $\overline d(p,q)=d(p,q)$ when $p\le q$, and is zero otherwise. These are the two events used to charge selections of a suboptimal arm in the proof of the finite-time KL-UCB bound.
--
--   Formalization Note: A finite bandit history stores the selected arm and observed reward at each round. The prefix $H_r$ excludes the round-$r$ observation, matching the information available to the policy when it selects that round's arm. The two real-valued components are finite sums of indicator functions.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Theorem 10.6 proof and Lemmas 10.7–10.8, printed pp. 139–140 (PDF pp. 128–129).

import Definitions.Def_klucbTruncatedRelativeEntropy
import Definitions.Def_banditHistoryPrefix

/-!
Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), proof of
Theorem 10.6, printed p. 139.

This version records the explicit one-sided KL feasibility tests appearing
in the book, rather than comparisons with the supremum-valued index.
-/

namespace BanditAlgorithm

/-- The two measurable selected-round counts in the proof of Theorem 10.6.
The first records incomplete initialization or failure of the optimal-arm
threshold test; the second records success of the selected arm's threshold
test after initialization. -/
noncomputable def klucbFeasibilityFailureCount {k n : ℕ}
    (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) : ℝ × ℝ :=
  let initialized := fun r : Fin n ↦
    ∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0
  let threshold := banditOptimalMean ν - ε
  let budget := fun (j : Fin k) (r : Fin n) ↦
    Real.log (klucbExploration (r.val + 1)) /
      armPullCount j (banditHistoryPrefixAt h r)
  let lowSelected := ∑ r : Fin n,
    if (h r).1 = i ∧
        (¬ initialized r ∨
          budget a r <
            klucbTruncatedRelativeEntropy
              (armEmpiricalMean a (banditHistoryPrefixAt h r))
              threshold) then (1 : ℝ) else 0
  let highSelected := ∑ r : Fin n,
    if initialized r ∧ (h r).1 = i ∧
        klucbTruncatedRelativeEntropy
            (armEmpiricalMean i (banditHistoryPrefixAt h r))
            threshold ≤
          budget i r then (1 : ℝ) else 0
  (lowSelected, highSelected)

end BanditAlgorithm


