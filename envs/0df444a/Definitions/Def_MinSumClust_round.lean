-- Prove2me | Definitions.Def_MinSumClust_round
-- name    : MinSumClust_round
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:15.058746+00:00
-- url     : https://prove2.me/theorems/67be1643-f163-48d3-819d-ff18d88e4b38
-- title:
--   The rounding algorithm of Theorem 3
-- statement:
--   Given $\mathcal S_1,\mathcal S_2$ with $k_1\le k<k_2$: if $\alpha>1/2$, the algorithm returns $\mathcal S_1$ split into exactly $k$ nonempty clusters (§5, p.42; §5.5.3, p.56); otherwise it samples the labelings of §5.3 and runs Algorithms 5, 6 and 7. The result is a probability distribution over outcomes.
--
--   **Formalization Note** The split and the tie ranking of Algorithm 6 are parameters (the paper fixes neither), and Theorem 3 holds for every split refining $\mathcal S_1$ into $k$ parts and every ranking.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), §5, p.42 (PDF p.44); §5.3–§5.5, pp.43–56

import Mathlib
import Definitions.Def_MinSumClust_Bipoint
import Definitions.Def_MinSumClust_alg5
import Definitions.Def_MinSumClust_alg6
import Definitions.Def_MinSumClust_alg7

namespace MinSumClust

variable {D : Type} [Fintype D] [DecidableEq D]

/-- **Algorithms 5–7 with the random labelings** (§5.3–§5.5, pp.43–49): sample `ℓ_M, ℓ_L`, run
Algorithm 5, Algorithm 6 and Algorithm 7.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), §5, pp.43–49 (PDF pp.45–51). -/
noncomputable def alg567 (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (k : ℕ)
    (rk : Finset D → ℕ) : PMF (Outcome D) :=
  (labelPMF S₁ S₂).bind fun ℓ =>
    (alg6 S₁ S₂ k rk ℓ (alg5 S₁ S₂ ℓ)).map (alg7 S₁ S₂ ℓ (alg5 S₁ S₂ ℓ))

/-- The outcome whose clusters are the parts of `sp` (tagged with side `0`). -/
def splitOutcome (sp : Finset (Finset D)) : Outcome D :=
  (sp.image fun S => ((0 : Fin 2), S), fun t => t.2)

/-- **The rounding algorithm of Theorem 3** (§5, p.42, and §5.5.3, p.56): if `α > 1/2`, return
`𝒮₁` split into exactly `k` nonempty clusters (the parts of `sp`); otherwise run Algorithms 5–7.

**Formalization Note.** "Splitting it into exactly k nonempty clusters" fixes no rule, so the split
`sp` is a parameter, and Theorem 3 quantifies over every refinement of `𝒮₁` into `k` parts. The tie
ranking `rk` of Algorithm 6 is a parameter too. -/
noncomputable def round (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (k : ℕ)
    (rk : Finset D → ℕ) (sp : Finset (Finset D)) : PMF (Outcome D) :=
  if 1 / 2 < alphaBip S₁ S₂ k then PMF.pure (splitOutcome sp) else alg567 S₁ S₂ k rk

end MinSumClust


