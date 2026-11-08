-- Prove2me | Definitions.Def_CompDesignBFM_RandMechanism
-- name    : CompDesignBFM_RandMechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:09.800511+00:00
-- url     : https://prove2.me/theorems/d5ecfca5-3b49-4a3a-bb1b-5bbe1b51e59e
-- title:
--   Randomized mechanism as a finite mixture
-- statement:
--   A **randomized mechanism** is a finite mixture: weights $w_1,\dots,w_k\ge0$ with $\sum_j w_j=1$ and deterministic mechanisms $M_1,\dots,M_k$.
--
--   **Formalization Note** The paper speaks of a distribution over deterministic mechanisms; a finite mixture is one, so an existence claim for this type is at least as strong as the paper's.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism

namespace CompDesignBFM

/-- A randomized mechanism as a finite mixture of deterministic mechanisms
(Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3: "a distribution over deterministic truthful mechanisms").
**Formalization Note.** A finite mixture is a distribution over deterministic mechanisms, so an
existence claim for this type is at least as strong as the paper's. -/
structure RandMechanism (n : ℕ) where
  /-- The number of components. -/
  k : ℕ
  /-- The mixture weights. -/
  w : Fin k → ℝ
  /-- The weights are nonnegative. -/
  w_nonneg : ∀ j, 0 ≤ w j
  /-- The weights sum to one. -/
  w_sum : ∑ j, w j = 1
  /-- The deterministic components. -/
  mech : Fin k → Mechanism n

end CompDesignBFM


