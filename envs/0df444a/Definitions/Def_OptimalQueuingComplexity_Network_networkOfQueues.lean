-- Prove2me | Definitions.Def_OptimalQueuingComplexity_Network_networkOfQueues
-- name    : OptimalQueuingComplexity_Network_networkOfQueues
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T10:03:42.391614+00:00
-- url     : https://prove2.me/theorems/534392d3-a4d9-4366-934d-66a62e34f158
-- title:
--   The decision problem NETWORK OF QUEUES
-- statement:
--   **NETWORK OF QUEUES**: given a well-formed instance with threshold $K \in \mathbb{Q}$, decide whether there exists an admissible policy $\pi$ with
--   $$J^\pi > K.$$
--
--   This is the decision problem of Section 2 of Papadimitriou and Tsitsiklis: "The problem is to decide whether there exists a policy $\pi$ for which $J^\pi > K$." The inequality is strict.
--
--   **Formalization Note.** An instance that is not well formed is a no-instance. Policies are deterministic and stationary, as in the paper's definition of a policy. $J^\pi$ is compared with $K$ in the extended reals.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 295, Section 2 (formal definition of the problem NETWORK OF QUEUES)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Network_weightedThroughput

namespace OptimalQueuingComplexity.Network

/-- The decision problem **NETWORK OF QUEUES** (Papadimitriou & Tsitsiklis 1999, p. 295): given a
(well-formed) instance, "decide whether there exists a policy `π` for which `J^π > K`". -/
def networkOfQueues (I : Instance) : Prop :=
  I.WellFormed ∧ ∃ π : Policy I, π.Admissible ∧ ((I.K : ℝ) : EReal) < weightedThroughput π

end OptimalQueuingComplexity.Network


