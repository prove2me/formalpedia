-- Prove2me | Definitions.Def_MDPComplexity_AverageCost_DetMDP
-- name    : MDPComplexity_AverageCost_DetMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:31:56.410987+00:00
-- url     : https://prove2.me/theorems/f99cd191-005c-4931-83f8-312f0734d7cf
-- title:
--   Finite stationary deterministic Markov decision process
-- statement:
--   A **deterministic Markov decision process** has a finite state set $S$. Each state $s$ has a finite, nonempty set $D_s$ of available decisions. A decision $d\in D_s$ has a real cost $c(s,d)$ and a certain successor state $\operatorname{next}(s,d)\in S$.
--
--   The process is stationary: neither its decision sets, costs nor successors depend on time. Decisions remain distinct even if they have the same source and destination, so the associated directed graph can have parallel arcs and loops. This is the model used throughout the mission.
--
--   **Formalization Note** Nonempty $D_s$ makes a policy possible at every state. This is implicit in the paper's definition of a policy, which chooses a decision for every state and time.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), pp. 444–445, §2 Markov Decision Processes and §3 Deterministic problems, https://doi.org/10.1287/moor.12.3.441

import Mathlib

namespace MDPComplexity.AverageCost

/-- A finite stationary deterministic Markov decision process. Each decision is an arc,
so distinct decisions may have the same destination. -/
structure DetMDP (S : Type*) [Fintype S] where
  D : S → Type*
  [finiteD : ∀ s, Fintype (D s)]
  [nonemptyD : ∀ s, Nonempty (D s)]
  next : (s : S) → D s → S
  c : (s : S) → D s → ℝ

attribute [instance] DetMDP.finiteD DetMDP.nonemptyD

end MDPComplexity.AverageCost


