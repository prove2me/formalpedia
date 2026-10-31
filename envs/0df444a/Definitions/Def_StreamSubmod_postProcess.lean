-- Prove2me | Definitions.Def_StreamSubmod_postProcess
-- name    : StreamSubmod_postProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:11.686636+00:00
-- url     : https://prove2.me/theorems/a861a612-077c-48bd-8ab6-9481dcfc020e
-- title:
--   Post-processing of the solutions $S_1,\dots,S_p$
-- statement:
--   Given solutions $S_1,\dots,S_p$, the post-processing runs the offline algorithm with $\bigcup_{i=1}^p S_i$ as the ground set, which gives a solution $S_o$, and returns the solution of maximum value among $S_o,S_1,\dots,S_p$. The module also defines the best set of a list of sets, which is the empty set for the empty list.
--
--   This is the last phase of Algorithm 1 and, for each guess, of Algorithm 2.
--
--   **Formalization Note** Ties go to the earliest set in the list. The guarantees only concern the value of the returned set.
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Algorithm 1, lines 6–7, p.7; Algorithm 2, lines 13–15, p.11

import Mathlib

namespace StreamSubmod

variable {E : Type} [DecidableEq E]

/-- The better of two sets: `B` if it has strictly larger value, and `A` otherwise. -/
noncomputable def better (f : Finset E → ℝ) (A B : Finset E) : Finset E :=
  if f A < f B then B else A

/-- A set of maximum value in a list of sets (ties: the earliest in the list), and the empty set for
the empty list (Algorithm 2, line 15, p.11: "or the empty set if `T = ∅`"). -/
noncomputable def bestOf (f : Finset E → ℝ) : List (Finset E) → Finset E
  | [] => ∅
  | A :: L => L.foldl (better f) A

/-- The post-processing of the solutions `S_1, …, S_p` (Algorithm 1, lines 6–7, p.7; Algorithm 2,
lines 13–14, p.11): run the offline algorithm with `⋃ᵢ S_i` as the ground set to obtain `S_o`, and
return the best among `S_o, S_1, …, S_p`. -/
noncomputable def postProcess {Ω : Type} {p : ℕ} [Fintype E] (f : Finset E → ℝ)
    (Off : Ω → Finset E → Finset E) (ω : Ω) (S : Fin p → Finset E) : Finset E :=
  bestOf f (Off ω (Finset.univ.biUnion S) :: (List.finRange p).map S)

end StreamSubmod


