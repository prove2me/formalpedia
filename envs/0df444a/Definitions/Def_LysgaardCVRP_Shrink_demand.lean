-- Prove2me | Definitions.Def_LysgaardCVRP_Shrink_demand
-- name    : LysgaardCVRP_Shrink_demand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:23:40.431331+00:00
-- url     : https://prove2.me/theorems/4f834735-d96d-4fb7-a5bd-1342212ab9d8
-- title:
--   Total demand $q(S)$ of a customer set
-- statement:
--   Each customer $i \in \{1, \dots, n\}$ has an integer demand $q_i$. For a set $S$ of customers, the **total demand** is
--
--   $$q(S) = \sum_{i \in S} q_i .$$
--
--   It is the total load that the vehicles serving $S$ must carry, and it enters the rounded capacity bound $k(S) = \lceil q(S)/Q \rceil$.
--
--   **Formalization Note** Demands are natural numbers indexed by `Fin (n+1)`; the value at the depot $0$ is never used. The sum is taken in the reals because the capacity $Q$ is real.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 424 (PDF p. 2), §1, definition of q(S)

import Mathlib

namespace LysgaardCVRP.Shrink

/-- The total demand $q(S) = \sum_{i \in S} q_i$ of a set of customers (Lysgaard, Letchford &
Eglese, Math. Program. Ser. A 100 (2004), §1, p. 424, PDF p. 2).

**Formalization Note.** Demands are natural numbers `q : Fin (n+1) → ℕ` (the paper's demands
are integers with $0 < q_i \le Q$); the value `q 0` at the depot is never used by the theorems,
which apply `demand` only to sets not containing `0`. The sum is taken in `ℝ` because the
capacity $Q$ is real. -/
def demand {n : ℕ} (q : Fin (n + 1) → ℕ) (S : Finset (Fin (n + 1))) : ℝ :=
  ∑ i ∈ S, (q i : ℝ)

end LysgaardCVRP.Shrink


