-- Prove2me | Definitions.Def_OfflineToOnline_orthant
-- name    : OfflineToOnline_orthant
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:59.014233+00:00
-- url     : https://prove2.me/theorems/3d6a3f70-518c-4bb3-bf6e-568e032817c9
-- title:
--   Nonnegative orthant of $\mathbb R^d$
-- statement:
--   The **nonnegative orthant** is
--
--   $$
--   S=\{u\in\mathbb R^d:\ [u]_j\ge0\ \text{for every } j\in[d]\}.
--   $$
--
--   It is the target set of the Blackwell game attached to each subproblem of a Blackwell-reducible greedy algorithm (Definition 7); the paper also calls it the positive orthant.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Definition 7 item 2, p.18

import Mathlib

namespace OfflineToOnline

/-- The nonnegative orthant `S = {u ∈ ℝ^d : [u]_j ≥ 0, j ∈ [d]}` of Definition 7, p.18 (the
"positive orthant" of the proof of Theorem 2, p.20).

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Definition 7 item 2, p.18. -/
def orthant (d : ℕ) : Set (Fin d → ℝ) :=
  {u | ∀ j, 0 ≤ u j}

end OfflineToOnline


