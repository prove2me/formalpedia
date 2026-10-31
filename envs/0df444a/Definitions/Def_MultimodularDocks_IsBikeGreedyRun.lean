-- Prove2me | Definitions.Def_MultimodularDocks_IsBikeGreedyRun
-- name    : MultimodularDocks_IsBikeGreedyRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:34.77898+00:00
-- url     : https://prove2.me/theorems/4e3613cf-c180-4e1e-91d3-e4f8c2e09362
-- title:
--   A complete run of Algorithm 1 (greedy bike placement, $\alpha=1$)
-- statement:
--   Algorithm 1 places bikes greedily for fixed docks. At the current allocation, adding a bike at $i$ (turning an empty dock full) has gain $c_i(d_i,b_i)-c_i(d_i-1,b_i+1)$, possible when $d_i\ge 1$, and removing a bike at $j$ has gain $c_j(d_j,b_j)-c_j(d_j+1,b_j-1)$, possible when $b_j\ge 1$. One iteration
--
--   1. picks $i^\star$ maximizing the gain of adding and $j^\star$ maximizing the gain of removing (ties broken arbitrarily);
--   2. if the two gains sum to a positive number, moves a bike from $j^\star$ to $i^\star$;
--   3. otherwise stops.
--
--   A **complete run** from an allocation $a$ to $y$ is a finite sequence of such bike moves from $a$ to $y$ such that the routine stops at $y$: no station can receive a bike, or none can give one, or the chosen pair has total gain at most $0$.
--
--   **Formalization Note** The routine is a relation, so every tie-breaking is covered. Stations at which a move is impossible are excluded from the maxima (their value in the paper is $-\infty$); if no station is left, the routine stops.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Algorithm 1, p.35 (with α = 1)

import Mathlib
import Definitions.Def_MultimodularDocks_bikeMove

namespace MultimodularDocks

variable {S : Type*}

/-- The gain `c_i(d_i, b_i) − c_i(d_i − 1, b_i + 1)` of adding a bike at `i` (an empty dock
becomes full), line 3 of Algorithm 1 (arXiv:1611.09304v5, p.35) with `α = 1`. -/
def addGain (I : Instance S) (a : Alloc S) (i : S) : ℝ :=
  I.g i (a.d i) (a.b i) - I.g i (a.d i - 1) (a.b i + 1)

/-- The gain `c_j(d_j, b_j) − c_j(d_j + 1, b_j − 1)` of removing a bike at `j`, line 4 of
Algorithm 1 (p.35) with `α = 1`. -/
def removeGain (I : Instance S) (a : Alloc S) (j : S) : ℝ :=
  I.g j (a.d j) (a.b j) - I.g j (a.d j + 1) (a.b j - 1)

/-- Lines 3–4 of Algorithm 1 (p.35): `i` maximizes `addGain` over the stations where a bike can
be added (`d_i ≥ 1`), and `j` maximizes `removeGain` over the stations where a bike can be
removed (`b_j ≥ 1`). Ties may be broken arbitrarily. -/
def IsBikePick (I : Instance S) (a : Alloc S) (i j : S) : Prop :=
  1 ≤ a.d i ∧ (∀ i', 1 ≤ a.d i' → addGain I a i' ≤ addGain I a i) ∧
    1 ≤ a.b j ∧ (∀ j', 1 ≤ a.b j' → removeGain I a j' ≤ removeGain I a j)

/-- One iteration of Algorithm 1 that moves a bike (lines 5–7, p.35): for a pick `(i⋆, j⋆)`
with `addGain + removeGain > 0`, a bike moves from `j⋆` to `i⋆`. -/
def BikeStep [DecidableEq S] (I : Instance S) (a a' : Alloc S) : Prop :=
  ∃ i j, IsBikePick I a i j ∧ 0 < addGain I a i + removeGain I a j ∧ a' = bikeMove j i a

/-- The stopping test of Algorithm 1 (line 9, p.35): no station can receive a bike, or none can
give one, or the pick's combined gain is `≤ 0`. -/
def BikeStop (I : Instance S) (a : Alloc S) : Prop :=
  (∀ i, a.d i < 1) ∨ (∀ j, a.b j < 1) ∨
    ∃ i j, IsBikePick I a i j ∧ addGain I a i + removeGain I a j ≤ 0

/-- **A complete run of Algorithm 1** (Greedy routine to find a bike-optimal allocation,
Freund, Henderson, Shmoys, arXiv:1611.09304v5, Algorithm 1, p.35, with `α = 1`): `y` is reached
from `a` by iterations that move a bike, and the stopping test holds at `y`.

**Formalization Note** The routine is a relation, so every tie-breaking in the `arg max` of
lines 3–4 is covered. The `arg max` of the page ranges over values `c_i(d_i, b_i) −
c_i(d_i − 1, b_i + 1)` that are `−∞` when `d_i = 0` (and likewise for removal when `b_j = 0`);
such stations are excluded, and if no station is left, the comparison of line 5 fails and the
routine stops. -/
def IsBikeGreedyRun [DecidableEq S] (I : Instance S) (a y : Alloc S) : Prop :=
  Relation.ReflTransGen (BikeStep I) a y ∧ BikeStop I y

end MultimodularDocks


