-- Prove2me | Definitions.Def_RvsCert_IsChampion
-- name    : RvsCert_IsChampion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:45:00.150202+00:00
-- url     : https://prove2.me/theorems/7533152f-dd87-42b4-8bd2-aa1d12a2fda2
-- title:
--   Champion of the sporting event
-- statement:
--   An athlete $a=(c,b)$ is the **champion** of the input $(X,Y)$ if
--
--   1. *(well formatted proposal card)* $Y^a_0\le Y^a_1\le\dots\le Y^a_{2n-2}$ and $Y^a_{2n-2}<n$;
--   2. *(proposal card consistent with race)* for each $j\in\{0,\dots,2n-2\}$, with $p_j=Y^a_j-Y^a_{j-1}$ and $r$ the $j$-th race of $c$: $p_j<n$, the result list of $r$ holds $a$ at position $p_j$, and every position $q<p_j$ holds $\bot$.
--
--   This is the paper's formal definition; the informal conditions (C1)–(C3) are its motivation and are not separate requirements.
--
--   **Formalization Note** Positions are $0$-based. An entry that is neither $0$ nor a valid athlete code is not $\bot$, so it fails the second condition at a prior position.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, Formal definition, p.2

import Mathlib
import Definitions.Def_RvsCert_raceOf
import Definitions.Def_RvsCert_raceEntry
import Definitions.Def_RvsCert_athleteCode
import Definitions.Def_RvsCert_claimedPos

namespace RvsCert

/-- **Athlete `a = (c, b)` is the champion of input `x`** (Formal definition, Section 2, p.2 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1, conditions 1 and 2):
1. *Well formatted proposal card*: the card entries `Y_0, …, Y_{2n−2}` are monotonically
   non-decreasing and the last one is `< n`;
2. *Proposal card consistent with race*: in each of the `2n − 1` races of `a` (the `j`-th against
   `opponent c j`), the claimed position `p_j = Y_j − Y_{j−1}` exists (`p_j < n`), the race
   result at position `p_j` is athlete `a`, and every prior position is ⊥.

**Formalization Note.** Positions are `0`-based; ⊥ is the value `0`; an entry with a value that
is neither `0` nor a valid athlete code is not ⊥. Conditions (C1)–(C3) of p.1–2 are the informal
reading and are not separate clauses: the formal definition only asks that prior positions be ⊥. -/
def IsChampion (n : ℕ) (x : Idx n → Bool) (a : Fin (2 * n) × Fin n) : Prop :=
  (∀ j j' : Fin (2 * n - 1), j ≤ j' → cardEntry n x a j ≤ cardEntry n x a j') ∧
  (∀ j : Fin (2 * n - 1), (j : ℕ) + 1 = 2 * n - 1 → cardEntry n x a j < n) ∧
  (∀ j : Fin (2 * n - 1), claimedPos n x a j < n ∧
    ∀ q : Fin n,
      ((q : ℕ) < claimedPos n x a j → raceEntry n x (raceOf a.1 j) q = 0) ∧
      ((q : ℕ) = claimedPos n x a j → raceEntry n x (raceOf a.1 j) q = athleteCode n a))

instance (n : ℕ) (x : Idx n → Bool) (a : Fin (2 * n) × Fin n) : Decidable (IsChampion n x a) := by
  unfold IsChampion; infer_instance

end RvsCert


