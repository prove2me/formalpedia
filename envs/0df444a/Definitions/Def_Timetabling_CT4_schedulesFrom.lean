-- Prove2me | Definitions.Def_Timetabling_CT4_schedulesFrom
-- name    : Timetabling_CT4_schedulesFrom
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:34:50.33736+00:00
-- url     : https://prove2.me/theorems/f344d008-b364-4670-a4af-e85d6b50a76f
-- title:
--   Placements of a teacher's lectures on its free periods
-- statement:
--   Let $L = (i_1, \dots, i_r)$ be the classes a teacher must meet (with repetitions), $A$ the teacher's free periods, and $\mathrm{ok}(i, k)$ a test saying that class $c_i$ is free at period $k$. $\mathsf{schedulesFrom}(\mathrm{ok}, L, A)$ lists the slot lists
--
--   $$
--   [(i_1, k_1), \dots, (i_r, k_r)], \qquad k_1, \dots, k_r \in A \text{ pairwise distinct}, \quad \mathrm{ok}(i_s, k_s) \text{ for all } s,
--   $$
--
--   keeping one list for every set of slots. A slot $(i, k)$ means that the teacher meets class $c_i$ at period $k$.
--
--   It is the enumeration of a teacher's possible schedules used both by the specification ($\mathsf{teacherSchedules}$) and by the algorithm.
--
--   **Formalization Note** Placements are generated in the order of $L$ and $A$; duplicates as slot sets (a class met twice) are removed. On at most two lectures and two periods the work is $O(1)$.
-- source:
--   de Werra (1985), proof of Proposition 2.4, pp. 154-155, "possible schedules"; schedule table, p. 155. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib

namespace Timetabling.CT4

/-- **All ways to place a teacher's lectures on its free periods.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4,
pp. 154–155, "possible schedules", and Table 1, p. 155.

Given the classes `L` a teacher must meet (with repetitions), the teacher's free periods `A`,
and a test `ok i k` (class `c_i` free at period `k`), `schedulesFrom ok L A` lists the slot
lists `[(i₁, k₁), …, (i_r, k_r)]` obtained by giving the lectures `L = [i₁, …, i_r]` pairwise
distinct periods `k₁, …, k_r` taken from `A` with `ok i_s k_s`; two placements with the same set
of slots are listed once.

**Formalization Note.** `place` enumerates the placements in the order of `L` and `A`; `dedup`
keeps one representative of each slot set. On a teacher with at most two lectures and at most
two periods it does `O(1)` work. -/
def schedulesFrom {m p : ℕ} (ok : Fin m → Fin p → Bool) (L : List (Fin m)) (A : List (Fin p)) :
    List (List (Fin m × Fin p)) :=
  dedup (place L A)
where
  /-- Ordered placements of the lectures `L` on distinct periods of `A`. -/
  place : List (Fin m) → List (Fin p) → List (List (Fin m × Fin p))
    | [], _ => [[]]
    | i :: L', A' => A'.flatMap fun k =>
        if ok i k then (place L' (A'.erase k)).map ((i, k) :: ·) else []
  /-- Keep one list per set of slots. -/
  dedup : List (List (Fin m × Fin p)) → List (List (Fin m × Fin p))
    | [] => []
    | s :: S =>
      if S.any (fun t => s.all (· ∈ t) && t.all (· ∈ s)) then dedup S else s :: dedup S

end Timetabling.CT4


