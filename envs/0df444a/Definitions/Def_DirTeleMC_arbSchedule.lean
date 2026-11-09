-- Prove2me | Definitions.Def_DirTeleMC_arbSchedule
-- name    : DirTeleMC_arbSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:31:40.569201+00:00
-- url     : https://prove2.me/theorems/ffd4a3d3-4a02-45c4-be1f-f0af84cf994e
-- title:
--   The schedule along an out-arborescence with a child order
-- statement:
--   An out-arborescence $T$ with a child order defines a schedule: every vertex calls its children consecutively in that order, starting in the round after it becomes informed. The root is informed in round $0$, and if $u$ is informed in round $t(u)$, its $i$-th child ($i = 1, 2, \dots$) is informed in round
--   $$t(c_i) = t(u) + i.$$
--   The schedule has as many rounds as the largest $t(v)$, and round $j$ consists of the calls $(\mathrm{parent}(c), c)$ with $t(c) = j$.
--
--   The **busy schedule** of Lemma 3.1 is this schedule for an arbitrary child order; SCHEDULE (§B.2) and Lemma 3.2 use orders that are non-increasing in leaf counts.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §3, pp.8–9 (PDF pp.9–10); Lemma 3.1, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_DirTeleMC_Arb
import Definitions.Def_DirTeleMC_Schedule

namespace DirTeleMC

namespace Arb

variable {n : ℕ}

/-- The informing rounds along an arborescence, computed down `m` levels: the root is informed in round `0`,
and the `i`-th child (from `0`) in `ord u` of a vertex `u` informed in round `t` is informed in round
`t + i + 1`. -/
def timeAux (A : Arb n) (ord : Fin n → List (Fin n)) : ℕ → Fin n → ℕ
  | 0, _ => 0
  | m + 1, v => timeAux A ord m (A.parent v) + (ord (A.parent v)).idxOf v + 1

/-- **The round in which `v` is informed** in the schedule along `A` with child order `ord`.
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), §3, pp.8–9: "an out-arborescence and an ordering of each vertex's children
define a schedule: every vertex calls its children consecutively in that order, starting in the round after
it becomes informed".

The root is informed in round `0` (before the first round), and `t(c) = t(u) + i + 1` for the `i`-th child
`c` (from `0`) of `u`. -/
noncomputable def informTime (A : Arb n) (ord : Fin n → List (Fin n)) (v : Fin n) : ℕ :=
  timeAux A ord (A.depth v) v

/-- **The schedule along an out-arborescence** (§3, pp.8–9). Round `j + 1` consists of the calls
`(parent c, c)` for the non-root vertices `c` with `informTime c = j + 1`; the schedule has as many rounds as
the latest informing round.

The busy schedule of Lemma 3.1 (p.9: "each informed vertex calls one child it has not yet called in every
round, until it has called all its children") is this schedule for an arbitrary child order. -/
noncomputable def arbSchedule (A : Arb n) (ord : Fin n → List (Fin n)) : Schedule n := by
  classical
  exact (List.range (A.verts.sup (A.informTime ord))).map fun j =>
    (((List.finRange n).filter fun c => c ∈ A.verts ∧ c ≠ A.root ∧ A.informTime ord c = j + 1).map
      fun c => (A.parent c, c))

end Arb

end DirTeleMC


