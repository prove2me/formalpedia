-- Prove2me | Definitions.Def_CoffmanMitrani_IsPriority
-- name    : CoffmanMitrani_IsPriority
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:18:02.311971+00:00
-- url     : https://prove2.me/theorems/45118e59-07ec-456b-bbaf-1ecb9c726847
-- title:
--   Preemptive priority discipline $S(i_1,\dots,i_M)$
-- statement:
--   Let $\sigma$ be an ordering of the classes, $\sigma(0)$ having the highest priority. A schedule $S$ follows the preemptive priority discipline for $\sigma$ if, almost surely, whenever $S$ serves job $j$ at time $t$, every job present at time $t$ belongs to a class of strictly lower priority, or to the same class with a later (or equal) index. Combined with the scheduling-strategy conditions this is the preemptive-resume priority discipline that always serves the earliest present job of the highest-priority class with a present job.
--
--   The paper's discipline $S(i_1, i_2, \dots, i_M)$, with performance vector $P(i_1,\dots,i_M)$, gives class $i_1$ the highest priority, then $i_2$, and so on.
--
--   **Formalization Note** $\sigma(k) = i_{k+1} - 1$ in 0-based classes. The order within a class is first come first served; the paper does not fix it, and it does not change any class mean.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 815

import Mathlib
import Definitions.Def_CoffmanMitrani_Data_P
import Definitions.Def_CoffmanMitrani_present
open MeasureTheory ProbabilityTheory

namespace CoffmanMitrani

/-- **Preemptive priority discipline.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 815: "the preemptive priority disciplines, S(1, 2) and S(2, 1), giving preemptive
priority to Class 1 and Class 2 jobs respectively"; "There are M! such disciplines, one for each
assignment of priorities to the M job classes. Denote by P(1, 2, ···, M), ···, P(M, M − 1, ···, 1)
the performance vectors of these strategies".

For a permutation `σ` of the classes (`σ 0` has the highest priority, `σ 1` the next, …),
`IsPriority D σ S` says that almost surely, whenever `S` serves job `j` at time `t`, every job `j'`
present at time `t` has strictly lower priority class, or the same class and a later (or equal)
index. Together with `IsStrategy D S` (no idling, only present jobs served) this is the
preemptive-resume priority discipline for the priority order `σ 0, σ 1, …`, first come first served
within a class.

**Formalization Note.** The paper's `S(i1, …, iM)` is `σ` with `σ k = i_{k+1} − 1` (0-based classes).
Service order within a class is not specified in the paper; first come first served is used, and
any within-class order gives the same class means. -/
def IsPriority (D : Data) (σ : Equiv.Perm (Fin D.M)) (S : Schedule D.M) : Prop :=
  ∀ᵐ ω ∂D.P, ∀ (t : ℝ) (j j' : Job D.M), S ω t = some j → present S j' ω t →
    σ.symm j.1 < σ.symm j'.1 ∨ (j.1 = j'.1 ∧ j.2 ≤ j'.2)

end CoffmanMitrani


