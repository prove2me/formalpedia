-- Prove2me | Definitions.Def_CoffmanMitrani_IsStrategy
-- name    : CoffmanMitrani_IsStrategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:15:27.355125+00:00
-- url     : https://prove2.me/theorems/0c43c9a1-21bb-4686-807f-86559c69f3a6
-- title:
--   Scheduling strategies (Assumptions 1–3)
-- statement:
--   A schedule $S$ is a **scheduling strategy** if
--
--   1. for each job $j$ the set of pairs (sample point, time) at which $S$ serves $j$ is measurable (up to null sets) for the product of $P$ and Lebesgue measure;
--
--   and there is a decision rule — a function from (busy-period record, seed sequence) to a (class, rank) or "idle" — such that for almost every sample point:
--
--   2. only present jobs are served;
--   3. $S(t)$ is "idle" exactly when no job is present at time $t$ (Assumption 1: no artificial idle periods);
--   4. every job eventually receives its full service requirement;
--   5. whenever job $j_0$ opens a busy period and $t$ lies in that busy period, $S(t)$ is the job named by the rule applied to the record of that busy period at time $t$ and to the seeds of $j_0$ (Assumptions 2 and 3).
--
--   Clause 5 means that sequencing decisions use only the arrival times, departure times, execution intervals and class indices of the jobs of the current busy period up to time $t$, possibly randomized through that busy period's own seeds, and the same rule is applied in every busy period. Such a strategy cannot see service requirements that have not yet been revealed by a departure, future arrivals, or anything from earlier busy periods. Preemptive priority, first-come-first-served, preemptive last-come-first-served, round robin with a fixed quantum and mixing strategies are scheduling strategies; shortest-remaining-processing-time is not.
--
--   **Formalization Note** Clause 4 follows almost surely from clauses 2–3 and $\rho<1$; it makes departure times well defined.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812, Assumptions 1–3 and the paragraph after them

import Mathlib
import Definitions.Def_CoffmanMitrani_Data_P
import Definitions.Def_CoffmanMitrani_present
import Definitions.Def_CoffmanMitrani_history__a0cb5b
import Definitions.Def_CoffmanMitrani_IsBPStart
import Definitions.Def_CoffmanMitrani_InBP
import Definitions.Def_CoffmanMitrani_seed
open MeasureTheory ProbabilityTheory

namespace CoffmanMitrani

/-- **Scheduling strategies (Assumptions 1–3).**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812: "1. We assume that S(t) takes on the special value 0 when and only when t falls
within an idle period. 2. If t falls within busy period B, then the domain of S(t) is restricted to
those arrival times, departure times, execution intervals, and (priority) class indices which apply
to jobs waiting, being served, or having been served during B up to time t. 3. A mapping S(t) may be
deterministic or it may be governed by some probability law whose parameters are restricted to those
in Assumption 2 above. … Assumption 2 does not permit any strategy which bases the sequencing
decisions in one busy period on information concerning prior busy periods."

`IsStrategy D S` holds when
1. (measurability) for every job `j`, `{(ω, t) | S ω t = some j}` is null-measurable for
   `D.P ⊗ Lebesgue`; and there is a decision rule `rule`, mapping a busy-period record (`History`)
   and a seed sequence to a (class, rank) or `none`, such that for `D.P`-almost every `ω`:
2. (feasibility) a job served at time `t` is present (has arrived and requires further service);
3. (Assumption 1) `S ω t = none` exactly when no job is present at time `t`;
4. (completion) every job eventually receives its full service requirement;
5. (Assumptions 2–3) whenever job `j0` opens a busy period and `t` lies in it, `S ω t` is
   `rule (history S ω j0 t) (seed ω j0)`, translated back from ranks to job indices.

**Formalization Note.** Clause 5 is the reading of Assumptions 2–3: the decision at time `t` is a
function of the current busy period's own arrival, schedule and departure record (relative times,
classes, ranks) and of that busy period's own seeds, through one rule used in every busy period; so
the strategy cannot see unrealized service requirements, future arrivals, or anything from earlier
busy periods (including the absolute time and the busy-period count). Randomization is the seed
dependence. Clause 4 holds automatically under clauses 2–3 and `ρ < 1`; it ensures `departure` is
not a junk value. Clauses 2–5 are required almost surely. -/
def IsStrategy (D : Data) (S : Schedule D.M) : Prop :=
  (∀ j : Job D.M, NullMeasurableSet {p : Omega D.M × ℝ | S p.1 p.2 = some j}
      (D.P.prod MeasureTheory.volume)) ∧
  ∃ rule : History D.M → (ℕ → unitInterval) → Option (Fin D.M × ℕ),
    ∀ᵐ ω ∂D.P,
      (∀ (t : ℝ) (j : Job D.M), S ω t = some j → present S j ω t) ∧
      (∀ t : ℝ, S ω t = none ↔ ∀ j : Job D.M, ¬ present S j ω t) ∧
      (∀ j : Job D.M, ∃ t : ℝ, serviceReq ω j ≤ served S j ω t) ∧
      (∀ (j0 : Job D.M) (t : ℝ), IsBPStart ω j0 → InBP ω j0 t →
        S ω t = (rule (history S ω j0 t) (seed ω j0)).map
          (fun p => (p.1, classOffset ω j0 p.1 + p.2)))

end CoffmanMitrani


