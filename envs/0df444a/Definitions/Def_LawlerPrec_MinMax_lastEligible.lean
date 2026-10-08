-- Prove2me | Definitions.Def_LawlerPrec_MinMax_lastEligible
-- name    : LawlerPrec_MinMax_lastEligible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:52:51.734052+00:00
-- url     : https://prove2.me/theorems/a47ebce3-258c-4cd2-b0de-6baf3db705db
-- title:
--   The set $S$ of jobs that may be performed last
-- statement:
--   Let $J$ be a finite set of jobs and $\prec$ the precedence relation ($i \prec j$: job $i$ is required to precede job $j$). The set $S(J)$ of jobs **which may be performed last** consists of the jobs of $J$ that are not required to precede any other job of $J$:
--
--   $$
--   S(J) \;=\; \{\, j \in J \;:\; \text{there is no } i \in J,\ i \neq j, \text{ with } j \prec i \,\}.
--   $$
--
--   This is the set $S$ of Lawler's Sequencing Theorem. Applied to the set of jobs that remain after some jobs have already been placed at the end of the sequence, it gives the jobs eligible for the latest still-open position; constraints into jobs already placed are ignored, which is what "having removed $k$ from the problem" means in the algorithm.
--
--   **Formalization Note** "Others" excludes $j$ itself (the guard $i \neq j$), so a self-loop $j \prec j$ does not remove $j$ from $S(J)$; this matches the feasibility definition, which compares only distinct positions. Only jobs of $J$ are considered.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 544, §2 Sequencing Theorem, THEOREM (the set S)

import Mathlib

namespace LawlerPrec.MinMax

open Classical in
/-- The set `S` of the Theorem (Lawler 1973, §2, p. 544): "the subset of jobs which may be
performed last, i.e. those jobs which are not required to precede any others". A job `j ∈ J`
belongs to `S` iff `prec j i` fails for every other job `i ∈ J`, `i ≠ j`. Only jobs of `J`
count, so for a reduced job set (after removing jobs already placed last) constraints into
removed jobs are ignored. -/
noncomputable def lastEligible {ι : Type*} (prec : ι → ι → Prop) (J : Finset ι) : Finset ι :=
  J.filter (fun j => ∀ i ∈ J, i ≠ j → ¬ prec j i)

end LawlerPrec.MinMax


