-- Prove2me | Definitions.Def_ParetoNCSched_firstSingleTime
-- name    : ParetoNCSched_firstSingleTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:23:22.419606+00:00
-- url     : https://prove2.me/theorems/65ee5251-b09b-4aad-b91c-0f0be8c5709a
-- title:
--   The time $t_f$: first time with $N(t_f)\le1$
-- statement:
--   $t_f$ is the first time $t\ge0$ at which at most one job of the run of $\mathrm{MRC}_R$ is unfinished.
--
--   **Formalization Note** Written as the infimum of these times; Lemma D.1 asserts that it is attained and is an event time.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma D.1(b), p.21

import Mathlib
import Definitions.Def_ParetoNCSched_stateAt
import Definitions.Def_ParetoNCSched_unfinished

namespace ParetoNCSched

/-- **The time `t_f`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma D.1(b), p.21: "Let t_f be the first time with N(t_f) ≤ 1".

**Formalization Note.** The infimum of the times `t ≥ 0` at which at most one job is unfinished in
the run of `MRC_R` (Lemma D.1 asserts it is attained and is an event time). -/
noncomputable def firstSingleTime {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ (unfinished p (stateAt R p σ t)).card ≤ 1}

end ParetoNCSched


