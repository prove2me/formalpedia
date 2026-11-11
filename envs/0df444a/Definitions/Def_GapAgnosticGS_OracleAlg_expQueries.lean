-- Prove2me | Definitions.Def_GapAgnosticGS_OracleAlg_expQueries
-- name    : GapAgnosticGS_OracleAlg_expQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:20.630058+00:00
-- url     : https://prove2.me/theorems/b5835ff9-7a72-419d-92b4-9020a1e75321
-- title:
--   Expected number of oracle queries
-- statement:
--   The **expected query count** of an adaptive oracle algorithm with oracle $U$ is
--
--   $$\mathbb E[\#\text{queries}]=\sum_{h:\ \text{the step at }h\text{ is a query}}\|\psi_h\|^2 ,$$
--
--   the expected number of controlled uses of $U$ or $U^\dagger$ along a run. It is the cost measure of the upper bounds ("expected queries").
--
--   **Formalization Note** Valued in $[0,\infty]$: an algorithm whose runs are too long with too much probability has expected count $\infty$, never a junk $0$.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1, p.2 (PDF p.3): "using … expected queries"

import Definitions.Def_GapAgnosticGS_OracleAlg_branch

namespace GapAgnosticGS

open scoped ENNReal

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1, p.2 (PDF p.3): "using … expected queries"; §1, p.1 (PDF p.2): "one
controlled use of W_H or W_H† counts as one query". The expected number of queries of the run of
`A` with oracle `U`: the sum, over the histories at which `A` queries, of the probability (squared
branch norm) of reaching that history.

**Formalization Note.** `ℝ≥0∞`-valued: an algorithm whose runs make unboundedly many queries with
too much probability has `expQueries = ⊤`, never a junk `0`. -/
noncomputable def OracleAlg.expQueries {Q Y O : Type} [Fintype Q] [DecidableEq Q] [Fintype Y]
    [DecidableEq Y] (A : OracleAlg Q Y O) (U : Matrix Q Q ℂ) : ℝ≥0∞ :=
  ∑' h : List ℕ, match A.step h with
    | .query _ => (‖A.branch U h‖₊ : ℝ≥0∞) ^ 2
    | _ => 0

end GapAgnosticGS


