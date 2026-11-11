-- Prove2me | Definitions.Def_GapAgnosticGS_OracleAlg_maxQueries
-- name    : GapAgnosticGS_OracleAlg_maxQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:52.557851+00:00
-- url     : https://prove2.me/theorems/9939f40c-8a25-4c59-a12d-51214f68f683
-- title:
--   Worst-case number of oracle queries
-- statement:
--   The **worst-case query count** of an adaptive oracle algorithm with oracle $U$ is the supremum, over all histories reached with nonzero probability, of the number of queries made before reaching them. A lower bound "requires $\Omega(\cdot)$ queries in the worst case" bounds this quantity from below on some instance.
--
--   **Formalization Note** Valued in $\mathbb N\cup\{\infty\}$; an algorithm with runs of unbounded length has worst-case count $\infty$ (comparisons are made in $[0,\infty]$, never by converting $\infty$ to $0$).
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 3.15, p.14 (PDF p.15): "requires Ω((α/∆gs)√deff) queries in the worst case"

import Definitions.Def_GapAgnosticGS_OracleAlg_pathQueries
import Definitions.Def_GapAgnosticGS_OracleAlg_branch

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 3.15, p.14 (PDF p.15): "requires Ω((α/Δ_gs)√d_eff) queries in the worst case".
The worst-case number of queries of `A` with oracle `U`: the supremum, over the histories reached
with nonzero probability, of the number of queries made before reaching them.

**Formalization Note.** `ℕ∞`-valued: an algorithm with runs of unbounded length has
`maxQueries = ⊤`. Lower bounds compare it in `ℝ≥0∞`, never through `toReal`. -/
noncomputable def OracleAlg.maxQueries {Q Y O : Type} [Fintype Q] [DecidableEq Q] [Fintype Y]
    [DecidableEq Y] (A : OracleAlg Q Y O) (U : Matrix Q Q ℂ) : ℕ∞ :=
  ⨆ (h : List ℕ) (_ : A.branch U h ≠ 0), (A.pathQueries h : ℕ∞)

end GapAgnosticGS


