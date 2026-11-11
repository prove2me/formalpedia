-- Prove2me | Definitions.Def_GapAgnosticGS_OracleAlg_haltProb
-- name    : GapAgnosticGS_OracleAlg_haltProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:32.154212+00:00
-- url     : https://prove2.me/theorems/f412f8e2-9105-44d0-b9a1-05599c529541
-- title:
--   Halting probability of an oracle algorithm
-- statement:
--   The **halting probability** of an adaptive oracle algorithm with oracle $U$ is the sum of $\|\psi_h\|^2$ over the histories $h$ at which it halts. "Terminates almost surely" (Theorem 3.8) means that this probability is $1$.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 3.8, p.12 (PDF p.13): "SpecLocate(E, δ) terminates almost surely"

import Definitions.Def_GapAgnosticGS_OracleAlg_branch

namespace GapAgnosticGS

open scoped ENNReal

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 3.8, p.12 (PDF p.13): "SpecLocate(E, δ) terminates almost surely". The
probability that the run of `A` with oracle `U` halts: the sum of the squared norms of the branch
vectors at the histories where `A` halts. "Terminates almost surely" is `haltProb = 1`. -/
noncomputable def OracleAlg.haltProb {Q Y O : Type} [Fintype Q] [DecidableEq Q] [Fintype Y]
    [DecidableEq Y] (A : OracleAlg Q Y O) (U : Matrix Q Q ℂ) : ℝ≥0∞ :=
  ∑' h : List ℕ, match A.step h with
    | .halt _ => (‖A.branch U h‖₊ : ℝ≥0∞) ^ 2
    | _ => 0

end GapAgnosticGS


