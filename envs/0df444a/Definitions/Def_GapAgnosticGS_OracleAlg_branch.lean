-- Prove2me | Definitions.Def_GapAgnosticGS_OracleAlg_branch
-- name    : GapAgnosticGS_OracleAlg_branch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:07.409535+00:00
-- url     : https://prove2.me/theorems/30aba3c8-d7e1-48d3-8d4e-5eadec3114e1
-- title:
--   Branch vector of an adaptive oracle algorithm after a classical history
-- statement:
--   For an adaptive oracle algorithm and an oracle $U$, the **branch vector** $\psi_h$ after the classical history $h$ is defined recursively: $\psi_{[]}$ is the initial state, and $\psi_{z::h}$ is obtained from $\psi_h$ by one step (isometry, controlled query, or projection onto measurement outcome $z$). Its squared norm $\|\psi_h\|^2$ is the probability that the run passes through $h$.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1, p.2 (PDF p.3) (the algorithm model)

import Definitions.Def_GapAgnosticGS_OracleAlg_child

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc) (the algorithm model of Theorem 1.1, p.2, PDF p.3). The unnormalized branch vector of
the run of `A` with oracle `U` after the classical history `h` (newest entry first): `init` at the
empty history, then one `OracleAlg.child` step per entry. Its squared norm is the probability
that the run passes through `h`. -/
noncomputable def OracleAlg.branch {Q Y O : Type} [Fintype Q] [DecidableEq Q] [Fintype Y]
    [DecidableEq Y] (A : OracleAlg Q Y O) (U : Matrix Q Q ℂ) :
    (h : List ℕ) → EuclideanSpace ℂ (Q × Y × Bool × Fin (A.w h))
  | [] => A.init
  | z :: h => A.child U h z (OracleAlg.branch A U h)

end GapAgnosticGS


