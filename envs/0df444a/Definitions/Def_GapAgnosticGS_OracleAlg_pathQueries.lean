-- Prove2me | Definitions.Def_GapAgnosticGS_OracleAlg_pathQueries
-- name    : GapAgnosticGS_OracleAlg_pathQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:49.412368+00:00
-- url     : https://prove2.me/theorems/e05f1c82-a1dd-4ff4-8c7c-7c7eeeaada31
-- title:
--   Number of queries made before reaching a history
-- statement:
--   For an adaptive oracle algorithm and a classical history $h$, the number of query steps the algorithm executes at the proper prefixes of $h$, i.e. the number of queries made before the run reaches $h$. It does not depend on the oracle; it is used to define the worst-case query count.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 3.15, p.14 (PDF p.15) (query counting in the worst case)

import Definitions.Def_GapAgnosticGS_OracleAlg

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc) (query counting of Theorem 3.15, p.14, PDF p.15). The number of query steps the
algorithm `A` executes before reaching the history `h`: the query steps at the proper prefixes
of `h`. It does not depend on the oracle. -/
def OracleAlg.pathQueries {Q Y O : Type} [Fintype Q] [DecidableEq Q] [Fintype Y]
    [DecidableEq Y] (A : OracleAlg Q Y O) : List ℕ → ℕ
  | [] => 0
  | _ :: h => OracleAlg.pathQueries A h + match A.step h with
      | .query _ => 1
      | _ => 0

end GapAgnosticGS


