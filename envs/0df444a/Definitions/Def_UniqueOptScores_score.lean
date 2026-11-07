-- Prove2me | Definitions.Def_UniqueOptScores_score
-- name    : UniqueOptScores_score
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:03.358414+00:00
-- url     : https://prove2.me/theorems/c43ff041-d39c-49e9-869b-fe02250791c4
-- title:
--   Score of a candidate, out-of-range values replaced by $0$
-- statement:
--   For an evaluator $E$ (a clocked deterministic oracle machine), an oracle $A$, a score ceiling $K$, an input $x$ and a candidate $z$, the **score** $s^A(x, z)$ is the number written by $E^A$ on input $\langle x, z\rangle$ if it is at most $K$, and $0$ otherwise:
--   $$
--   s^A_K(x, z) = \begin{cases} \mathrm{num}\big(E^A(\langle x, z\rangle)\big) & \text{if this is } \le K,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   This implements "A timeout, malformed output, or out-of-range score is replaced by zero" (Definition 4.1); timeouts cannot occur for clocked evaluators.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Definition 4.1, p.16

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_output
import Definitions.Def_UniqueOptScores_pair
import Definitions.Def_UniqueOptScores_decodeNat

namespace UniqueOptScores

/-- **The score of a candidate, with out-of-range values replaced by zero.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Definition 4.1, p.16: "A timeout, malformed output, or out-of-range score is replaced by
zero."

`score E A K x z` is the number written by the evaluator `E` on input `⟨x, z⟩` with oracle `A` if it
is at most `K`, and `0` otherwise. -/
noncomputable def score (E : HMBinPacking.OracleMachine) (A : Set (List Bool)) (K : ℕ)
    (x z : List Bool) : ℕ :=
  if decodeNat (output E A (pair x z)) ≤ K then decodeNat (output E A (pair x z)) else 0

end UniqueOptScores


