-- Prove2me | Definitions.Def_KarpLiptonOM_OracleTM_trace
-- name    : KarpLiptonOM_OracleTM_trace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:02.8631+00:00
-- url     : https://prove2.me/theorems/072f2979-2000-48cf-8891-9378c30335c4
-- title:
--   Query trace of an oracle machine
-- statement:
--   The **query trace** of an oracle machine with oracle $O$ over $t$ steps from a configuration $c$ is the list, in order of asking, of the strings on the query tape at the steps where the machine is in the query state. It records exactly which oracle questions a computation asks.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Lemma A.3.9, p.28 (the queries of the canonical-circuit machine)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_step
import Definitions.Def_KarpLiptonOM_Tape_bits

namespace KarpLiptonOM

/-- The **query trace**: the list, in order, of the query strings asked during the first `t` steps
from configuration `c` with oracle `O` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Lemma A.3.9, p.28: "queries `1^π(n,1), …, 1^π(n,ℓ(n))`"). -/
noncomputable def OracleTM.trace (M : OracleTM) (O : Set (List Bool)) :
    ℕ → M.Cfg → List (List Bool)
  | 0, _ => []
  | t + 1, c => by
    classical exact
      (if c.state = M.qquery ∧ ¬ (c.state = M.qaccept ∨ c.state = M.qreject)
        then [c.query.bits M.ι] else []) ++ M.trace O t (M.step O c)

end KarpLiptonOM


