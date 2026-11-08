-- Prove2me | Definitions.Def_MantriCVQ_queryCount
-- name    : MantriCVQ_queryCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:13.940125+00:00
-- url     : https://prove2.me/theorems/ad8031d0-72d1-43f1-8f33-89b2f56a995d
-- title:
--   Oracle queries of a machine
-- statement:
--   The number of oracle queries a machine makes on an input in its first $T$ steps: the number of steps at which it is in the query state. Theorem 5.5 (iii) bounds this count for the verifier.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 5.5 (iii), p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- The number of oracle queries an oracle machine makes on input `s` in its first `T` steps: the
number of steps at which it is in the query state (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), Theorem 5.5 (iii), p. 22 (PDF p. 24)). -/
def queryCount (M : OTM) (O : Oracle) (s : Str) (T : ℕ) : ℕ :=
  ((List.range T).filter fun t => decide ((M.runCfg O s t).state = 3)).length

end MantriCVQ


