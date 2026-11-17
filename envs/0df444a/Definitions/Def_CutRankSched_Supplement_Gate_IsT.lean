-- Prove2me | Definitions.Def_CutRankSched_Supplement_Gate_IsT
-- name    : CutRankSched_Supplement_Gate_IsT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:41:27.705057+00:00
-- url     : https://prove2.me/theorems/2c363771-c5b3-4e10-a6f2-3b67983b37de
-- title:
--   Non-Clifford gates $T_q$, $T^\dagger_q$
-- statement:
--   A gate is a **non-Clifford occurrence** if it is a $T_q$ or a $T^\dagger_q$ gate. The number of such gates in a circuit is its number of input $T/T^\dagger$ occurrences.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 4.1, p.6

import Mathlib
import Definitions.Def_CutRankSched_Supplement_Gate

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- Whether a gate is a non-Clifford `T_q` or `T†_q` gate (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 4.1, p.6: "the number of
input T/T† occurrences"). -/
def Gate.IsT {m : ℕ} : Gate m → Bool
  | .T _ => true
  | .Tdg _ => true
  | _ => false

end Supplement

end CutRankSched


