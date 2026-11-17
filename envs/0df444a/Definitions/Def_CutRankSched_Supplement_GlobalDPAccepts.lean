-- Prove2me | Definitions.Def_CutRankSched_Supplement_GlobalDPAccepts
-- name    : CutRankSched_Supplement_GlobalDPAccepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:46:41.125008+00:00
-- url     : https://prove2.me/theorems/bcd0280d-3fde-4428-9b32-47e7b1bfafec
-- title:
--   Acceptance of the global-rank DP
-- statement:
--   The global-rank DP for the rank factorization $A=BC$ and budget $L$ **accepts** if its state set after the last event $n$ is nonempty.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 5.1, p.9

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Supplement_gdpSet

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The global-rank DP **accepts** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.2, Theorem 5.1, p.9) for the rank factorization
`A = BC`: its state set after the last event `n` is nonempty. -/
def GlobalDPAccepts (I : Instance) {r : ℕ} (L : ℕ) (B : Matrix (Fin I.n) (Fin r) (ZMod 2))
    (C : Matrix (Fin r) (Fin I.n) (ZMod 2)) : Prop :=
  (gdpSet I L B C I.n).Nonempty

end Supplement

end CutRankSched


