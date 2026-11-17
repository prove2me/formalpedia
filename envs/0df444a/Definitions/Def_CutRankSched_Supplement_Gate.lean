-- Prove2me | Definitions.Def_CutRankSched_Supplement_Gate
-- name    : CutRankSched_Supplement_Gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:38:17.563953+00:00
-- url     : https://prove2.me/theorems/1b75f66b-d8cd-465a-807d-80cf795b86bc
-- title:
--   Clifford+$T/T^\dagger$ gates $H_q, S_q, \mathrm{CNOT}_{c,t}, T_q, T^\dagger_q$
-- statement:
--   A **gate** on $m$ qubits is one of: a Hadamard $H_q$, a phase gate $S_q$, a controlled-NOT $\mathrm{CNOT}_{c,t}$ with control $c$ and target $t\neq c$, a $T_q$ gate, or a $T^\dagger_q$ gate. The first three generate the Clifford group up to global phase; $T$ and $T^\dagger$ are the non-Clifford gates.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 4.1, p.6

import Mathlib

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The gates of a Clifford+T/T† circuit on `m` qubits (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §4.1, Theorem 4.1, p.6):
the Clifford generators `H_q`, `S_q`, `CNOT_{c,t}` (`c ≠ t`, control `c`, target `t`), and the
non-Clifford gates `T_q`, `T†_q`. -/
inductive Gate (m : ℕ) where
  | H (q : Fin m)
  | S (q : Fin m)
  | CNOT (c t : Fin m) (h : c ≠ t)
  | T (q : Fin m)
  | Tdg (q : Fin m)

end Supplement

end CutRankSched


