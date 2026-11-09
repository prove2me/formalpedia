-- Prove2me | Definitions.Def_CutRankSched_cross
-- name    : CutRankSched_cross
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:32:43.711314+00:00
-- url     : https://prove2.me/theorems/bce31b2e-eccb-4f83-a468-927421a6b478
-- title:
--   Cross matrix $A_k=A[[k],\{k+1,\dots,n\}]$
-- statement:
--   For $0 \le k \le n$, the **cross matrix** at cut $k$ is the submatrix
--   $$
--   A_k = A[[k], \{k+1, \dots, n\}]
--   $$
--   of the anticommutation matrix with rows the first $k$ events and columns the remaining $n - k$ events.
--
--   **Formalization Note** 0-based: rows are the events `a` with `a.val < k`, columns those with `k ≤ b.val`.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.3, Eq. (3), p.5

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A

set_option autoImplicit false

namespace CutRankSched

/-- The cross matrix `A_k = A[[k], {k+1, …, n}]` (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.3, Eq. (3), p.5): rows the first
`k` events, columns the remaining ones.

**Formalization Note** 0-based: rows `a.val < k`, columns `k ≤ b.val`. -/
def cross (I : Instance) (k : ℕ) :
    Matrix {a : Fin I.n // a.val < k} {b : Fin I.n // k ≤ b.val} (ZMod 2) :=
  fun a b => A I a.1 b.1

end CutRankSched


