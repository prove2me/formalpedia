-- Prove2me | Definitions.Def_CutRankSched_splice
-- name    : CutRankSched_splice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:26.367741+00:00
-- url     : https://prove2.me/theorems/9a380146-f805-413e-ac5e-745ae0be091f
-- title:
--   Prefix–suffix splice of two assignments
-- statement:
--   For a cut $k$ and two layer assignments $\lambda, \mu$, the **splice** follows $\lambda$ on the first $k$ events and $\mu$ on the rest:
--   $$
--   (\lambda \mid_k \mu)_j = \begin{cases} \lambda_j & j \le k, \\ \mu_j & j > k. \end{cases}
--   $$
--   It expresses "a partial assignment completed by a suffix assignment" in the safe-state-merging argument.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), proof of Theorem 5.2, p.10

import Mathlib

set_option autoImplicit false

namespace CutRankSched

/-- The assignment that follows `lam` on the first `k` events and `mu` on the suffix
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), proof of Theorem 5.2, safe state merging, p.10). -/
def splice {n L : ℕ} (k : ℕ) (lam mu : Fin n → Fin L) : Fin n → Fin L :=
  fun j => if j.val < k then lam j else mu j

end CutRankSched


