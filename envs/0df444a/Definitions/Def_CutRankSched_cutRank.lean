-- Prove2me | Definitions.Def_CutRankSched_cutRank
-- name    : CutRankSched_cutRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:34:00.940827+00:00
-- url     : https://prove2.me/theorems/a01f11d7-737d-4967-9857-ef8c438fbdb6
-- title:
--   Maximum prefix–suffix cut rank $\kappa_\pi$
-- statement:
--   The **cut rank** of the fixed order is
--   $$
--   \kappa_\pi = \max_{0 \le k \le n} \operatorname{rank}_{\mathbb F_2}(A_k) ,
--   $$
--   the largest $\mathbb F_2$-rank of a cross matrix. The cuts $k = 0$ and $k = n$ (empty matrices, rank $0$) are included. One has $\kappa_\pi \le \operatorname{rank}(A) \le 2m$, and $\kappa_\pi$ need not be even.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.3, Eq. (3), p.5

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_cross

set_option autoImplicit false

namespace CutRankSched

/-- The maximum prefix–suffix cut rank `κ_π = max_{0 ≤ k ≤ n} rank_{𝔽₂}(A_k)`
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.3, Eq. (3), p.5). The cuts `k = 0` and `k = n` are included (rank `0`). -/
noncomputable def cutRank (I : Instance) : ℕ :=
  (Finset.range (I.n + 1)).sup fun k => (cross I k).rank

end CutRankSched


