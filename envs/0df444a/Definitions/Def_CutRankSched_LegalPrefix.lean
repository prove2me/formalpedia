-- Prove2me | Definitions.Def_CutRankSched_LegalPrefix
-- name    : CutRankSched_LegalPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:34:07.355351+00:00
-- url     : https://prove2.me/theorems/71f508b8-2536-4f77-b944-528e88f6f9e5
-- title:
--   Constraints (2) on the first $k$ events
-- statement:
--   A layer assignment is **legal on the first $k$ events** if the constraints (2) hold for all pairs of events among the first $k$:
--   $$
--   A_{ij} = 1,\ i < j \le k \implies \lambda_i < \lambda_j, \qquad \{i, j\} \in E(X^\circ),\ i, j \le k \implies \lambda_i \ne \lambda_j .
--   $$
--   These are the partial assignments the proof of Theorem 5.2 tracks at cut $k$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Problem 3.2, Eq. (2), p.5; proof of Theorem 5.2, p.10

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_Residual

set_option autoImplicit false

namespace CutRankSched

/-- The constraints (2) restricted to the first `k` events (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Problem 3.2, Eq. (2), p.5,
as used in the proof of Theorem 5.2, p.10): a partial assignment is legal so far. -/
def LegalPrefix (I : Instance) (L k : ℕ) (lam : Fin I.n → Fin L) : Prop :=
  (∀ i j : Fin I.n, i.val < k → j.val < k → i < j → A I i j = 1 → lam i < lam j) ∧
    ∀ i j : Fin I.n, i.val < k → j.val < k → Residual I i j → lam i ≠ lam j

end CutRankSched


