-- Prove2me | Definitions.Def_CutRankSched_Feasible
-- name    : CutRankSched_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:35:02.648552+00:00
-- url     : https://prove2.me/theorems/090609e3-6ec4-4b82-bd55-c2b71c62642b
-- title:
--   Feasibility in $L$ rounds (Problem 3.2)
-- statement:
--   An instance is **feasible in $L$ rounds** if there is a map $\lambda : [n] \to [L]$ satisfying the constraints (2). Problem 3.2 asks, given the instance and a positive integer $L$, to decide feasibility.
--
--   When $n = 0$ the empty assignment is feasible for every $L$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Problem 3.2, p.5

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_IsSchedule

set_option autoImplicit false

namespace CutRankSched

/-- Feasibility in `L` rounds, the decision question of Problem 3.2 (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Problem 3.2, p.5):
there is a map `λ : [n] → [L]` satisfying (2). -/
def Feasible (I : Instance) (L : ℕ) : Prop :=
  ∃ lam : Fin I.n → Fin L, IsSchedule I L lam

end CutRankSched


