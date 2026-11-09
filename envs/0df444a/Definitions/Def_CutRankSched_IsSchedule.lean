-- Prove2me | Definitions.Def_CutRankSched_IsSchedule
-- name    : CutRankSched_IsSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:33:53.767018+00:00
-- url     : https://prove2.me/theorems/a24c0905-3dcd-4799-9cfa-3487036d31c4
-- title:
--   Layer assignment satisfying (2)
-- statement:
--   A map $\lambda : [n] \to [L]$ is a **schedule** (satisfies the constraints (2) of Problem 3.2) if
--   $$
--   A_{ij} = 1,\ i < j \implies \lambda_i < \lambda_j, \qquad \{i, j\} \in E(X^\circ) \implies \lambda_i \ne \lambda_j .
--   $$
--   Anticommuting events keep their trace order; commuting events with overlapping exposure regions occupy different rounds. Layers need not be monotone along the trace.
--
--   **Formalization Note** Events and layers are 0-based: $\lambda$ is a map `Fin n → Fin L`, and layer `t` is the paper's layer $t+1$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Problem 3.2, Eq. (2), p.5

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_Residual

set_option autoImplicit false

namespace CutRankSched

/-- A layer assignment `λ : [n] → [L]` satisfying the constraints (2) of Problem 3.2
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Problem 3.2, Eq. (2), p.5):
`A_ij = 1, i < j ⟹ λ_i < λ_j` and `{i, j} ∈ E(X°) ⟹ λ_i ≠ λ_j`.

**Formalization Note** Events and layers are 0-based (`Fin n`, `Fin L`); layer `t : Fin L` is the
paper's layer `t + 1`. Layers need not be monotone along the trace. -/
def IsSchedule (I : Instance) (L : ℕ) (lam : Fin I.n → Fin L) : Prop :=
  (∀ i j : Fin I.n, i < j → A I i j = 1 → lam i < lam j) ∧
    ∀ i j : Fin I.n, Residual I i j → lam i ≠ lam j

end CutRankSched


