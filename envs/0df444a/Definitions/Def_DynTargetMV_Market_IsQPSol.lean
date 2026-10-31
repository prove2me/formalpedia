-- Prove2me | Definitions.Def_DynTargetMV_Market_IsQPSol
-- name    : DynTargetMV_Market_IsQPSol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:40:03.292425+00:00
-- url     : https://prove2.me/theorems/64072bc9-31f8-48a4-b867-c467b6bed789
-- title:
--   $v$ solves the quadratic program (2.10) at time $t$
-- statement:
--   At time $t$, the vector $v\in\mathbb R^m$ is the optimal solution of
--   $$
--   \min_{v\in\mathbb R^m}\ \tfrac12 v^\top\sigma(t)\sigma(t)^\top v\quad\text{subject to}\quad b(t)^\top v\ge\psi(t),\ Qv\ge0 .
--   $$
--   This static problem determines all three equilibrium strategies of Theorem 1.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.10), p.10

import Definitions.Def_DynTargetMV_halfQuad
import Definitions.Def_DynTargetMV_IsOptimal
import Definitions.Def_DynTargetMV_Market

open Matrix

namespace DynTargetMV

/-- `v` is the optimal solution of the quadratic program (2.10) at time `t`:
`min_v ½ v⊤σ(t)σ(t)⊤v` subject to `b(t)⊤v ≥ ψ(t)`, `Qv ≥ 0`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.10), p.10. -/
def Market.IsQPSol {m d n : ℕ} (M : Market m d n) (ψ : ℝ → ℝ) (t : ℝ) (v : Fin m → ℝ) : Prop :=
  IsOptimal (halfQuad (M.σ t * (M.σ t)ᵀ)) {w | ψ t ≤ M.b t ⬝ᵥ w ∧ 0 ≤ M.Q *ᵥ w} v

end DynTargetMV


