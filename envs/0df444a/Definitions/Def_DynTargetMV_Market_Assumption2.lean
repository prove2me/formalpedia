-- Prove2me | Definitions.Def_DynTargetMV_Market_Assumption2
-- name    : DynTargetMV_Market_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:13.988956+00:00
-- url     : https://prove2.me/theorems/afea124d-87e0-434d-ac15-d5a3745b5594
-- title:
--   Assumption 2 — $\{y\mid b(t)^\top y>0,\ Qy\ge0\}\neq\emptyset$
-- statement:
--   For any $t\in[0,T)$, the set
--   $$
--   \{y\in\mathbb R^m\mid b(t)^\top y>0,\ Qy\ge0\}
--   $$
--   is nonempty. This says that the portfolio constraints leave a way to earn a positive expected excess return, and it makes (2.10) feasible.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Assumption 2, p.9

import Definitions.Def_DynTargetMV_Market

open Set Matrix

namespace DynTargetMV

/-- **Assumption 2.** For any `t ∈ [0,T)`, the set `{y ∈ ℝ^m | b(t)⊤y > 0, Qy ≥ 0}` is nonempty.
He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Assumption 2, p.9.

**Formalization Note** `Qy ≥ 0` is the coordinatewise order on `Fin n → ℝ`. -/
def Market.Assumption2 {m d n : ℕ} (M : Market m d n) : Prop :=
  ∀ t ∈ Ico 0 M.T, ∃ y : Fin m → ℝ, 0 < M.b t ⬝ᵥ y ∧ 0 ≤ M.Q *ᵥ y

end DynTargetMV


