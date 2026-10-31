-- Prove2me | Definitions.Def_DynTargetMV_Market_targetAspiration
-- name    : DynTargetMV_Market_targetAspiration
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:40:20.504009+00:00
-- url     : https://prove2.me/theorems/2eac4020-be36-4c84-b6a9-94a84895fbb3
-- title:
--   The aspiration target (2.9)
-- statement:
--   The target for the expected terminal wealth, for an aspiration level $\xi$,
--   $$
--   L(t,x)=e^{-\int_t^T\psi(s)ds}\,x\,e^{\int_t^Tr(s)ds}+\bigl(1-e^{-\int_t^T\psi(s)ds}\bigr)\xi,\quad t\in[0,T),\ x\in\mathbb R ,
--   $$
--   a weighted average of the risk-free payoff of the current wealth and $\xi$.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.9), p.9

import Definitions.Def_DynTargetMV_Market

namespace DynTargetMV

/-- The aspiration target (2.9):
`L(t,x) = e^{−∫_t^T ψ(s)ds} x e^{∫_t^T r(s)ds} + (1 − e^{−∫_t^T ψ(s)ds}) ξ`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.9), p.9. -/
noncomputable def Market.targetAspiration {m d n : ℕ} (M : Market m d n) (ψ : ℝ → ℝ) (ξ t x : ℝ) :
    ℝ :=
  Real.exp (-∫ s in t..M.T, ψ s) * x * Real.exp (∫ s in t..M.T, M.r s) +
    (1 - Real.exp (-∫ s in t..M.T, ψ s)) * ξ

end DynTargetMV


