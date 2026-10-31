-- Prove2me | Definitions.Def_DynTargetMV_Market_xStar
-- name    : DynTargetMV_Market_xStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:33.593985+00:00
-- url     : https://prove2.me/theorems/332c9b15-0f8c-4384-8d26-34d57bf9b260
-- title:
--   $x^*(t)=\xi e^{-\int_t^Tr(s)ds}$
-- statement:
--   For an aspiration level $\xi$,
--   $$
--   x^*(t)=\xi\,e^{-\int_t^Tr(s)ds}
--   $$
--   is the wealth at time $t$ that grows to $\xi$ at the risk-free rate.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Theorem 1 (iii), p.10

import Definitions.Def_DynTargetMV_Market

namespace DynTargetMV

/-- `x*(t) = ξ e^{−∫_t^T r(s)ds}`, the wealth at `t` that grows to the aspiration level `ξ` at the
risk-free rate. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Theorem 1 (iii), p.10. -/
noncomputable def Market.xStar {m d n : ℕ} (M : Market m d n) (ξ t : ℝ) : ℝ :=
  ξ * Real.exp (-∫ s in t..M.T, M.r s)

end DynTargetMV


