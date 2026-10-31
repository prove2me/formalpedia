-- Prove2me | Definitions.Def_DynTargetMV_Market_phiGap
-- name    : DynTargetMV_Market_phiGap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:50.935043+00:00
-- url     : https://prove2.me/theorems/4e0d3bcc-deb6-44d1-83b8-68f0ac18432a
-- title:
--   $\varphi(t;u)=1-e^{-\int_t^T\|\sigma(s)^\top u(s)\|^2ds}$, (C.12)
-- statement:
--   For a function $u$,
--   $$
--   \varphi(t;u):=1-e^{-\int_t^T\|\sigma(s)^\top u(s)\|^2ds}\in[0,1).
--   $$
--   It is the coefficient of the linear term of (C.14). The coefficient (C.23) of (C.22) is its negative.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.12), p.27; (C.23), p.30

import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_Market

open Matrix

namespace DynTargetMV

/-- `φ(t;u) := 1 − e^{−∫_t^T ‖σ(s)⊤u(s)‖²ds}`, the coefficient `φ(t;û)` of (C.12), p.27; (C.23), p.30,
is its negative. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.12), p.27. -/
noncomputable def Market.phiGap {m d n : ℕ} (M : Market m d n) (u : ℝ → Fin m → ℝ) (t : ℝ) : ℝ :=
  1 - Real.exp (-∫ s in t..M.T, sqNorm ((M.σ s)ᵀ *ᵥ u s))

end DynTargetMV


