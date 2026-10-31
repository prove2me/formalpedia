-- Prove2me | Definitions.Def_DynTargetMV_Market_targetGross
-- name    : DynTargetMV_Market_targetGross
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:32.927306+00:00
-- url     : https://prove2.me/theorems/d2de5e29-c7fe-457a-aad7-92651854eefd
-- title:
--   The gross-return target (2.7)
-- statement:
--   The target for the expected terminal wealth
--   $$
--   L(t,x)=x\,e^{\int_t^T[r(s)+\psi(s)]ds},\quad t\in[0,T),\ x\in\mathbb R ,
--   $$
--   under which the target gross return is independent of wealth.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.7), p.9

import Definitions.Def_DynTargetMV_Market

namespace DynTargetMV

/-- The gross-return target (2.7): `L(t,x) = x e^{∫_t^T [r(s)+ψ(s)]ds}`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.7), p.9. -/
noncomputable def Market.targetGross {m d n : ℕ} (M : Market m d n) (ψ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  x * Real.exp (∫ s in t..M.T, (M.r s + ψ s))

end DynTargetMV


