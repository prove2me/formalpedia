-- Prove2me | Definitions.Def_DynTargetMV_Market_targetPremium
-- name    : DynTargetMV_Market_targetPremium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:43.40957+00:00
-- url     : https://prove2.me/theorems/70f468ef-50a8-4747-aaa2-8ebde5d22792
-- title:
--   The premium target (2.8)
-- statement:
--   The target for the expected terminal wealth, for some $\gamma>0$,
--   $$
--   L(t,x)=\frac1\gamma\bigl(e^{\int_t^T\psi(s)ds}-1\bigr)+x\,e^{\int_t^Tr(s)ds},\quad t\in[0,T),\ x\in\mathbb R ,
--   $$
--   the risk-free return of the current wealth plus a premium.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.8), p.9

import Definitions.Def_DynTargetMV_Market

namespace DynTargetMV

/-- The premium target (2.8): `L(t,x) = (1/γ)(e^{∫_t^T ψ(s)ds} − 1) + x e^{∫_t^T r(s)ds}`.
He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.8), p.9. -/
noncomputable def Market.targetPremium {m d n : ℕ} (M : Market m d n) (ψ : ℝ → ℝ) (γ t x : ℝ) : ℝ :=
  (1 / γ) * (Real.exp (∫ s in t..M.T, ψ s) - 1) + x * Real.exp (∫ s in t..M.T, M.r s)

end DynTargetMV


