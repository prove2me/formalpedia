-- Prove2me | Definitions.Def_DynTargetMV_Market_Hpremium
-- name    : DynTargetMV_Market_Hpremium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:51.327683+00:00
-- url     : https://prove2.me/theorems/1a49f688-758f-470c-adcd-87418e78ed31
-- title:
--   $H(t;\hat\pi)$, (C.17)
-- statement:
--   For a wealth-independent strategy $\hat\pi(s)$,
--   $$
--   H(t;\hat\pi):=e^{\int_t^Tr(s)ds}\int_t^Te^{-\int_t^sr(z)dz}b(s)^\top\hat\pi(s)\,ds-\bigl(e^{\int_t^T\psi(s)ds}-1\bigr)/\gamma .
--   $$
--   Feasibility for target (2.8) is $H(t;\hat\pi)\ge0$ on $[0,T)$, and $H(t;\hat\pi)=0$ means that the target binds at time $t$.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.17), p.28

import Definitions.Def_DynTargetMV_Market

open Matrix

namespace DynTargetMV

/-- `H(t;π̂) := e^{∫_t^T r(s)ds} ∫_t^T e^{−∫_t^s r(z)dz} b(s)⊤π̂(s)ds − (e^{∫_t^T ψ(s)ds} − 1)/γ`, (C.17), for a
wealth-independent strategy `p = π̂`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.17), p.28. -/
noncomputable def Market.Hpremium {m d n : ℕ} (M : Market m d n) (ψ : ℝ → ℝ) (γ : ℝ)
    (p : ℝ → Fin m → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∫ s in t..M.T, M.r s) *
      (∫ s in t..M.T, Real.exp (-∫ z in t..s, M.r z) * (M.b s ⬝ᵥ p s)) -
    (Real.exp (∫ s in t..M.T, ψ s) - 1) / γ

end DynTargetMV


