-- Prove2me | Definitions.Def_DynTargetMV_Market_Hbar
-- name    : DynTargetMV_Market_Hbar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:54.495082+00:00
-- url     : https://prove2.me/theorems/e0344dcc-1f5c-4cc8-b63f-bb3a82af33c3
-- title:
--   $\bar H(t;\hat v)$, (C.21)
-- statement:
--   For a function $\hat v$,
--   $$
--   \bar H(t;\hat v):=\int_t^Tb(s)^\top\hat v(s)\,ds-\int_t^T\psi(s)\,ds .
--   $$
--   For target (2.9), $\bar H(t;\hat v)\ge0$ on $[0,T)$ is the feasibility of $\hat\pi(t,x)=\hat v(t)(x^*(t)-x)$, and $\bar H(t;\hat v)=0$ means that the target binds at time $t$.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.21), p.29

import Definitions.Def_DynTargetMV_Market

open Matrix

namespace DynTargetMV

/-- `H̄(t;v̂) := ∫_t^T b(s)⊤v̂(s)ds − ∫_t^T ψ(s)ds`, (C.21). He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.21), p.29. -/
noncomputable def Market.Hbar {m d n : ℕ} (M : Market m d n) (ψ : ℝ → ℝ) (v : ℝ → Fin m → ℝ)
    (t : ℝ) : ℝ :=
  (∫ s in t..M.T, M.b s ⬝ᵥ v s) - ∫ s in t..M.T, ψ s

end DynTargetMV


