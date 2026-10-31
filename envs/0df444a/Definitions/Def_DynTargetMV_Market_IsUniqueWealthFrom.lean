-- Prove2me | Definitions.Def_DynTargetMV_Market_IsUniqueWealthFrom
-- name    : DynTargetMV_Market_IsUniqueWealthFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:40:44.590442+00:00
-- url     : https://prove2.me/theorems/8b2c8ce9-a543-4bb7-9d6b-04a0fdc6e8f7
-- title:
--   $X$ is the unique strong solution of the wealth equation from $(t,x)$
-- statement:
--   The process $X$ solves the wealth equation of $\pi$ from $(t,x)$, and any other solution is indistinguishable from it on $[t,T]$. This is the "unique strong solution" of p.7.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.7

import Definitions.Def_DynTargetMV_Market_IsWealthFrom

open MeasureTheory Set

namespace DynTargetMV

/-- `X` is the unique strong solution of the wealth equation of `π` from `(t,x)`: any other solution
is indistinguishable from it on `[t,T]`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.7 ("has a unique strong solution"). -/
def Market.IsUniqueWealthFrom {m d n : ℕ} (M : Market m d n) {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (F : Filtration ℝ mΩ) (W : Fin d → ℝ → Ω → ℝ)
    (π : ℝ → ℝ → Fin m → ℝ) (t x : ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  M.IsWealthFrom P F W π t x X ∧
  ∀ Y, M.IsWealthFrom P F W π t x Y → ∀ᵐ ω ∂P, ∀ s ∈ Icc t M.T, Y s ω = X s ω

end DynTargetMV


