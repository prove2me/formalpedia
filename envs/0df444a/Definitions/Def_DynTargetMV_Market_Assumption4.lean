-- Prove2me | Definitions.Def_DynTargetMV_Market_Assumption4
-- name    : DynTargetMV_Market_Assumption4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:40.228109+00:00
-- url     : https://prove2.me/theorems/0f42b6bd-31e8-4775-ad82-49a8eeca09cc
-- title:
--   Assumption 4 — $\int_0^T\|v^*(t)\|^2dt<+\infty$
-- statement:
--   The solution $v^*$ of (2.10) is square-integrable:
--   $$
--   \int_0^T\|v^*(t)\|^2\,dt<+\infty .
--   $$
--   **Formalization Note** The predicate is stated for a function $v$ on $[0,T)$. The theorems apply it to the solution of (2.10).
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Assumption 4, p.10

import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_Market

open MeasureTheory Set

namespace DynTargetMV

/-- **Assumption 4.** `∫₀ᵀ ‖v*(t)‖² dt < +∞`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Assumption 4, p.10.

**Formalization Note** Stated for a function `v`; the statements apply it to a selection of the
solutions of (2.10). The integrability on `[0,T)` of `‖v‖²` includes its a.e. measurability, which
for `v*` holds by right-continuity. -/
def Market.Assumption4 {m d n : ℕ} (M : Market m d n) (v : ℝ → Fin m → ℝ) : Prop :=
  IntegrableOn (fun t => sqNorm (v t)) (Ico 0 M.T)

end DynTargetMV


