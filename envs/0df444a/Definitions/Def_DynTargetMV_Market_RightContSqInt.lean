-- Prove2me | Definitions.Def_DynTargetMV_Market_RightContSqInt
-- name    : DynTargetMV_Market_RightContSqInt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:53.079144+00:00
-- url     : https://prove2.me/theorems/16399863-d182-426a-a66d-8a8984789b3f
-- title:
--   Right-continuous and square-integrable in $t\in[0,T)$
-- statement:
--   A function $u:[0,T)\to\mathbb R^m$ belongs to this class if it is right-continuous and $\int_0^T\|u(t)\|^2dt<+\infty$. It is the regularity of the uniqueness classes of Theorem 1.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Theorem 1, p.10

import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_Market

open MeasureTheory Set

namespace DynTargetMV

/-- `u` is right-continuous and square-integrable in `t ∈ [0,T)`, the regularity of the uniqueness
classes of Theorem 1. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Theorem 1, p.10.

**Formalization Note** Right-continuity entry by entry; square-integrability for Lebesgue measure on
`[0,T)`, with the Euclidean norm. Only the values of `u` on `[0,T)` matter. -/
def Market.RightContSqInt {m d n : ℕ} (M : Market m d n) (u : ℝ → Fin m → ℝ) : Prop :=
  (∀ t ∈ Ico 0 M.T, ∀ i, ContinuousWithinAt (fun s => u s i) (Ici t) t) ∧
  IntegrableOn (fun s => sqNorm (u s)) (Ico 0 M.T)

end DynTargetMV


