-- Prove2me | Definitions.Def_DynTargetMV_Market_Assumption3
-- name    : DynTargetMV_Market_Assumption3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:23.264498+00:00
-- url     : https://prove2.me/theorems/2385cb06-3dc3-4fae-b699-04a941f51551
-- title:
--   Assumption 3 — $\psi$ nonnegative, right-continuous, integrable on $[0,T)$
-- statement:
--   The function $\psi$ of the targets (2.7)–(2.9) is nonnegative, right-continuous, and integrable in $t\in[0,T)$.
--
--   **Formalization Note** Integrability is for Lebesgue measure on $[0,T)$. The function $\psi$ need not be bounded and may blow up at $T$.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Assumption 3, p.10

import Definitions.Def_DynTargetMV_Market

open MeasureTheory Set

namespace DynTargetMV

/-- **Assumption 3.** `ψ` is nonnegative, right-continuous, and integrable in `t ∈ [0,T)`.
He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Assumption 3, p.10.

**Formalization Note** Integrability is `L¹` for Lebesgue measure on `[0,T)`. `ψ` need not be bounded
and may blow up at `T`; its values outside `[0,T)` play no role. -/
structure Market.Assumption3 {m d n : ℕ} (M : Market m d n) (ψ : ℝ → ℝ) : Prop where
  /-- `ψ` is nonnegative on `[0,T)`. -/
  nonneg : ∀ t ∈ Ico 0 M.T, 0 ≤ ψ t
  /-- `ψ` is right-continuous on `[0,T)`. -/
  rightCont : ∀ t ∈ Ico 0 M.T, ContinuousWithinAt ψ (Ici t) t
  /-- `ψ` is integrable on `[0,T)`. -/
  integrable : IntegrableOn ψ (Ico 0 M.T)

end DynTargetMV


