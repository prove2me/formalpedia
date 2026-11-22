-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowWeightSpan_RowWtSpanOfBideterminant
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowWeightSpan_RowWtSpanOfBideterminant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:02.545518+00:00
-- url     : https://prove2.me/theorems/078db1e8-f5e3-4c5e-8c27-9a93468cdafa
-- title:
--   Row Wt Span Of Bideterminant
-- statement:
--   Definitions and structural lemmas for Row Wt Span Of Bideterminant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowWeightSpan/RowWtSpanOfBideterminant.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowWtSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.RWS
open PI.RW
def rowW {k : ℕ} (a : Fin k) : Fin k × Fin k → ℕ := fun v => if v.1 = a then 1 else 0
def Data (m : ℕ) (ν : Fin (m + 1) → ℕ) : Type :=
  {d : Σ N : ℕ, Σ sz : Fin N → ℕ, ∀ j, Fin (sz j) → Fin (m + 1) //
    (∀ j, d.2.1 j ≤ m + 1) ∧ shapeDeg d.2.1 = ν ∧ ∀ j, StrictMono (d.2.2 j)}
end PI.RWS


