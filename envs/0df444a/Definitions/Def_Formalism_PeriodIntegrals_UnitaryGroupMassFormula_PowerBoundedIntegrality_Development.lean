-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerBoundedIntegrality_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerBoundedIntegrality_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:38.925638+00:00
-- url     : https://prove2.me/theorems/2ac1d238-47b0-4a6a-8d13-3dd66f005823
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerBoundedIntegrality/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PowBddInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.PowBddIntWork
open Matrix
def StepA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (γ : Matrix (Fin k) (Fin k) E) (N : ℕ), 0 < N →
    (∀ (n : ℕ) (i j : Fin k), IsIntegral ℤ ((N : E) * (γ ^ n) i j)) → IsIntegral ℤ γ
def StepB : Prop :=
  ∀ (E : Type) [Field E] (k : ℕ) (γ : Matrix (Fin k) (Fin k) E), IsIntegral ℤ γ →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i)
end PI.PowBddIntWork


