-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:23.232341+00:00
-- url     : https://prove2.me/theorems/409eb989-f74c-4f49-a7a8-e3c58bc79dc2
-- title:
--   Charpoly Dvd Of Pow Eq One
-- statement:
--   Definitions and structural lemmas for Charpoly Dvd Of Pow Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.Mk
open Polynomial Matrix
def Good (ℓ : ℕ) (p : ℚ[X]) : Prop :=
  p.Monic ∧ ∃ y : ℕ, (ℓ - 1) * y ≤ p.natDegree ∧
    -p.nextCoeff = (p.natDegree : ℚ) - (ℓ : ℚ) * (y : ℚ) ∧ (y = 0 → p = (X - 1) ^ p.natDegree)
end PI.Mk


