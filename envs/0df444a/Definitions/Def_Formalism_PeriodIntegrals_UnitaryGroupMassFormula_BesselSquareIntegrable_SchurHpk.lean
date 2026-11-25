-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpk
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpk
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:37:03.988583+00:00
-- url     : https://prove2.me/theorems/f5e8b38f-59b4-4d46-9700-f98b700901ba
-- title:
--   Schur Hpk
-- statement:
--   Definitions and structural lemmas for Schur Hpk, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselSquareIntegrable/SchurHpk.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselL2FixAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Closed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.BesselL2FixAtZero
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal
open PI.UpqRep PI.BesselL2FixAtZero
section Transport
variable {n : ℕ} (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ)
def conjPrime₂ (g : UJ ε) : Fin n → Fin n → ℂ := Matrix.of.symm (P⁻¹ * toM g * P)
end Transport
end PI.UnitaryGroupMassFormula.BesselL2FixAtZero


