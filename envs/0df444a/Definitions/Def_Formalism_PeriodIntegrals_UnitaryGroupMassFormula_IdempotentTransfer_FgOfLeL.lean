-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_FgOfLeL
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_FgOfLeL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:00:47.645281+00:00
-- url     : https://prove2.me/theorems/851491ef-0aef-431c-8195-036fc593ddfe
-- title:
--   Fg Of Le L
-- statement:
--   Definitions and structural lemmas for Fg Of Le L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/FgOfLeL.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.Tr
open PI.Dv Module NumberField
section Conv
variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
def kap (K : Type) [Field K] [NumberField K] : ℝ := Formalism.HN.logDisc K / (finrank ℚ K : ℝ) - Real.log 2
end Conv
end PI.Dv.Tr


