-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_ExistsGlOfLeftInv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_ExistsGlOfLeftInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:14.597049+00:00
-- url     : https://prove2.me/theorems/ff994292-3c8b-4f6e-b9a4-b3132cd9da29
-- title:
--   Exists Gl Of Left Inv
-- statement:
--   Definitions and structural lemmas for Exists Gl Of Left Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/ExistsGlOfLeftInv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace MassDataIdxAdA
open Matrix
variable {K : Type*} [Field K] (O : ValuationSubring K) {ι : Type*} [Fintype ι] [DecidableEq ι]
end MassDataIdxAdA


