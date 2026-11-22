-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HilbertSchmidtBlocks_HSBlocksMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HilbertSchmidtBlocks_HSBlocksMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:33.286408+00:00
-- url     : https://prove2.me/theorems/6786e2c3-5b60-4852-9455-c00729c85dd9
-- title:
--   HSBlocks Main
-- statement:
--   Definitions and structural lemmas for HSBlocks Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HilbertSchmidtBlocks/HSBlocksMain.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HilbertSchmidtBlocks_Change
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
namespace NormHilbertSchmidtBlocks
open Formalism.L2.SG.NormCut
end NormHilbertSchmidtBlocks


