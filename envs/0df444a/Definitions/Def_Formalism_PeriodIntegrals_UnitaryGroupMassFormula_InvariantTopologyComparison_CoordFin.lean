-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFin
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFin
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:32:25.193693+00:00
-- url     : https://prove2.me/theorems/ce057ece-32e4-44ed-bb45-1c685bc8a960
-- title:
--   Coord Fin
-- statement:
--   Definitions and structural lemmas for Coord Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/CoordFin.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
end PI.InvTopW


