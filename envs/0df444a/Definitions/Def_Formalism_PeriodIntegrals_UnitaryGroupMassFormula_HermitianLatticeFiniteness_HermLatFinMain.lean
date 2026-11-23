-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HermLatFinMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HermLatFinMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:00.333808+00:00
-- url     : https://prove2.me/theorems/581be42f-392f-43bd-a7c0-24fe65228fe2
-- title:
--   Herm Lat Fin Main
-- statement:
--   Definitions and structural lemmas for Herm Lat Fin Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianLatticeFiniteness/HermLatFinMain.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ShortVectors
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomOfTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexOrder
noncomputable section
namespace PI.HermLatFin.UnitaryGroupMassFormula
variable {E : Type} [Field E] [NumberField E]
section Covol
variable [StarRing E] {n : ℕ}
end Covol
end PI.HermLatFin.UnitaryGroupMassFormula


