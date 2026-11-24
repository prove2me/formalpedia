-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_DualIncl
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_DualIncl
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:30.765003+00:00
-- url     : https://prove2.me/theorems/b1a5bfe5-8b39-4200-9eb0-26314b3bdbba
-- title:
--   Dual Incl
-- statement:
--   Definitions and structural lemmas for Dual Incl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/DualIncl.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix TensorProduct
namespace PI.UnitaryGroupMassFormula.LCG
namespace DualI
open Formalism.UG Formalism.UG.P
abbrev AA (I : Formalism.MainNotions.S.AutInst) : Type := I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F
abbrev SS (I : Formalism.MainNotions.S.AutInst) : Subring (AA I) := Formalism.MainNotions.S.IntAf I.F I.E
abbrev iA (I : Formalism.MainNotions.S.AutInst) : I.E →+* AA I := Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
end DualI
end PI.UnitaryGroupMassFormula.LCG


