-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:58.369122+00:00
-- url     : https://prove2.me/theorems/d2755f6c-b1d1-4542-8e5f-a97af6a0858a
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace PI.UnitaryApproxFinWork
def TopStep : Prop := CayleyFin → EigAvoid → PI.UnitaryApproxFin.UnitaryApproxFin
def CayleyStep : Prop := ApproxE → BddR → UnitS → CayleyFin
def ApproxEStep : Prop := WeakApproxF → ApproxE
end PI.UnitaryApproxFinWork
end


