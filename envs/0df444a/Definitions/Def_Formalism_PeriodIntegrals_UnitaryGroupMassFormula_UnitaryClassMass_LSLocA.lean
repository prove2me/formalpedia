-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSLocA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSLocA
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:32:29.005588+00:00
-- url     : https://prove2.me/theorems/d7d53035-c9bd-4d65-ac6c-394a350ddf77
-- title:
--   LSLoc A
-- statement:
--   Definitions and structural lemmas for LSLoc A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSLocA.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_SigRTmulOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
end PI.UnitaryGroupMassFormula.UJClassMass


