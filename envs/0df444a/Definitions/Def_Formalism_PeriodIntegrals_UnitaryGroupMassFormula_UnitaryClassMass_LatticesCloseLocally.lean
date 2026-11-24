-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LatticesCloseLocally
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LatticesCloseLocally
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:18:45.993573+00:00
-- url     : https://prove2.me/theorems/0d52e7e7-e28a-4289-a70b-88e6c7dfc554
-- title:
--   Lattices Close Locally
-- statement:
--   Definitions and structural lemmas for Lattices Close Locally, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LatticesCloseLocally.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermCL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
section Lin
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {M : ℕ}
end Lin
end PI.UnitaryGroupMassFormula.UJClassMass


