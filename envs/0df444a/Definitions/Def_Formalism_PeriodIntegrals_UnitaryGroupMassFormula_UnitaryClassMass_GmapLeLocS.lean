-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:47:41.273008+00:00
-- url     : https://prove2.me/theorems/b367e13d-050b-4a42-ba1f-b831411267af
-- title:
--   Gmap Le Loc S
-- statement:
--   Definitions and structural lemmas for Gmap Le Loc S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/GmapLeLocS.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
section Glob
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}
end Glob
end PI.UnitaryGroupMassFormula.UJClassMass


