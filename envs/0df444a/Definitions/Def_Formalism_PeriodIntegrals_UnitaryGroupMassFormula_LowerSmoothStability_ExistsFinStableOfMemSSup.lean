-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:20:58.658808+00:00
-- url     : https://prove2.me/theorems/43200dab-ca1a-4c39-97ed-c47b2538fd28
-- title:
--   Exists Fin Stable Of Mem SSup
-- statement:
--   Definitions and structural lemmas for Exists Fin Stable Of Mem SSup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerSmoothStability/ExistsFinStableOfMemSSup.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.UnitaryGroupMassFormula.LowSmooth
open PI.UpqRep
section Directed
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type*}
def FinStable (G : Set ι) (ρ : ι → H →L[ℂ] H) : Set (Submodule ℂ H) :=
  {S | FiniteDimensional ℂ S ∧ ∀ g ∈ G, ∀ x ∈ S, ρ g x ∈ S}
end Directed
section Transport
variable {k r : ℕ}
end Transport
end PI.UnitaryGroupMassFormula.LowSmooth


