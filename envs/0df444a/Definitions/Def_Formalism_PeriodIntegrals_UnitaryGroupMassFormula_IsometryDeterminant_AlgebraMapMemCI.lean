-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:13.682931+00:00
-- url     : https://prove2.me/theorems/4a44b061-594b-4504-9c22-a76e98a3095e
-- title:
--   Algebra Map Mem CI
-- statement:
--   Definitions and structural lemmas for Algebra Map Mem CI, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/AlgebraMapMemCI.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable (K) in

abbrev cI (J : Ideal R) : Submodule R K := ((J : FractionalIdeal (nonZeroDivisors R) K) : Submodule R K)
end PI.IsoDetW.Loc


