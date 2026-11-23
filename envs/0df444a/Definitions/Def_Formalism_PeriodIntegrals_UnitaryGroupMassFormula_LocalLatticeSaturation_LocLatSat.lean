-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_LocLatSat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_LocLatSat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:38.13096+00:00
-- url     : https://prove2.me/theorems/1d24d5d6-ac44-4d6e-a4a0-205907613593
-- title:
--   Loc Lat Sat
-- statement:
--   Definitions and structural lemmas for Loc Lat Sat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeSaturation/LocLatSat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace PI.LocLatSat.UnitaryGroupMassFormula
variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}
end PI.LocLatSat.UnitaryGroupMassFormula


