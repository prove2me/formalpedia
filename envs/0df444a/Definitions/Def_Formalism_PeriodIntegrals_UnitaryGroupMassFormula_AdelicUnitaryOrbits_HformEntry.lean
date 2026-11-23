-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:34.648603+00:00
-- url     : https://prove2.me/theorems/2fc76fa0-92e1-4e25-8c21-17f115bba2bd
-- title:
--   Hform Entry
-- statement:
--   Definitions and structural lemmas for Hform Entry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/HformEntry.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelicOrbitU
open Matrix Formalism.UG
section Refl
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
end Refl
end PIW.AdelicOrbitU


