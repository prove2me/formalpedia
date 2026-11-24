-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:23:10.605658+00:00
-- url     : https://prove2.me/theorems/83742dd9-c52d-4b59-896e-a02c2b79847e
-- title:
--   Level A
-- statement:
--   Definitions and structural lemmas for Level A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelA.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
namespace PI.UnitaryGroupMassFormula.InHHClassFin
section Generic
variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}
end Generic
end PI.UnitaryGroupMassFormula.InHHClassFin


