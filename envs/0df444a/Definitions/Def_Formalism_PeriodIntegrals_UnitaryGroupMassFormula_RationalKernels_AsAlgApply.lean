-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_AsAlgApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_AsAlgApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:28.780846+00:00
-- url     : https://prove2.me/theorems/ef637406-ebca-43ae-91f4-ff76e29b2e5d
-- title:
--   As Alg Apply
-- statement:
--   Definitions and structural lemmas for As Alg Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/AsAlgApply.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end PI.Dv.RK


