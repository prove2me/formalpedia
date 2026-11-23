-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_AugmentationDegreeZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_AugmentationDegreeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:48.094813+00:00
-- url     : https://prove2.me/theorems/be8df93c-b31c-4778-893f-a361c7edd3e7
-- title:
--   Augmentation Degree Zero
-- statement:
--   Definitions and structural lemmas for Augmentation Degree Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/AugmentationDegreeZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_YHom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EagonNorthcottZ
open MvPolynomial Finset
def wy (D : ℕ) : Fin D ⊕ Fin D → ℕ := Sum.elim 0 1
end PI.EagonNorthcottZ


