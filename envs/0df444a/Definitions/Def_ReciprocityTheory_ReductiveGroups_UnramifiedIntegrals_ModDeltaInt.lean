-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:45.382806+00:00
-- url     : https://prove2.me/theorems/7caa5043-b1c9-40e7-bfeb-9aae7a0069ef
-- title:
--   Mod Delta Int
-- statement:
--   Definitions and structural lemmas for Mod Delta Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModDeltaInt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
def s3Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 3 n : ℤ)
def s5Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 5 n : ℤ)
def tZ : PowerSeries ℤ := PowerSeries.mk fun n =>
  (5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ)) / 12
end ReciprocityTheory.ChartRestriction.L1


