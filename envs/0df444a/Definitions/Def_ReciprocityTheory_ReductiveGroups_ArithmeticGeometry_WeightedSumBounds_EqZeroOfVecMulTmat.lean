-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:22.732629+00:00
-- url     : https://prove2.me/theorems/b40f2a0d-cd8a-4873-94c7-58d8c0fe828d
-- title:
--   Eq Zero Of Vec Mul Tmat
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Vec Mul Tmat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/EqZeroOfVecMulTmat.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
def tmat (γ : Fin d → Fin d → PowerSeries C) : Matrix (Fin d) (Fin d) C :=
  Matrix.of fun a b => tangent (γ a) b
end
end ReciprocityTheory.ChartRestriction.G.Sh.PTb


