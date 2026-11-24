-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:43.928198+00:00
-- url     : https://prove2.me/theorems/0e48261d-f5a7-4e26-8750-165d71dfbcef
-- title:
--   ABridge St A
-- statement:
--   Definitions and structural lemmas for ABridge St A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module
variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]
theorem continuous_conjPt : Continuous (conjPt : (J → ℂ) → J → ℂ) := by
  exact continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)
def conjEquiv (J : Type) [Fintype J] : (J → ℂ) ≃ᵐ (J → ℂ) where
  toFun := conjPt
  invFun := conjPt
  left_inv z := by funext i; simp [conjPt]
  right_inv z := by funext i; simp [conjPt]
  measurable_toFun := continuous_conjPt.measurable
  measurable_invFun := continuous_conjPt.measurable
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


