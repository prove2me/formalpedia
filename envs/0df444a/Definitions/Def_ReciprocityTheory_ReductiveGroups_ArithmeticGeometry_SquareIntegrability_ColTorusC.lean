-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:47.487526+00:00
-- url     : https://prove2.me/theorems/fb51bc0e-891b-4aac-a83e-420ab31c0327
-- title:
--   Col Torus C
-- statement:
--   Definitions and structural lemmas for Col Torus C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
def ctU (q : ℕ) (b : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun t => cexp (q * Real.pi * Hf t b - q * Real.pi * Hf b b / 2) * F (t - b)
def ctY (Y : GT ι) (w : EuclideanSpace ℂ ι) : GT ι where
  b := Y.b
  integral := Y.integral
  perfect := Y.perfect
  ka := fun t => Y.ka t * cexp (2 * Real.pi * (Hf t w).im * I)
  ka_abs := by
    intro x hx
    rw [norm_mul, Y.ka_abs x hx, one_mul, Complex.norm_exp]
    simp
instance ctCnt (Y : GT ι) : Countable (Submodule.span ℤ (Set.range Y.b)).toAddSubgroup :=
  inferInstanceAs (Countable (Submodule.span ℤ (Set.range Y.b)))
end
end ReciprocityTheory.ChartRestriction.G.I2
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
variable {K : Submodule ℝ (EuclideanSpace ℂ ι)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK
end
end ReciprocityTheory.ChartRestriction.G.I2


