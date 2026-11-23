-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:49.015806+00:00
-- url     : https://prove2.me/theorems/e97163fe-41c9-4836-abcd-9fa51cf3fd15
-- title:
--   Iterated FDeriv Tail Zero
-- statement:
--   Definitions and structural lemmas for Iterated FDeriv Tail Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/IteratedFDerivTailZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
def expN (N : ℕ) (z : ℂ) : ℂ := ∑ n ∈ Finset.range (N + 1), z ^ n / (n.factorial : ℂ)
def gN (N : ℕ) (z : ℂ) : ℂ := cexp z - expN N z
def ellL (q : ℕ) (a : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι →L[ℂ] ℂ :=
  ((q : ℂ) * (Real.pi : ℂ)) • innerSL ℂ a
end
end ReciprocityTheory.ChartRestriction.G.I2.FPw


