-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
-- name    : ReciprocityTheory_SemistableReduction_TorusMeanC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:08.54442+00:00
-- url     : https://prove2.me/theorems/bc9913d6-4de7-4bf1-b09f-7dd8187b3647
-- title:
--   Torus Mean C
-- statement:
--   Definitions and structural lemmas for Torus Mean C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanC.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def tmLog (f : MvPolynomial ι ℂ) (θ : ι → ℝ) : ℝ := Real.log ‖MvPolynomial.eval (torusPoint θ) f‖
end ReciprocityTheory.MultiplicativeHeights


