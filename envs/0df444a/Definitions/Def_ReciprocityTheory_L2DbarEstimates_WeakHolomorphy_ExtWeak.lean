-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:49.368247+00:00
-- url     : https://prove2.me/theorems/e5083ec2-781f-4c03-8e83-261158af1648
-- title:
--   Ext Weak
-- statement:
--   Definitions and structural lemmas for Ext Weak, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}
noncomputable def extErr (F : V n → ℂ) (k : ℝ) (v z : V n) : ℂ :=
  (fderiv ℝ (extCut F k) z (I • v) : ℂ) - I * (fderiv ℝ (extCut F k) z v : ℂ)
end ReciprocityTheory.L2DbarEstimates.C


