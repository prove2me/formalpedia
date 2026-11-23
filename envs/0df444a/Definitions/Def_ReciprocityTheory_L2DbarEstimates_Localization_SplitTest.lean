-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
-- name    : ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:30.181313+00:00
-- url     : https://prove2.me/theorems/33cc6285-3d21-4b1a-b71a-d7e65e102077
-- title:
--   Split Test
-- statement:
--   Definitions and structural lemmas for Split Test, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
section SplitHelpers
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
end SplitHelpers
def splitTestSub {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) :
    Submodule ℂ (M → ℂ) where
  carrier := {g | IsTest n z g}
  add_mem' := fun {a b} ha hb => ⟨Smooth.add n z a b ha.1 hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨Smooth.const n z 0, HasCompactSupport.zero⟩
  smul_mem' := fun c g hg => ⟨Smooth.mul n z (fun _ => c) g (Smooth.const n z c) hg.1,
    hg.2.mul_left (f := fun _ => c)⟩
end
end ReciprocityTheory.L2DbarEstimates.F


