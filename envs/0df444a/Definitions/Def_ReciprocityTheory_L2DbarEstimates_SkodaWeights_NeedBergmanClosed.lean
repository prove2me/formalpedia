-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NeedBergmanClosed
-- name    : ReciprocityTheory_L2DbarEstimates_SkodaWeights_NeedBergmanClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:26.931104+00:00
-- url     : https://prove2.me/theorems/5702adf5-d388-4708-a763-3e1c9d980eba
-- title:
--   Need Bergman Closed
-- statement:
--   Definitions and structural lemmas for Need Bergman Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/NeedBergmanClosed.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
def NeedBergmanClosed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ ψ : M → ℝ, Continuous ψ →
    IsClosed (holSub n z ψ : Set (WeightedL2 n z ψ))
end ReciprocityTheory.L2DbarEstimates.H


