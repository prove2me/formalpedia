-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:12.286896+00:00
-- url     : https://prove2.me/theorems/c1a3a7b2-d958-4a8b-ad36-db2251bcb1c6
-- title:
--   Eventually Differentiable At Of Cont Diff At
-- statement:
--   Definitions and structural lemmas for Eventually Differentiable At Of Cont Diff At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
namespace ReciprocityTheory.L2DbarEstimates
def LeviNonnegOn (n : ℕ) (φ : V n → ℝ) (U : Set (V n)) : Prop :=
  ∀ x ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun y => (φ y : ℂ)) x ξ).re
variable {n : ℕ}
end ReciprocityTheory.L2DbarEstimates


