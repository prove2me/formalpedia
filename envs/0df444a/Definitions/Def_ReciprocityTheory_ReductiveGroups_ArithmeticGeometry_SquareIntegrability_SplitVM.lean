-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:35.342647+00:00
-- url     : https://prove2.me/theorems/7933d7e6-2cc9-4861-b997-028bc3604b3e
-- title:
--   Split VM
-- statement:
--   Definitions and structural lemmas for Split VM, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVM.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
def ConjSymm (t : (E →+* ℂ) → ℂ) : Prop :=
  ∀ σ, t (ComplexEmbedding.conjugate σ) = (starRingEnd ℂ) (t σ)
end
end ReciprocityTheory.ChartRestriction.G.I2


