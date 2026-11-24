-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:49.491963+00:00
-- url     : https://prove2.me/theorems/d70ee982-7db4-4219-a0f8-959935e75d54
-- title:
--   Eich Along Sub
-- statement:
--   Definitions and structural lemmas for Eich Along Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {σ : R →+* R}
  {J : Matrix ι ι R}
variable (σ J) in

def tor (e f : ι → R) (l m : R) : Matrix ι ι R :=
  1 + (l - 1) • vecMulVec e (J *ᵥ (σ ∘ f)) + (m - 1) • vecMulVec f (J *ᵥ (σ ∘ e))
section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
variable {e f : ι → R} (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
include he hff
variable (hef : hf σ J e f = 1)
include hef
end
end ReciprocityTheory.ChartRestriction.G.SA


