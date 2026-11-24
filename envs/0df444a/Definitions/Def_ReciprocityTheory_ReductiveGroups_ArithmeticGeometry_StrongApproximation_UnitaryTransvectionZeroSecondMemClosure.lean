-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:34.040623+00:00
-- url     : https://prove2.me/theorems/3d7d3175-22a2-441a-8da8-3b531af44d4f
-- title:
--   Unitary Transvection Zero Second Mem Closure
-- statement:
--   Definitions and structural lemmas for Unitary Transvection Zero Second Mem Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (σ J) in

def hm (e f : ι → K) (M : Matrix (Fin 2) (Fin 2) K) : Matrix ι ι K :=
  1 + (M 0 0 - 1) • vecMulVec e (J *ᵥ (σ ∘ f)) + M 0 1 • vecMulVec e (J *ᵥ (σ ∘ e))
    + M 1 0 • vecMulVec f (J *ᵥ (σ ∘ f)) + (M 1 1 - 1) • vecMulVec f (J *ᵥ (σ ∘ e))
section
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
end
section
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
end
end ReciprocityTheory.ChartRestriction.G.SA


