-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:14.739798+00:00
-- url     : https://prove2.me/theorems/93522215-5667-48cc-b84f-3e7ce4860e80
-- title:
--   Conj Mem Eich Set
-- statement:
--   Definitions and structural lemmas for Conj Mem Eich Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ConjMemEichSet.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
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
section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
variable {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include he hff hef
end
variable (σ J) in

def Good (e f : ι → K) : Set (Matrix ι ι K) :=
  {g | ∃ n ∈ Submonoid.closure (eichSet σ J e f), ∃ l m : K, m * σ l = 1 ∧ g = n * tor σ J e f l m}
section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
end
end ReciprocityTheory.ChartRestriction.G.SA


