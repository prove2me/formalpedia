-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsSmallSaturatingVector
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsSmallSaturatingVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:12.726983+00:00
-- url     : https://prove2.me/theorems/2f6d977c-c788-4f1d-8aa8-1a0cb21ee016
-- title:
--   Exists Small Saturating Vector
-- statement:
--   Definitions and structural lemmas for Exists Small Saturating Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsSmallSaturatingVector.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
noncomputable def hQdist {K : Type} [Field K] {r k : ℕ} (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (q : Fin r → K) : ℝ :=
  ⨅ z : Fin k → ℂ, Real.sqrt (∑ i, ‖σ (q i) + ∑ j, z j * σ (b j i)‖ ^ 2)
section Final
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
end Final
section Main
end Main
end ReciprocityTheory.ChartRestriction.G.T0


