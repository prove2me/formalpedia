-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:10.055151+00:00
-- url     : https://prove2.me/theorems/c532f621-dcca-4138-866b-dde9c7243a24
-- title:
--   Slice Cut
-- statement:
--   Definitions and structural lemmas for Slice Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
noncomputable section
def sliceCut {n : ℕ} (h : HermNorm n) (k : ℕ) (x : Fin n → ℂ) : ℝ :=
  Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))
namespace SliceCut
variable {n : ℕ} (h : HermNorm n)
end SliceCut
end
end GroundTheory.Heights₂.Heights


