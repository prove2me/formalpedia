-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSize
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSize
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:13.758778+00:00
-- url     : https://prove2.me/theorems/fea0f0ba-e732-469d-8a5d-85c78421ccfc
-- title:
--   Nonempty Jacquet Rallis Haar Measures Forall Size
-- statement:
--   Definitions and structural lemmas for Nonempty Jacquet Rallis Haar Measures Forall Size, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyJacquetRallisHaarMeasuresForallSize.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.HaarExist
variable (r : ℕ)
def positiveCompactsOf {X : Type} [TopologicalSpace X] (s : Set X) (h : IsCompact s ∧ IsOpen s ∧ s.Nonempty) :
    TopologicalSpace.PositiveCompacts X :=
  ⟨⟨s, h.1⟩, by simpa [h.2.1.interior_eq] using h.2.2⟩
end GlobalTheory.JR.HaarExist


