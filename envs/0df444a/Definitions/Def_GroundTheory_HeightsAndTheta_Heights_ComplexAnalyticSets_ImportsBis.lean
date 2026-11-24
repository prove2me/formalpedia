-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:19.767499+00:00
-- url     : https://prove2.me/theorems/bda2e9d9-3634-463a-81a9-de99460d9c67
-- title:
--   Imports Bis
-- statement:
--   Definitions and structural lemmas for Imports Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ImportsBis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory
noncomputable section
def LogIntegrableOn.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (u : Fin n → ℂ) (B : Set (Fin n → ℂ)),
    IsAffVariety J d → IsFiniteProj J A → (∀ i, SmoothNear (zeroLocus J) (φ i)) →
    linForm u ∉ J → MeasurableSet B → Bornology.IsBounded B →
      ProjIntegrable J A (B.indicator fun x => Real.log ‖linVal u x‖) φ
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


