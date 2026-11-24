-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:47.244318+00:00
-- url     : https://prove2.me/theorems/c85d36e1-a830-4bbb-ad2f-3dc0f77d31df
-- title:
--   St Tube Form Compare
-- statement:
--   Definitions and structural lemmas for St Tube Form Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTubeFormCompare.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
def TubeFormCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
      ∃ C : ℝ, ∀ y, tubeDens J A P R φ y ≤ C * tubeDens J A P R (fun _ => euclPot) y
end
end GroundTheory.Heights₂.Heights


