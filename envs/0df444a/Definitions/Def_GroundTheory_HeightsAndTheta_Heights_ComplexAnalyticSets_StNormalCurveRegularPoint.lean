-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveRegularPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveRegularPoint
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:16:10.735748+00:00
-- url     : https://prove2.me/theorems/caabb23b-984f-435f-b9f7-ccbf14f89c43
-- title:
--   St Normal Curve Regular Point
-- statement:
--   Definitions and structural lemmas for St Normal Curve Regular Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalCurveRegularPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveBranchOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelOpenMapping
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
open MvPolynomial
noncomputable section
def NormalCurveRegularPoint.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
      w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
        ∃ (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)) (O : Set (Fin 1 → ℂ)) (V : Set (σ → ℂ)) (g : (Fin 1 → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ w ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
            IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I ∩ V = g '' O
end
end GroundTheory.Heights₂.Heights


