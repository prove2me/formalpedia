-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDisc
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDisc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:22.644457+00:00
-- url     : https://prove2.me/theorems/1e077c4b-d7a6-4c23-ad0f-a046fcf76828
-- title:
--   St Normal Model Disc
-- statement:
--   Definitions and structural lemmas for St Normal Model Disc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelDisc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveBranchOrder
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
def NormalModelDisc.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ r : ℝ, 0 < r ∧ ∃ φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ,
        DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧
          Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧ φ 0 = w
end
end GroundTheory.Heights₂.Heights


