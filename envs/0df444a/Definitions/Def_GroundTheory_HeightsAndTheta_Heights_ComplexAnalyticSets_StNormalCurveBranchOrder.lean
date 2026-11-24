-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveBranchOrder
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveBranchOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:15.074114+00:00
-- url     : https://prove2.me/theorems/5bb286f5-b4ab-44df-85f6-3a6ee689129f
-- title:
--   St Normal Curve Branch Order
-- statement:
--   Definitions and structural lemmas for St Normal Curve Branch Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalCurveBranchOrder.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchLift
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
def NormalCurveBranchOrder.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ) (r : ℝ) (φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → 0 < r →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) → φ 0 = w →
      ∀ g : MvPolynomial (Fin n ⊕ Fin M.m) ℂ,
        Ring.ord (pointLocalRing M.ideal w)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) g) =
          analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0
def NormalCurveBranchOrder.diagonalDisc : (Fin 1 → ℂ) → Fin 1 ⊕ Fin IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel.m → ℂ :=
  fun t _ ↦ t 0
end
end GroundTheory.Heights₂.Heights


