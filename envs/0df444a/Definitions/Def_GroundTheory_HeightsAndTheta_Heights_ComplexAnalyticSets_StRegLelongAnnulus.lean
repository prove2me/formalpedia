-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongAnnulus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:46.298775+00:00
-- url     : https://prove2.me/theorems/2afb8346-a341-4d6b-9ddb-7fedc76f6bcc
-- title:
--   St Reg Lelong Annulus
-- statement:
--   Definitions and structural lemmas for St Reg Lelong Annulus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegLelongAnnulus.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLogDensNonneg
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
def RegLelongAnnulus.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → 0 < r → r ≤ s →
      r ^ (2 * d) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y) -
        s ^ (2 * d) * (∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y) =
      r ^ (2 * d) * s ^ (2 * d) * ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => logDistSq x) y
end
end GroundTheory.Heights₂.Heights


