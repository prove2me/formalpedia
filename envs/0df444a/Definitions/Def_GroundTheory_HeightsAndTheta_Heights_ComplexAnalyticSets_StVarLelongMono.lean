-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarLelongMono
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarLelongMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:30.974851+00:00
-- url     : https://prove2.me/theorems/f9b66baf-3f3d-40d6-8e2d-cdedf81b906c
-- title:
--   St Var Lelong Mono
-- statement:
--   Definitions and structural lemmas for St Var Lelong Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarLelongMono.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongMono
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
def VarLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < r → r ≤ s →
      s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1) (fun _ => euclPot) y ≤
        r ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1) (fun _ => euclPot) y
end
end GroundTheory.Heights₂.Heights


