-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveJacobian
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveJacobian
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:36.024703+00:00
-- url     : https://prove2.me/theorems/6a357435-c978-49a9-93f8-f64adca6c34a
-- title:
--   St Normal Curve Jacobian
-- statement:
--   Definitions and structural lemmas for St Normal Curve Jacobian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalCurveJacobian.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveRegularPoint
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
def NormalCurveJacobian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
      w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
        ∃ (k : ℕ) (f : Fin k → MvPolynomial σ ℂ) (D : MvPolynomial σ ℂ),
          k + 1 = Fintype.card σ ∧ (∀ j, f j ∈ I) ∧
            LinearIndependent ℂ (fun j (i : σ) => eval w (pderiv i (f j))) ∧
            eval w D ≠ 0 ∧ ∀ p ∈ I, D * p ∈ Ideal.span (Set.range f)
end
end GroundTheory.Heights₂.Heights


