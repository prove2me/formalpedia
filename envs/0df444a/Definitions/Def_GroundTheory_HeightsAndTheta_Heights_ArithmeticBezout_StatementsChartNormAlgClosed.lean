-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormAlgClosed
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormAlgClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:11.85675+00:00
-- url     : https://prove2.me/theorems/85575f65-4059-4a3a-a038-9f91bc7df128
-- title:
--   Statements Chart Norm Alg Closed
-- statement:
--   Definitions and structural lemmas for Statements Chart Norm Alg Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartNormAlgClosed.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SectionLineAnyField
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
def ChartNormAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → (p = ⊥ ∨ ∃ q, Prime q ∧ p = Ideal.span {q}) →
      specFirst f t ∉ p → ∀ u : Fin n → F,
        algebraMap _ (Localization.AtPrime p) (specFirst f u) =
          algebraMap _ (Localization.AtPrime p) (specFirst f t) *
            LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))
end
end GroundTheory.Heights₂.Heights


