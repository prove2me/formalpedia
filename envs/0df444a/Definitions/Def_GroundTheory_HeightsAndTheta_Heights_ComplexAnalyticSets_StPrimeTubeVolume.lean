-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:02.289798+00:00
-- url     : https://prove2.me/theorems/cec0eb93-9b58-4b2f-bac8-ffd798232115
-- title:
--   St Prime Tube Volume
-- statement:
--   Definitions and structural lemmas for St Prime Tube Volume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimeTubeVolume.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
def PrimeTubeVolume.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (k : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (zeroSet J ∩ K)) ≤
          ENNReal.ofReal (C * r ^ ((2 * n : ℤ) - 2 * k))
end
end GroundTheory.Heights₂.Heights


