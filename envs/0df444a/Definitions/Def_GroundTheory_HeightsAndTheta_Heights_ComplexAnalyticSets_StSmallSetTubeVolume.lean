-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:19.2088+00:00
-- url     : https://prove2.me/theorems/4a8c2b1f-ea0f-4220-8d61-aaf7d2e3f109
-- title:
--   St Small Set Tube Volume
-- statement:
--   Definitions and structural lemmas for St Small Set Tube Volume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSmallSetTubeVolume.lean

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
def SmallSetTubeVolume.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (zeroSet I ∩ K)) ≤
          ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d))
end
end GroundTheory.Heights₂.Heights


