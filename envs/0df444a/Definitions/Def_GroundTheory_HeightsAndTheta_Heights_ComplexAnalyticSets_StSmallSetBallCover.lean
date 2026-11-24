-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetBallCover
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetBallCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:09.470644+00:00
-- url     : https://prove2.me/theorems/88bd21bc-60fe-4a7f-8481-0679006b202f
-- title:
--   St Small Set Ball Cover
-- statement:
--   Definitions and structural lemmas for St Small Set Ball Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSmallSetBallCover.lean

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
def SmallSetBallCover.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ T : Finset (Fin n → ℂ),
        (↑T : Set (Fin n → ℂ)) ⊆ zeroSet I ∩ K ∧ zeroSet I ∩ K ⊆ ⋃ c ∈ T, Metric.ball c r ∧
          (T.card : ℝ) * r ^ (2 * d) ≤ C * r ^ 2
end
end GroundTheory.Heights₂.Heights


