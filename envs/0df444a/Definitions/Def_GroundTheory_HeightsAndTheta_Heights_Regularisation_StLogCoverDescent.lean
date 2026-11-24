-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:38.448728+00:00
-- url     : https://prove2.me/theorems/457da5bc-a917-4d26-bfb1-041c963ae38b
-- title:
--   St Log Cover Descent
-- statement:
--   Definitions and structural lemmas for St Log Cover Descent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/StLogCoverDescent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology
noncomputable section
def LogCoverDescent.Statement : Prop :=
  ∀ (n a : ℕ) (h : a ≤ n) (φ : (Fin n → ℂ) → ℂ), AnalyticOnNhd ℂ φ (logCover h) →
    (∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) →
    AnalyticOnNhd ℂ (fun z => φ (logLift a z)) (puncturedChart h (ball 0 1)) ∧
      ∀ w ∈ logCover h, φ (logLift a (expCover a w)) = φ w
end
end GroundTheory.Heights₂.Heights.Regular


