-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:53.207879+00:00
-- url     : https://prove2.me/theorems/675f7b0e-0817-41e4-91de-990e6dc838fc
-- title:
--   Statements Fs Pot Laplacian
-- statement:
--   Definitions and structural lemmas for Statements Fs Pot Laplacian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/StatementsFsPotLaplacian.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianLogGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian Real
def FsPotLaplacian.Statement : Prop :=
  (∀ y : ℂ, Δ fsPotPlane y = 2 / (1 + ‖y‖ ^ 2) ^ 2) ∧
    MeasureTheory.Integrable (Δ fsPotPlane) ∧ ∫ y, Δ fsPotPlane y = 2 * π
end GroundTheory.Heights₂.Heights.LowerBoundFree


