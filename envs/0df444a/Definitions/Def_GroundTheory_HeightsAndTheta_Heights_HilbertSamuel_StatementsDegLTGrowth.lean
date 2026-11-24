-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:47.332804+00:00
-- url     : https://prove2.me/theorems/42943e0f-33ac-4e53-9685-79568f9d1026
-- title:
--   Statements Deg LTGrowth
-- statement:
--   Definitions and structural lemmas for Statements Deg LTGrowth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsDegLTGrowth.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.NumbersDVR
def DegLTGrowth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (g : (K → ℤ) → ℤ), DegLT g n →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(g (fun k => (a k : ℤ)) : ℝ)| ≤ C * ((∑ k, (a k : ℝ)) + 1) ^ ((n : ℝ) - 1)
end GroundTheory.Heights₂.Heights.HilbertSamuel


