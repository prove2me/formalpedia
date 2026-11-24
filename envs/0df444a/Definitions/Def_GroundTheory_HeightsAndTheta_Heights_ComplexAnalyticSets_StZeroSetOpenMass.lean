-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:47.054672+00:00
-- url     : https://prove2.me/theorems/57f7d5a5-58e7-43bb-818f-5057051fdee8
-- title:
--   St Zero Set Open Mass
-- statement:
--   Definitions and structural lemmas for St Zero Set Open Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StZeroSetOpenMass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsBranchesGoodPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory
noncomputable section
def ZeroSetOpenMass.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
    ∀ (x : Fin n → ℂ) (O : Set (Fin n → ℂ)), IsOpen O → x ∈ O →
      x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
        0 < μH[((2 * d : ℕ) : ℝ)] (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ O)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


