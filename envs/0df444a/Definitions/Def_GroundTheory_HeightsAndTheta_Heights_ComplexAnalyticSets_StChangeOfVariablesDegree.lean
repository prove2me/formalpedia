-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChangeOfVariablesDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChangeOfVariablesDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:15.255095+00:00
-- url     : https://prove2.me/theorems/f334a3ff-ccb3-4004-b0e7-31ec4d6c4bc3
-- title:
--   St Change Of Variables Degree
-- statement:
--   Definitions and structural lemmas for St Change Of Variables Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StChangeOfVariablesDegree.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
def ChangeOfVariablesDegree.Statement : Prop :=
  ∀ (n : ℕ) (φ : (Fin n → ℝ) → Fin n → ℝ), ContDiff ℝ ∞ φ →
    HasCompactSupport (fun x => φ x - x) →
      ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ x, f (φ x) * (fderiv ℝ φ x).det = ∫ x, f x
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


