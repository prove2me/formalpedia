-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_ResidueFiniteModel
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_ResidueFiniteModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:47.86682+00:00
-- url     : https://prove2.me/theorems/570eb2cb-a465-4f7d-bc4c-0f4c0c3f9ea8
-- title:
--   Residue Finite Model
-- statement:
--   Definitions and structural lemmas for Residue Finite Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/ResidueFiniteModel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_ResidueChartModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauIIsBasisOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix
noncomputable section
open RigSymForm
def ResidueFiniteModel.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a : ℕ), 3 ≤ a → ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ b : ℕ, b < a → Nonempty (ResidueChartModel P a b x)
end
end GroundTheory.Heights₂.Heights.KeyFormula


