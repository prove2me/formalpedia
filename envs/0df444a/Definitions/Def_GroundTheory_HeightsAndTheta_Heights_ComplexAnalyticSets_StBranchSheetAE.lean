-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:51.245465+00:00
-- url     : https://prove2.me/theorems/d69bfa48-4003-4faf-8c6e-bceadc04bc8e
-- title:
--   St Branch Sheet AE
-- statement:
--   Definitions and structural lemmas for St Branch Sheet AE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchSheetAE.lean

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
def BranchSheetAE.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (p : Fin n → ℂ)
    (γ : VarBranch J d p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ᵐ t ∂(volume.restrict (Metric.ball (0 : Fin d → ℂ) γ.radius)), ∃ s, IsSheetAt J A (γ.toFun t) s
end
end GroundTheory.Heights₂.Heights


