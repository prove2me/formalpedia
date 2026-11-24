-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchInOneBranch
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchInOneBranch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:11.56065+00:00
-- url     : https://prove2.me/theorems/07a14312-f825-46d8-a183-87146d33359b
-- title:
--   St Punctured Branch In One Branch
-- statement:
--   Definitions and structural lemmas for St Punctured Branch In One Branch, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPuncturedBranchInOneBranch.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
def PuncturedBranchInOneBranch.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q)
    (ν : VarBranch I 1 q) (ρ : ℝ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 → 0 < ρ →
    (∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → ν.toFun (fun _ ↦ τ) ∈ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ∃ b, ∃ ρ' > 0, ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ' → ν.toFun (fun _ ↦ τ) ∈ (c b).image
end
end GroundTheory.Heights₂.Heights


