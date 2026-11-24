-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchSameOrder
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchSameOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:09.097543+00:00
-- url     : https://prove2.me/theorems/46d24cb8-bf92-4cff-a9d4-b3e28f40eff1
-- title:
--   St Punctured Branch Same Order
-- statement:
--   Definitions and structural lemmas for St Punctured Branch Same Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPuncturedBranchSameOrder.lean

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
def PuncturedBranchSameOrder.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c d : VarBranch I 1 q) (ρ : ℝ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 → 0 < ρ →
    (∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → d.toFun (fun _ ↦ τ) ∈ c.image) →
      ∀ f : MvPolynomial (Fin n) ℂ, branchOrder c f = branchOrder d f
end
end GroundTheory.Heights₂.Heights


