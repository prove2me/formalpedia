-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsBranchesGoodPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsBranchesGoodPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:33.938176+00:00
-- url     : https://prove2.me/theorems/c9ff01d8-72a0-4c6d-a5ec-8881f1e422a4
-- title:
--   Statements Branches Good Point
-- statement:
--   Definitions and structural lemmas for Statements Branches Good Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsBranchesGoodPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsLocalBranches
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
open MvPolynomial Filter Topology Matrix
noncomputable section
def BranchesGoodPoint.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
    p ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
    (∃ N ∈ 𝓝 p, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | GroundTheory.Heights₂.Heights.linEval u x = 0}) →
    (∀ b, GroundTheory.Heights₂.Heights.VanishesToOrder
      (fun t => GroundTheory.Heights₂.Heights.linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      ∃ (q : Fin n → ℂ) (π : Matrix (Fin d) (Fin n) ℂ) (s : Fin m → Fin (d + 1) → ℂ),
        q ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
        (∃ N ∈ 𝓝 q, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
        (∃ N ∈ 𝓝 q, ∀ b, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ N ⊆ (γ b).slice) ∧
        (∃ N ∈ 𝓝 q, ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N,
          GroundTheory.Heights₂.Heights.linEval u x = 0 → x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W) ∧
        (∀ b, s b ∈ Metric.ball 0 (γ b).radius ∧ s b 0 = 0 ∧ (γ b).toFun (s b) = q) ∧
        (∀ b, Function.Bijective
          (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (s b))) ∧
        ∀ b, ∀ P ∈ 𝓝 (s b), ∃ ε > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius,
          (γ b).toFun τ ∈ Metric.ball q ε → τ ∈ P
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


