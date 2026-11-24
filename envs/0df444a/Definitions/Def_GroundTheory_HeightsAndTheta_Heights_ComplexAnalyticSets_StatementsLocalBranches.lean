-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsLocalBranches
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsLocalBranches
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:31.19088+00:00
-- url     : https://prove2.me/theorems/1af516ac-111d-4ae0-86cb-3b21c5d8df4d
-- title:
--   Statements Local Branches
-- statement:
--   Definitions and structural lemmas for Statements Local Branches, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsLocalBranches.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
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
def BranchesToGoodPosition.Statement : Prop :=
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
      ∃ (q : Fin n → ℂ) (π : Matrix (Fin d) (Fin n) ℂ) (U : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ))
        (ρ : ℝ), GoodPosition J W u q π U V ρ (∑ b, ord b)
def GoodPositionToBranches.Statement : Prop :=
  ∀ (n e : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ)
    (π : Matrix (Fin e) (Fin n) ℂ) (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (ρ : ℝ) (N : ℕ),
    IsAffVariety J (e + 1) → linForm u ∉ J → W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
    GoodPosition J W u p π U V ρ N →
      ∃ (q : Fin n → ℂ) (m : ℕ) (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J (e + 1) q)
        (ord : Fin m → ℕ),
        q ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
        (∃ N' ∈ 𝓝 q, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N' ⊆ ⋃ b, (γ b).image) ∧
        (∃ N' ∈ 𝓝 q, ∀ b, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ N' ⊆ (γ b).slice) ∧
        (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | GroundTheory.Heights₂.Heights.linEval u x = 0}) ∧
        (∀ b, GroundTheory.Heights₂.Heights.VanishesToOrder
          (fun t => GroundTheory.Heights₂.Heights.linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
        ∑ b, ord b = N
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


