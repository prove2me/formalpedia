-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGeneralPointBranches
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGeneralPointBranches
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:27.156068+00:00
-- url     : https://prove2.me/theorems/1c0143ae-943b-4d4f-a0f7-d12a932f65e6
-- title:
--   St Divisor General Point Branches
-- statement:
--   Definitions and structural lemmas for St Divisor General Point Branches, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDivisorGeneralPointBranches.lean

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
open MvPolynomial Filter Topology Matrix ComplexSets
noncomputable section
def DivisorGeneralPointBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W ∧
            (∀ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W' → W' = W) ∧
            (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W) ∧
            ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
              (π : Matrix (Fin d) (Fin n) ℂ),
              (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
              (∃ N ∈ 𝓝 q, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) ∧
              (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
              (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
              ∀ b, Function.Bijective
                (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))
end
end GroundTheory.Heights₂.Heights


