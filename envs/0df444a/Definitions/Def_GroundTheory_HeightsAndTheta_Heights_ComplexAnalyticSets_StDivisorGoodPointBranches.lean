-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPointBranches
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPointBranches
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:36:24.104325+00:00
-- url     : https://prove2.me/theorems/6f44f531-c788-4e00-946f-726bc1debfaa
-- title:
--   St Divisor Good Point Branches
-- statement:
--   Definitions and structural lemmas for St Divisor Good Point Branches, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDivisorGoodPointBranches.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
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
def DivisorGoodPointBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (q : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    q ∈ zeroSet J → linEval u q = 0 → DivisorRegularAt J u d q → NormalDivisorChartAt M u d q →
    NormalDoublePointsOnDivisor M u q →
      ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
          (π : Matrix (Fin d) (Fin n) ℂ),
          (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
          (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → ∀ b, x ∈ (γ b).slice) ∧
          (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
          (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
          ∀ b, Function.Bijective
            (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))
end
end GroundTheory.Heights₂.Heights


