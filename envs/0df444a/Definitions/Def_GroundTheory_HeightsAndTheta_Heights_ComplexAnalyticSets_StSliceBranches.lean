-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBranches
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBranches
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:57.247623+00:00
-- url     : https://prove2.me/theorems/198ee409-1a0e-48ce-aeda-322d2605e424
-- title:
--   St Slice Branches
-- statement:
--   Definitions and structural lemmas for St Slice Branches, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceBranches.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
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
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
def SliceBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → p ∈ zeroSet W →
    (∃ N ∈ 𝓝 p, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
    ∀ (U : Set (Fin n → ℂ)) (Λ : (Fin n → ℂ) → Set (Matrix (Fin d) (Fin n) ℂ)),
      IsOpen U → zeroSet W ⊆ closure (zeroSet W ∩ U) → (∀ q ∈ zeroSet W ∩ U, Dense (Λ q)) →
        ∃ q ∈ zeroSet W ∩ U, ∃ L ∈ Λ q, ∃ c : Fin m → VarBranch (sliceIdeal J L q) 1 q,
          (∃ N ∈ 𝓝 q, zeroSet (sliceIdeal J L q) ∩ N ⊆ ⋃ b, (c b).image) ∧
          (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {x | linEval u x = 0}) ∧
          ∀ b, VanishesToOrder (fun t => linEval u ((c b).toFun t)) (c b).radius (ord b)
end
end GroundTheory.Heights₂.Heights


