-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:56.748785+00:00
-- url     : https://prove2.me/theorems/a625d8fb-db55-458d-8cd4-919038fc526f
-- title:
--   St Divisor One Component
-- statement:
--   Definitions and structural lemmas for St Divisor One Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDivisorOneComponent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGeneralPointBranches
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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
def DivisorOneComponent.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W ∧
            (∀ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W' → W' = W) ∧
            ∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W
end
end GroundTheory.Heights₂.Heights


