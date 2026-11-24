-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:21.813187+00:00
-- url     : https://prove2.me/theorems/89dc0e98-e61e-4285-8a14-5d28b5f0a805
-- title:
--   Statements Invertible Index Mul
-- statement:
--   Definitions and structural lemmas for Statements Invertible Index Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsInvertibleIndexMul.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights
def InvertibleIndexMul.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (M N P : AddSubgroup Ω) (η : Type) [Fintype η] (g h : η → Ω),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) → (∀ b ∈ B, ∀ z ∈ N, b * z ∈ N) → (∀ b ∈ B, ∀ z ∈ P, b * z ∈ P) →
    (∀ i, g i ≠ 0) → (∀ i, h i ≠ 0) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * g i ∈ B) → (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * h i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i,
      ((∃ b : B, b ∉ m ∧ (b : Ω) * g i ∈ M) ∧ ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * g i) ∧
      ((∃ b : B, b ∉ m ∧ (b : Ω) * h i ∈ N) ∧ ∀ z ∈ N, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * h i) ∧
      ((∃ b : B, b ∉ m ∧ (b : Ω) * (g i * h i) ∈ P) ∧
        ∀ z ∈ P, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * (g i * h i))) →
      0 < genIndex M B.toAddSubgroup ∧ 0 < genIndex N B.toAddSubgroup ∧
        genIndex P B.toAddSubgroup = genIndex M B.toAddSubgroup * genIndex N B.toAddSubgroup
end GroundTheory.Heights₂.Heights.Targets


