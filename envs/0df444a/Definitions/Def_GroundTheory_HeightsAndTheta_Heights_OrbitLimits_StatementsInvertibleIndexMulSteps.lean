-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:35.389823+00:00
-- url     : https://prove2.me/theorems/3b5afd4a-c3ac-46dd-9108-b6c7b293e5d8
-- title:
--   Statements Invertible Index Mul Steps
-- statement:
--   Definitions and structural lemmas for Statements Invertible Index Mul Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsInvertibleIndexMulSteps.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
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
def LocalGen {Ω : Type} [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (m : Ideal B) (f : Ω) : Prop :=
  (∃ b : B, b ∉ m ∧ (b : Ω) * f ∈ X) ∧ ∀ z ∈ X, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * f
def LocalGenFamily.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (η : Type) [Fintype η] (f : η → Ω),
    Module.Finite ℤ B → (∀ b ∈ B, ∀ z ∈ X, b * z ∈ X) → (∀ i, f i ≠ 0) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * f i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B X m (f i)) →
      X ≠ ⊥ ∧ ∃ (ι : Type) (_ : Fintype ι) (a : ι → Ω), (∀ j, a j ∈ X) ∧
        (∀ j, ∃ c ∈ B, c ≠ 0 ∧ c * a j ∈ B) ∧
        ∀ m : Ideal B, m.IsMaximal → ∃ j, ∀ z ∈ X, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * a j
def LocallyPrincipalCoprimeField.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (B : Subring Ω) (M : AddSubgroup Ω) (ι : Type) [Fintype ι]
    (a : ι → Ω),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * a i) →
    M ≠ ⊥ → ∀ s : B, s ≠ 0 →
      ∃ (β δ : B) (I : Ideal B), β ≠ 0 ∧ δ ≠ 0 ∧ I ⊔ Ideal.span {s} = ⊤ ∧
        ∀ x : Ω, x ∈ M ↔ ∃ y ∈ I, (β : Ω) * x = δ * y
def InvertibleProductRep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (M N P : AddSubgroup Ω) (η : Type) [Fintype η] (g h : η → Ω)
    (β δ β' δ' : B) (I J : Ideal B),
    β ≠ 0 → δ ≠ 0 → β' ≠ 0 → δ' ≠ 0 →
    (∀ x : Ω, x ∈ M ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) →
    (∀ x : Ω, x ∈ N ↔ ∃ y ∈ J, (β' : Ω) * x = δ' * y) →
    (∀ b ∈ B, ∀ z ∈ P, b * z ∈ P) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i,
      LocalGen B M m (g i) ∧ LocalGen B N m (h i) ∧ LocalGen B P m (g i * h i)) →
      ∀ x : Ω, x ∈ P ↔ ∃ y ∈ I * J, ((β * β' : B) : Ω) * x = (δ * δ' : B) * y
def InvertibleIndexCharP.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (η : Type) [Fintype η] (f : η → Ω),
    ringChar Ω ≠ 0 → Module.Finite ℤ B → (∀ b ∈ B, ∀ z ∈ X, b * z ∈ X) → (∀ i, f i ≠ 0) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B X m (f i)) →
      genIndex X B.toAddSubgroup = 1
end GroundTheory.Heights₂.Heights.Targets


