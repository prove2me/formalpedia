-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:02.232629+00:00
-- url     : https://prove2.me/theorems/29143969-0481-48e5-b9e0-438ce0c427cb
-- title:
--   Statements Locally Principal Coprime
-- statement:
--   Definitions and structural lemmas for Statements Locally Principal Coprime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsLocallyPrincipalCoprime.lean

import Mathlib
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
namespace GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
def LocallyPrincipalCoprime.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L) (M : AddSubgroup L) (ι : Type) [Fintype ι]
    (a : ι → L),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) →
    M ≠ ⊥ → ∀ s : B, s ≠ 0 →
      ∃ (β δ : B) (I : Ideal B), β ≠ 0 ∧ δ ≠ 0 ∧ I ⊔ Ideal.span {s} = ⊤ ∧
        ∀ x : L, x ∈ M ↔ ∃ y ∈ I, (β : L) * x = δ * y
end
end GroundTheory.Heights₂.Heights


