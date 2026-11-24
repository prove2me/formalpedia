-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:32:08.001587+00:00
-- url     : https://prove2.me/theorems/3590e38f-8ef6-480a-b1b0-fe35d2342c6e
-- title:
--   Ring AFacts
-- statement:
--   Definitions and structural lemmas for Ring AFacts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/RingAFacts.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
def RingAFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    (∀ x ∈ ringA l, ‖x‖ ≤ 1) ∧
    (∀ x ∈ ringA l, ∃ f : ℕ, 0 < f ∧ ∃ y ∈ ringA l, x ^ (l ^ f) - x = (l : ℂ_[l]) * y)
def FrobA : Prop :=
  ∀ (l : ℕ) [Fact l.Prime],
    ∃ σ0 : ringA l →+* ringA l,
      (∀ ζ : ringA l, (ζ : ℂ_[l]) ∈ muPrime l → σ0 ζ = ζ ^ l) ∧
      ∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y
def FrobAIsom : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (σ0 : ringA l →+* ringA l),
    (∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y) →
    ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖
end Formalism.L2.Th1.D


