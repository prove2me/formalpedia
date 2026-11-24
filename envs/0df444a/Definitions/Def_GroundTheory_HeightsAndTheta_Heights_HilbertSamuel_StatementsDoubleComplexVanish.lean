-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDoubleComplexVanish
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDoubleComplexVanish
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:33.223606+00:00
-- url     : https://prove2.me/theorems/11660d40-3cb0-4ec4-a63c-c1a9aae4e643
-- title:
--   Statements Double Complex Vanish
-- statement:
--   Definitions and structural lemmas for Statements Double Complex Vanish, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsDoubleComplexVanish.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
def DoubleComplexVanish.Statement : Prop :=
  ∀ (C : ℕ → ℕ → Type) [∀ p n, AddCommGroup (C p n)] (P : ∀ p n, AddSubgroup (C p n))
    (δ : ∀ p n, C p n →+ C p (n + 1)) (κ : ∀ p n, C (p + 1) n →+ C p n) (R : ℕ),
    (∀ p n, ∀ x ∈ P p n, δ p n x ∈ P p (n + 1)) →
    (∀ p n, ∀ x ∈ P (p + 1) n, κ p n x ∈ P p n) →
    (∀ p n, ∀ x ∈ P p n, δ p (n + 1) (δ p n x) = 0) →
    (∀ p n, ∀ x ∈ P (p + 1) n, δ p n (κ p n x) = κ p (n + 1) (δ (p + 1) n x)) →
    (∀ p n, ∀ x ∈ P (p + 2) n, κ p n (κ (p + 1) n x) = 0) →
    (∀ n, ∀ x ∈ P 0 n, ∃ y ∈ P 1 n, κ 0 n y = x) →
    (∀ p n, ∀ x ∈ P (p + 1) n, κ p n x = 0 → ∃ y ∈ P (p + 2) n, κ (p + 1) n y = x) →
    (∀ p n, R < p → ∀ x ∈ P p n, x = 0) →
    (∀ p, 1 ≤ p → p ≤ R → ∀ n, ∀ x ∈ P p (n + 1), δ p (n + 1) x = 0 → ∃ y ∈ P p n, δ p n y = x) →
    ∀ n, ∀ x ∈ P 0 (n + 1), δ 0 (n + 1) x = 0 → ∃ y ∈ P 0 n, δ 0 n y = x
def DoubleComplexVanish.exP (p n : ℕ) : AddSubgroup ℤ := if p ≤ 1 ∧ n = 0 then ⊤ else ⊥
def DoubleComplexVanish.exκ (p : ℕ) : ℤ →+ ℤ := if p = 0 then AddMonoidHom.id ℤ else 0
end GroundTheory.Heights₂.Heights.HilbertSamuel


