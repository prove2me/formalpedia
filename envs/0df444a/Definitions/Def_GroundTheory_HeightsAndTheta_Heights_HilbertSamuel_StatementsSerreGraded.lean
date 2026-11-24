-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:17.974628+00:00
-- url     : https://prove2.me/theorems/1e19f6a1-061b-42dc-9c97-3386bbb22f09
-- title:
--   Statements Serre Graded
-- statement:
--   Definitions and structural lemmas for Statements Serre Graded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsSerreGraded.lean

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
noncomputable section
def gradedSpan {Ω : Type*} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω) (n : ℕ) :
    AddSubgroup Ω :=
  AddSubgroup.closure {x | ∃ (l : Fin r) (μ : Fin q → ℕ), d l + ∑ j, μ j = n ∧ x = t l * ∏ j, w j ^ μ j}
def SerreGraded.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (q r : ℕ) (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω),
    (∃ j, w j ≠ 0) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ s : Ω,
      (∀ j, w j ≠ 0 → ∃ D : ℕ, s * w j ^ D ∈ gradedSpan w d t (n + D)) → s ∈ gradedSpan w d t n
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


