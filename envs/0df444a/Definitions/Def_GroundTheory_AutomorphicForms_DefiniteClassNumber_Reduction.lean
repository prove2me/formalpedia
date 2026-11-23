-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
-- name    : GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:31.720254+00:00
-- url     : https://prove2.me/theorems/f54f5e2d-47cd-43cd-b39c-2b805ef17ef1
-- title:
--   Reduction
-- statement:
--   Definitions and structural lemmas for Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Reduction.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Module Submodule
open scoped RealInnerProductSpace
universe u
section Dual
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
def latticeDual (L : AddSubgroup X) : AddSubgroup X where
  carrier := {y | ∀ x ∈ L, ∃ n : ℤ, ⟪y, x⟫ = n}
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  add_mem' := fun {a b} ha hb x hx => by
    obtain ⟨m, hm⟩ := ha x hx
    obtain ⟨n, hn⟩ := hb x hx
    exact ⟨m + n, by rw [inner_add_left, hm, hn]; push_cast; ring⟩
  neg_mem' := fun {a} ha x hx => by
    obtain ⟨m, hm⟩ := ha x hx
    exact ⟨-m, by rw [inner_neg_left, hm]; push_cast; ring⟩
end Dual
def shortBasisBound : ℕ → ℝ → ℝ
  | 0, _ => 0
  | N + 1, μ => N * shortBasisBound N (Real.sqrt 3 / 2 * μ) + μ⁻¹
section Reduction
end Reduction
end GroundTheory.Automorphic


