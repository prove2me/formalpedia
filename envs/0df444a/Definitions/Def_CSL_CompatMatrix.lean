-- Prove2me | Definitions.Def_CSL_CompatMatrix
-- name    : CSL_CompatMatrix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:10:05.100505+00:00
-- url     : https://prove2.me/theorems/75c3c450-6eee-49d5-9b04-4995fc1f7631
-- title:
--   Coded sorting bridge: CSL CompatMatrix
-- statement:
--   Compatibility lemmas for matrices indexed by the lexicographic sum `I ⊕ₗ I`.
--
--   Current Mathlib no longer unfolds the type synonym `Lex` during rewriting, so lemmas about
--   `Matrix (I ⊕ I)` do not apply directly to `Matrix (I ⊕ₗ I)`. These lemmas hold for every
--   decidable-equality instance on `I ⊕ₗ I`.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Definitions.Def_CSL_Compat
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Sum.Order

/-! Compatibility lemmas for matrices indexed by the lexicographic sum `I ⊕ₗ I`.

Current Mathlib no longer unfolds the type synonym `Lex` during rewriting, so lemmas about
`Matrix (I ⊕ I)` do not apply directly to `Matrix (I ⊕ₗ I)`. These lemmas hold for every
decidable-equality instance on `I ⊕ₗ I`. -/

namespace CSL.CompatMatrix

variable {I : Type*} [DecidableEq I] {R : Type*} [Semiring R]

theorem fromBlocks_one_lex (inst : DecidableEq (I ⊕ₗ I)) :
    (Matrix.fromBlocks (1 : Matrix I I R) 0 0 1 : Matrix (I ⊕ I) (I ⊕ I) R) =
      (letI := inst; (1 : Matrix (I ⊕ₗ I) (I ⊕ₗ I) R)) := by
  ext a b
  refine Eq.trans ?_ (@Matrix.one_apply (I ⊕ₗ I) R inst _ _ a b).symm
  rcases a with r | r <;> rcases b with c | c
  · split_ifs with h'
    · obtain rfl : r = c := Sum.inl_injective h'
      simp
    · have hrc : r ≠ c := fun e => h' (e ▸ rfl)
      simp [Matrix.one_apply, hrc]
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    exact (if_neg Sum.inl_ne_inr).symm
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    exact (if_neg Sum.inr_ne_inl).symm
  · split_ifs with h'
    · obtain rfl : r = c := Sum.inr_injective h'
      simp
    · have hrc : r ≠ c := fun e => h' (e ▸ rfl)
      simp [Matrix.one_apply, hrc]

theorem one_mulVec_lex [Fintype I] (inst : DecidableEq (I ⊕ₗ I)) (v : I ⊕ₗ I → R) :
    (letI := inst; (1 : Matrix (I ⊕ₗ I) (I ⊕ₗ I) R)).mulVec v = v := by
  letI := inst
  exact Matrix.one_mulVec v

theorem fromBlocks_mul_lex [Fintype I] (A B C D A' B' C' D' : Matrix I I R) :
    (Matrix.fromBlocks A B C D : Matrix (I ⊕ₗ I) (I ⊕ₗ I) R) *
        (Matrix.fromBlocks A' B' C' D' : Matrix (I ⊕ₗ I) (I ⊕ₗ I) R) =
      (Matrix.fromBlocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') :
        Matrix (I ⊕ₗ I) (I ⊕ₗ I) R) :=
  Matrix.fromBlocks_multiply A B C D A' B' C' D'

end CSL.CompatMatrix


