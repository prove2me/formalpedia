-- Prove2me | Definitions.Def_MagicSquaresRealCone
-- name    : MagicSquaresRealCone
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-22T15:32:37.164544+00:00
-- url     : https://prove2.me/theorems/fb55b361-8134-4ec5-9f37-76e60f05b7cb
-- title:
--   Real semi-magic cone
-- statement:
--   For each order n, define the real linear subspace of n by n matrices whose row sums and column sums all equal one common real value. Its intersection with the nonnegative orthant is the real semi-magic cone.
-- source:
--   Original conic packaging of semi-magic matrices. The related Birkhoff-polytope face/matching-covered correspondence appears in Beniamini and Nisan, Bipartite Perfect Matching as a Real Polynomial, arXiv:2001.07642v2, Section 3.2.2, Theorem 3.11; the cone definition here is not a verbatim statement from that paper. https://arxiv.org/pdf/2001.07642v2

import Mathlib

namespace MagicSquaresRealCone

/-- Real matrices whose row and column sums share one common value. -/
def balancedSubspace (n : ℕ) : Submodule ℝ ((Fin n × Fin n) → ℝ) where
  carrier := {x | ∃ s : ℝ,
    (∀ i, ∑ j, x (i, j) = s) ∧ (∀ j, ∑ i, x (i, j) = s)}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩ <;> intro i <;> simp
  add_mem' := by
    rintro x y ⟨sx, hxr, hxc⟩ ⟨sy, hyr, hyc⟩
    refine ⟨sx + sy, ?_, ?_⟩
    · intro i
      simp only [Pi.add_apply, Finset.sum_add_distrib, hxr i, hyr i]
    · intro j
      simp only [Pi.add_apply, Finset.sum_add_distrib, hxc j, hyc j]
  smul_mem' := by
    rintro a x ⟨s, hxr, hxc⟩
    refine ⟨a * s, ?_, ?_⟩
    · intro i
      change ∑ j, a * x (i, j) = a * s
      rw [← Finset.mul_sum, hxr i]
    · intro j
      change ∑ i, a * x (i, j) = a * s
      rw [← Finset.mul_sum, hxc j]

/-- The cone of real nonnegative matrices with balanced row and column sums. -/
def cone (n : ℕ) : PointedCone ℝ ((Fin n × Fin n) → ℝ) :=
  PointedCone.ofSubmodule (balancedSubspace n) ⊓
    PointedCone.positive ℝ ((Fin n × Fin n) → ℝ)

end MagicSquaresRealCone


