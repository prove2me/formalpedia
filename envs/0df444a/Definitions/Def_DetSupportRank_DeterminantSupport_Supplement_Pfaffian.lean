-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_Pfaffian
-- name    : DetSupportRank_DeterminantSupport_Supplement_Pfaffian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:05:50.256341+00:00
-- url     : https://prove2.me/theorems/08734075-19de-4525-b078-93c45cb1eec8
-- title:
--   Division-free signed matching-sum Pfaffian
-- statement:
--   For an even-order matrix $A$, take all partitions of the ordered indices into pairs. Orient each pair increasingly, order the pairs by first endpoint, and let $\sigma_\pi$ be the resulting concatenated permutation. Define
--   $$\operatorname{pf}(A)=\sum_\pi\operatorname{sgn}(\sigma_\pi)\prod_{(i,j)\in\pi}A_{ij}.$$
--   Canonical permutations encode these pair partitions exactly once. No factorial or power of two is inverted. The empty Pfaffian is one, and odd-order inputs are assigned zero, as their perfect-matching set is empty. The source applies this construction to alternating matrices. The same definition works over a field and its formal polynomial ring.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §4.1, equation (3) and empty-matrix convention, p. 9 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Mathlib

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Canonical ordered pair partitions, represented without multiplicity by permutations.
Pairs occupy positions (0,1),(2,3),...; their first endpoints increase. Formula (3), p.9. -/
def IsMatchingPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ (i : Fin n), i.val % 2 = 0 → ∀ h : i.val + 1 < n,
    σ i < σ ⟨i.val + 1, h⟩) ∧
  (∀ (i j : Fin n), i.val % 2 = 0 → j.val % 2 = 0 → i < j → σ i < σ j)

/-- Division-free signed matching sum (3). Empty Pfaffian is 1; odd order is 0. -/
def pfaffian {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : R := by
  classical
  exact if Even n then
    ∑ σ ∈ Finset.univ.filter IsMatchingPermutation,
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) *
        ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val % 2 = 0),
          if h : i.val + 1 < n then A (σ i) (σ ⟨i.val + 1, h⟩) else 0
  else 0
end DetSupportRank.DeterminantSupport.Supplement


