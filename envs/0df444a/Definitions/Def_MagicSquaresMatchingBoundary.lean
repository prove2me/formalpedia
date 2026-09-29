-- Prove2me | Definitions.Def_MagicSquaresMatchingBoundary
-- name    : MagicSquaresMatchingBoundary
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-22T13:58:55.275741+00:00
-- url     : https://prove2.me/theorems/027fccf6-cca0-433e-8801-55c88c84db26
-- title:
--   Finite matching-board boundary coefficients
-- statement:
--   Let $n\ge 1$ and let a board be a subset of $[n]\times[n]$. For a permutation $\sigma$, write $\phi_\sigma=\{(i,\sigma(i)):i\in[n]\}$. A board is matching-covered if it is nonempty and each of its cells belongs to some permutation support contained in the board. Define
--   $$a(C)=\sum_{S\subseteq C}(-1)^{|S|}\mathbf 1\{C\setminus S\text{ contains a permutation support}\}.$$
--
--   These finite definitions specify the boundary identity used in a reduction of semi-magic reciprocity.
-- source:
--   Original matching-board specialization of the Eulerian face-lattice property and the order-dual of Weisner's theorem; derived in MATCHING-BOUNDARY-SOURCE.md. Richard P. Stanley, Enumerative Combinatorics, Volume 1, author manuscript, Proposition 3.8.9, p. 309, and Corollary 3.9.3, p. 313: https://math.mit.edu/~rstan/ec/ec1.pdf. This matching-board statement is our specialization, not a verbatim theorem in that source.

import Mathlib

/-! A finite matching criterion for the boundary reciprocity reduction. -/

namespace MagicSquaresBoundary

open Finset

noncomputable def permSupport {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n × Fin n) :=
  Finset.univ.image fun i => (i, σ i)

def HasPerm (n : ℕ) (B : Finset (Fin n × Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), permSupport σ ⊆ B

def MatchingCoveredBoard (n : ℕ) (B : Finset (Fin n × Fin n)) : Prop :=
  B.Nonempty ∧ ∀ e ∈ B, ∃ σ : Equiv.Perm (Fin n),
    e ∈ permSupport σ ∧ permSupport σ ⊆ B

noncomputable def matchingEulerCoefficient (n : ℕ)
    (B : Finset (Fin n × Fin n)) : ℚ := by
  classical
  exact ∑ S ∈ B.powerset, (-1 : ℚ) ^ S.card *
    (if HasPerm n (B \ S) then 1 else 0)

noncomputable def fiberCandidates {n : ℕ}
    (B φ : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) := by
  classical
  exact B.powerset.filter fun C => B \ φ ⊆ C

def MatchingBoundaryCriterion (n : ℕ) : Prop :=
  ∀ B : Finset (Fin n × Fin n), MatchingCoveredBoard n B →
    ∀ σ : Equiv.Perm (Fin n), permSupport σ ⊆ B →
      ∀ D : Finset (Fin n × Fin n), MatchingCoveredBoard n D → D ⊆ B →
        (∑ C ∈ (fiberCandidates B (permSupport σ)).filter
          (fun C => D ⊆ C), matchingEulerCoefficient n C) =
          if permSupport σ ⊆ D then matchingEulerCoefficient n B else 0

end MagicSquaresBoundary


