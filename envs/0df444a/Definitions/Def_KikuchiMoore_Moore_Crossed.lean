-- Prove2me | Definitions.Def_KikuchiMoore_Moore_Crossed
-- name    : KikuchiMoore_Moore_Crossed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:43:53.287648+00:00
-- url     : https://prove2.me/theorems/f5ec7f1a-eda9-4adb-a9c6-b5d24be6698f
-- title:
--   Canonical crossed halves and binary syndromes
-- statement:
--   Split each residual into its $a=\lfloor q/2\rfloor$ smallest vertices and its remaining $b=\lceil q/2\rceil$ vertices. For $q\ge2$ the coordinate space is the disjoint union of negatively tagged $a$-subsets and positively tagged $b$-subsets. A row is one coordinate of each sign, with no disjointness requirement on their underlying subsets. Every distinct pair of bundle members contributes the single unit-weight crossed edge between the two mixed rows, retaining its unordered label pair. For $q=1$ the construction instead uses singleton rows and residuals themselves. The realized mean is twice the number of instances divided by the number of rows, with the singleton case separate. The binary syndrome of a subfamily is its incidence sum in $\mathbb F_2^n$. These are proof-support constructions from Section 5, without additional assumptions on the main goal.
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Definitions and constructions, Sections 3–5, printed p. 21 = PDF p. 21, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Paired

noncomputable section
open scoped BigOperators

namespace KikuchiMoore.Moore

def minusHalf {n : ℕ} (q : ℕ) (R : Finset (Fin n)) : Finset (Fin n) :=
  ((R.sort (· ≤ ·)).take (q / 2)).toFinset

def plusHalf {n : ℕ} (q : ℕ) (R : Finset (Fin n)) : Finset (Fin n) :=
  R \ minusHalf q R

/-- Both signed half coordinates are present even when their underlying subsets overlap. -/
abbrev CrossCoordinate (n q : ℕ) := Row n (q / 2) ⊕ Row n ((q + 1) / 2)

/-- A pair of half-subsets represents one row with two signed coordinates. -/
abbrev CrossRow (n q : ℕ) := Row n (q / 2) × Row n ((q + 1) / 2)

def crossMoving {n q : ℕ} (R : Finset (Fin n)) : Finset (CrossCoordinate n q) := by
  classical
  exact Finset.univ.filter fun c => match c with
    | Sum.inl D => D.val = minusHalf q R
    | Sum.inr E => E.val = plusHalf q R

def crossInstances {n : ℕ} (k q : ℕ) (P : Finset (Bundle n)) :
    Finset (Finset (CrossRow n q) × Finset (Finset (Fin n))) := by
  classical
  exact Finset.univ.filter fun e => ∃ B ∈ P, B.center.card = k-q ∧
    ∃ F ∈ B.members, ∃ J ∈ B.members, F ≠ J ∧
    ∃ S T : CrossRow n q, S ≠ T ∧ e = ({S,T}, {F,J}) ∧
      S.1.val = minusHalf q (residual B F) ∧ S.2.val = plusHalf q (residual B J) ∧
      T.1.val = minusHalf q (residual B J) ∧ T.2.val = plusHalf q (residual B F)

def singletonCrossInstances {n : ℕ} (k : ℕ) (P : Finset (Bundle n)) :
    Finset (PairInstance n 1) := by
  classical
  exact Finset.univ.filter fun e => ∃ B ∈ P, B.center.card = k-1 ∧
    ∃ F ∈ B.members, ∃ J ∈ B.members, F ≠ J ∧
    ∃ S T : Row n 1, S ≠ T ∧ e = ({S,T}, {F,J}) ∧
      S.val = residual B F ∧ T.val = residual B J

def crossMean {n : ℕ} (k q : ℕ) (P : Finset (Bundle n)) : ℝ :=
  if q = 1 then 2 * ((singletonCrossInstances k P).card : ℝ) / n
  else 2 * ((crossInstances k q P).card : ℝ) /
    ((Nat.choose n (q/2) : ℝ) * Nat.choose n ((q+1)/2))

def syndrome {n : ℕ} (Q : Finset (Finset (Fin n))) : Fin n → ZMod 2 :=
  fun v => ∑ F ∈ Q, if v ∈ F then 1 else 0

end KikuchiMoore.Moore


