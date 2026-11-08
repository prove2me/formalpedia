-- Prove2me | Definitions.Def_ZeroExtensionGap_RandomPartition
-- name    : ZeroExtensionGap_RandomPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:37.964283+00:00
-- url     : https://prove2.me/theorems/fe78f48d-da16-4243-9383-dd33b8f91a84
-- title:
--   Bounded random partitions, separation probability, restriction and retractions
-- statement:
--   A partition of $Z$ is **$\Lambda$-bounded** for a distance $d$ if every two vertices in the same part have distance at most $\Lambda$, and a random partition is $\Lambda$-bounded if this holds with probability one. Distances are ambient, so shortest paths may leave $Z$. The separation probability of $x,y$ is $\Pr[P(x)\ne P(y)]$. The restriction of a partition to a subset discards empty parts. A **retraction** onto $B$ is a map $g$ into $B$ with $g(b)=b$ for $b\in B$.
--
--   **Formalization Note.** A random partition is its law, `PMF (Finpartition Z)`, which loses nothing because partitions of a finite set form a finite type. Bounded means bounded on the whole support. `Finpartition.part x` is the part containing $x$.
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), §5, p.21 (PDF p.23); §5.2, p.23 (PDF p.25)

import Mathlib

open scoped ENNReal

namespace ZeroExtensionGap

variable {α : Type*} [DecidableEq α]

/-- A `Λ`-bounded partition of `Z` for the distance `d`: every two vertices in the same part have
distance at most `Λ`. §5, p.21 (PDF p.23) (Chen, Zhu, *Almost Tight Hardness of Approximation for
0-Extension*, STOC 2027 submission, manuscript sha256 0cdea87b…). The distance is the ambient one,
"so shortest paths may leave Z". -/
def IsBoundedPartition (d : α → α → ℝ≥0∞) (Λ : ℝ) {Z : Finset α} (Q : Finpartition Z) : Prop :=
  ∀ x ∈ Z, ∀ y ∈ Z, Q.part x = Q.part y → d x y ≤ ENNReal.ofReal Λ

/-- A random partition is `Λ`-bounded if this holds with probability one (§5, p.21, PDF p.23).
**Formalization Note.** A random partition of a finite set is its law, a `PMF (Finpartition Z)`:
partitions of a finite set form a finite type, whatever process generated them. -/
def IsBoundedRandomPartition (d : α → α → ℝ≥0∞) (Λ : ℝ) {Z : Finset α}
    (P : PMF (Finpartition Z)) : Prop :=
  ∀ Q ∈ P.support, IsBoundedPartition d Λ Q

/-- The probability `Pr[P(x) ≠ P(y)]`. -/
noncomputable def separationProb {Z : Finset α} (P : PMF (Finpartition Z)) (x y : α) : ℝ :=
  (P.toOuterMeasure {Q | Q.part x ≠ Q.part y}).toReal

/-- The restriction to `A` of a partition of the whole vertex set, with empty parts discarded (§5,
p.21, PDF p.23). -/
def restrictPartition [Fintype α] (A : Finset α) (Q : Finpartition (Finset.univ : Finset α)) :
    Finpartition A :=
  (Q.avoid (Finset.univ \ A)).copy (by ext x; simp)

/-- A retraction of `M` onto `B`: a map `g : M → B` with `g(b) = b` for every `b ∈ B` (p.23, PDF p.25). -/
def IsRetractionOnto (B : Finset α) (g : α → α) : Prop :=
  (∀ x, g x ∈ B) ∧ ∀ b ∈ B, g b = b

end ZeroExtensionGap


