-- Prove2me | Definitions.Def_CirclePackingConstants
-- name    : CirclePackingConstants
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-12T10:50:13.44318+00:00
-- url     : https://prove2.me/theorems/6b35fc67-89d7-4609-8140-b6db42175724
-- title:
--   Equal-circle packing constants in the unit square
-- statement:
--   Defines admissible packings of $n$ congruent disks in the unit square, the supremal radius $r_n$, and the covered-area constant $c_n=n\pi r_n^2$.
-- source:
--   User-supplied Circles in squares: proofs and bounds, p. 1, and accompanying CirclePacking.lean source package, supplied September 12, 2026.

import Mathlib

noncomputable section

namespace CirclePackingConstants

abbrev Point := ℝ × ℝ

/-- Squared Euclidean distance in Cartesian coordinates. -/
def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Coordinate containment conditions for a disk center in the unit square. -/
def InInnerSquare (r : ℝ) (p : Point) : Prop :=
  r ≤ p.1 ∧ p.1 ≤ 1 - r ∧ r ≤ p.2 ∧ p.2 ≤ 1 - r

/-- `n` equal disks of radius `r` fit in the unit square with disjoint interiors. -/
def Packable (n : ℕ) (r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ 1 / 2 ∧
    ∃ p : Fin n → Point,
      (∀ i, InInnerSquare r (p i)) ∧
      ∀ i j, i ≠ j → (2 * r) ^ 2 ≤ sqDist (p i) (p j)

/-- The supremum of radii admitted by `Packable`. -/
def r_n (n : ℕ) : ℝ := sSup {r : ℝ | Packable n r}

/-- The optimal covered-area fraction for `n` equal disks in the unit square. -/
def c_n (n : ℕ) : ℝ := (n : ℝ) * Real.pi * (r_n n) ^ 2

end CirclePackingConstants


