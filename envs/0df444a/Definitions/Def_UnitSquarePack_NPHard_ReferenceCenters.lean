-- Prove2me | Definitions.Def_UnitSquarePack_NPHard_ReferenceCenters
-- name    : UnitSquarePack_NPHard_ReferenceCenters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:19:41.852921+00:00
-- url     : https://prove2.me/theorems/e86d8b14-cb11-4e11-b3ea-7eddd4b8d071
-- title:
--   Reference centers, quadrants, and the push directions of squares in integer packings
-- statement:
--   For $x, y \in \mathbb Z$ the **regular reference cell** with upper right corner $(2x, 2y)$ is the unit square $R(x,y) = [2x-1, 2x] \times [2y-1, 2y]$; the **shifted** cell is $[2x, 2x+1] \times [2y-1, 2y]$. Given a set $P$ and a set of rows $I \subseteq \mathbb Z$, a **reference center** of $P$ is a unit square of the form $[2k-1, 2k] \times [2\ell-1, 2\ell]$ with $\ell \in I$, or $[2k, 2k+1] \times [2\ell-1, 2\ell]$ with $\ell \notin I$, that is contained in $P$. With $I = \mathbb Z$ these are the regular reference centers of §2.2.
--
--   The square $Q(c) = [a, a+2] \times [b, b+2]$ has four unit **quadrants**: lower-left $[a,a+1]\times[b,b+1]$, lower-right $[a+1,a+2]\times[b,b+1]$, upper-left $[a,a+1]\times[b+1,b+2]$ and upper-right $[a+1,a+2]\times[b+1,b+2]$. Relative to a reference center $R$ that it covers, the square **pushes up** (resp. down, left, right) if $R$ is contained in one of its lower (resp. upper, right, left) quadrants.
--
--   An **integer packing** is a set $S \subseteq \mathbb Z^2$ of lower-left corners whose squares $Q(s)$, $s \in S$, have pairwise disjoint interiors. Following the paper, $\langle x, y\rangle$ denotes the square of $S$ covering $R(x,y)$ (there is at most one, as two squares containing the same unit cell overlap). The predicates `Covers S x y`, `RefPushesUp S x y`, `RefPushesDown`, `RefPushesLeft`, `RefPushesRight` say that $\langle x, y\rangle$ exists, and that it exists and pushes in the given direction. For a column range $X_1 \le x \le X_2$, the **row** $y$ is the set of squares of $S$ covering some $R(x, y)$ with $X_1 \le x \le X_2$.
--
--   Concretely, the square with corner $(a, b) \in \mathbb Z^2$ covering $R(x,y)$ has $a \in \{2x-2, 2x-1\}$ and $b \in \{2y-2, 2y-1\}$; it pushes up iff $b = 2y-1$, down iff $b = 2y-2$, right iff $a = 2x-1$ and left iff $a = 2x-2$.
--
--   For the possibly shifted rows of §4.6, `rowRefCell I x y` selects the regular cell when y ∈ I and the shifted cell otherwise. `IsPerfectIntPacking P I S` requires an integer packing contained in P covering every reference cell contained in P. In a bounded grid polygon this agrees with the cardinality definition of perfect packing: every square covers exactly one reference center. `rowSquaresFor`, `upRowSquares`, and `downRowSquares` collect all squares in a row, without clipping it to a common column interval.
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 6, §2.2 (reference centers, perfect packings, pushing); p. 23, §4.3

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_Squares

set_option autoImplicit false

namespace UnitSquarePack.NPHard

open Set

/-- The regular reference cell with upper right corner `(2x, 2y)`:
the unit square `[2x - 1, 2x] × [2y - 1, 2y]`. -/
def refCell (x y : ℤ) : Set (ℝ × ℝ) :=
  Icc (2 * (x : ℝ) - 1) (2 * x) ×ˢ Icc (2 * (y : ℝ) - 1) (2 * y)

/-- The shifted reference cell `[2x, 2x + 1] × [2y - 1, 2y]`, used on the rows `y ∉ I`
of Lemma 23. -/
def shiftedRefCell (x y : ℤ) : Set (ℝ × ℝ) :=
  Icc (2 * (x : ℝ)) (2 * x + 1) ×ˢ Icc (2 * (y : ℝ) - 1) (2 * y)

/-- `R` is a reference center of `P` for the row set `I ⊆ ℤ`: `R` is a unit square of the form
`[2k - 1, 2k] × [2ℓ - 1, 2ℓ]` with `ℓ ∈ I`, or `[2k, 2k + 1] × [2ℓ - 1, 2ℓ]` with `ℓ ∉ I`,
for some `k, ℓ ∈ ℤ`, and `R ⊆ P`. (With `I = ℤ` these are the regular reference centers.) -/
def IsReferenceCenter (P : Set (ℝ × ℝ)) (I : Set ℤ) (R : Set (ℝ × ℝ)) : Prop :=
  (∃ k ℓ : ℤ, (ℓ ∈ I ∧ R = refCell k ℓ) ∨ (ℓ ∉ I ∧ R = shiftedRefCell k ℓ)) ∧ R ⊆ P

/-- The four unit quadrants of the square `square2 c`, `c = (a, b)`. -/
def lowerLeftQuadrant (c : ℝ × ℝ) : Set (ℝ × ℝ) := Icc c.1 (c.1 + 1) ×ˢ Icc c.2 (c.2 + 1)
def lowerRightQuadrant (c : ℝ × ℝ) : Set (ℝ × ℝ) := Icc (c.1 + 1) (c.1 + 2) ×ˢ Icc c.2 (c.2 + 1)
def upperLeftQuadrant (c : ℝ × ℝ) : Set (ℝ × ℝ) := Icc c.1 (c.1 + 1) ×ˢ Icc (c.2 + 1) (c.2 + 2)
def upperRightQuadrant (c : ℝ × ℝ) : Set (ℝ × ℝ) :=
  Icc (c.1 + 1) (c.1 + 2) ×ˢ Icc (c.2 + 1) (c.2 + 2)

/-- The square `square2 c` *pushes up* relative to the reference center `R` it covers: `R` is
contained in one of its two lower quadrants (p. 6). -/
def PushesUp (R : Set (ℝ × ℝ)) (c : ℝ × ℝ) : Prop :=
  R ⊆ lowerLeftQuadrant c ∨ R ⊆ lowerRightQuadrant c

/-- Pushes down: `R` is contained in one of the two upper quadrants. -/
def PushesDown (R : Set (ℝ × ℝ)) (c : ℝ × ℝ) : Prop :=
  R ⊆ upperLeftQuadrant c ∨ R ⊆ upperRightQuadrant c

/-- Pushes left: `R` is contained in one of the two right quadrants. -/
def PushesLeft (R : Set (ℝ × ℝ)) (c : ℝ × ℝ) : Prop :=
  R ⊆ lowerRightQuadrant c ∨ R ⊆ upperRightQuadrant c

/-- Pushes right: `R` is contained in one of the two left quadrants. -/
def PushesRight (R : Set (ℝ × ℝ)) (c : ℝ × ℝ) : Prop :=
  R ⊆ lowerLeftQuadrant c ∨ R ⊆ upperLeftQuadrant c

/-- A packing of `2 × 2` squares with integer coordinates, given by the set `S ⊆ ℤ²` of the
lower-left corners of its squares: distinct squares have disjoint interiors. -/
def IsIntPacking (S : Set (ℤ × ℤ)) : Prop :=
  S.Pairwise fun s t => Disjoint (interior (square2 (toPlane s))) (interior (square2 (toPlane t)))

/-- The regular reference center with upper right corner `(2x, 2y)` is covered by a square of
the packing `S` (this square is unique, since two squares containing it overlap). -/
def Covers (S : Set (ℤ × ℤ)) (x y : ℤ) : Prop :=
  ∃ s ∈ S, refCell x y ⊆ square2 (toPlane s)

/-- `⟨x, y⟩ pushes up`: the square of `S` covering the reference center with upper right corner
`(2x, 2y)` pushes up. -/
def RefPushesUp (S : Set (ℤ × ℤ)) (x y : ℤ) : Prop :=
  ∃ s ∈ S, refCell x y ⊆ square2 (toPlane s) ∧ PushesUp (refCell x y) (toPlane s)

/-- `⟨x, y⟩ pushes down`. -/
def RefPushesDown (S : Set (ℤ × ℤ)) (x y : ℤ) : Prop :=
  ∃ s ∈ S, refCell x y ⊆ square2 (toPlane s) ∧ PushesDown (refCell x y) (toPlane s)

/-- `⟨x, y⟩ pushes left`. -/
def RefPushesLeft (S : Set (ℤ × ℤ)) (x y : ℤ) : Prop :=
  ∃ s ∈ S, refCell x y ⊆ square2 (toPlane s) ∧ PushesLeft (refCell x y) (toPlane s)

/-- `⟨x, y⟩ pushes right`. -/
def RefPushesRight (S : Set (ℤ × ℤ)) (x y : ℤ) : Prop :=
  ∃ s ∈ S, refCell x y ⊆ square2 (toPlane s) ∧ PushesRight (refCell x y) (toPlane s)

/-- The squares of the row `y` over the column range `X₁ ≤ x ≤ X₂`: the squares of `S` covering
one of the reference centers `⟨x, y⟩`, `X₁ ≤ x ≤ X₂`. -/
def rowSquares (S : Set (ℤ × ℤ)) (X₁ X₂ y : ℤ) : Set (ℤ × ℤ) :=
  {s | s ∈ S ∧ ∃ x : ℤ, X₁ ≤ x ∧ x ≤ X₂ ∧ refCell x y ⊆ square2 (toPlane s)}

/-- The reference cell in row `y`, with the row shifts allowed by §4.3.
Rows in `I` use the regular cells; other rows use the cells shifted one unit right. -/
noncomputable def rowRefCell (I : Set ℤ) (x y : ℤ) : Set (ℝ × ℝ) :=
  by
    classical
    exact if y ∈ I then refCell x y else shiftedRefCell x y

/-- A perfect integer packing of `P` for the reference centers of Lemma 23.
Every square is contained in `P`, and every reference center of `P` is covered.
For a bounded grid polygon this is equivalent to the paper's cardinality definition:
each integer square contains exactly one center and two squares cannot cover the same center. -/
def IsPerfectIntPacking (P : Set (ℝ × ℝ)) (I : Set ℤ) (S : Set (ℤ × ℤ)) : Prop :=
  IsIntPacking S ∧ (∀ s ∈ S, square2 (toPlane s) ⊆ P) ∧
    ∀ x y : ℤ, rowRefCell I x y ⊆ P → ∃ s ∈ S, rowRefCell I x y ⊆ square2 (toPlane s)

/-- All squares of row `y`, with its actual (possibly shifted) reference centers. -/
def rowSquaresFor (S : Set (ℤ × ℤ)) (I : Set ℤ) (y : ℤ) : Set (ℤ × ℤ) :=
  {s | s ∈ S ∧ ∃ x : ℤ, rowRefCell I x y ⊆ square2 (toPlane s)}

/-- Up-pushing squares of row `y`, including shifted rows. -/
def upRowSquares (S : Set (ℤ × ℤ)) (I : Set ℤ) (y : ℤ) : Set (ℤ × ℤ) :=
  {s | s ∈ S ∧ ∃ x : ℤ, rowRefCell I x y ⊆ square2 (toPlane s) ∧
    PushesUp (rowRefCell I x y) (toPlane s)}

/-- Down-pushing squares of row `y`, including shifted rows. -/
def downRowSquares (S : Set (ℤ × ℤ)) (I : Set ℤ) (y : ℤ) : Set (ℤ × ℤ) :=
  {s | s ∈ S ∧ ∃ x : ℤ, rowRefCell I x y ⊆ square2 (toPlane s) ∧
    PushesDown (rowRefCell I x y) (toPlane s)}

end UnitSquarePack.NPHard


