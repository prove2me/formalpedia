-- Prove2me | Definitions.Def_MongeApprox_Sparsify_Quadrant
-- name    : MongeApprox_Sparsify_Quadrant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:01:22.392115+00:00
-- url     : https://prove2.me/theorems/9939ac1e-06a6-4ed6-b724-5935ac23627b
-- title:
--   Measures on positions, quadrants $Q_{ij}$, rectangles, 'strictly inside', 'strictly to the lower left', and the Lemma 7.5 replacement property (§7)
-- statement:
--   A nonnegative matrix $\mu$ is identified with the measure $\mu(S):=\sum_{(a,b)\in S}\mu_{ab}$ on sets $S\subseteq\mathbb Z^2$ of positions, positions outside the matrix having mass zero. The **quadrant** with corner $(i,j)\in\mathbb Z^2$ is $Q_{ij}:=\{(a,b)\in\mathbb Z^2: a\ge i,\ b<j\}$. A **rectangle** is $R=[x..x')\times[y..y')$; a point $(i,j)$ lies **strictly inside** $R$ if $x<i<x'$ and $y<j<y'$. A position $(a',b')$ lies **strictly to the lower left** of $(a,b)$ if $a'>a$ and $b'<b$. Row sums, column sums, the nonzero rows and columns of $\mu$ in $R$, the restriction of $\mu$ to $R$, and the **replacement property** of Lemma 7.5: $\widehat\mu\ge0$ is supported on $R$, has the same row and column sums as $\mu$, at most $r+c-1$ nonzero entries ($r$, $c$ the numbers of nonzero rows and columns of $\mu$), and $\mu(Q_{ij})\le\widehat\mu(Q_{ij})\le\mu(R)$ for all integers $i,j$, with equality in the first inequality unless $(i,j)$ lies strictly inside $R$.
--
--   **Formalization Note.** A matrix on positions is a function `ℤ × ℤ → ℝ`; `mass μ S` is the finite sum `∑ᶠ z ∈ S, μ z`, which is the true sum whenever $\mu$ has finite support (every statement assumes this, directly or through support on a rectangle). `Rect` stores the four integer bounds (empty when $x'\le x$ or $y'\le y$). `rowSum`/`colSum` are `∑ᶠ` over the other coordinate. The bound "at most $r+c-1$ nonzero entries" is written `count + 1 ≤ r + c`.
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), §7 Quadrants and Rectangle replacement, printed p. 36 (PDF 38); Lemma 7.5, printed p. 36 (PDF 38)

import Mathlib

/-!
# Measures on positions, quadrants, rectangles, and rectangle replacements

Gorbachev, *Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes*
(2026, PDF sha256 b7eeb435…), §7 "Quadrants" and "Rectangle replacement", printed p. 36
(PDF 38); "strictly to the lower left", printed p. 36 (PDF 38).

Conventions.
* A nonnegative matrix `µ` is a function on positions `ℤ × ℤ` (first coordinate = row, growing
  downward; second = column), with mass `0` at every position outside the matrix. Its measure of a
  set `S` of positions is `mass µ S := Σ_{(a,b) ∈ S} µ_ab`, written as the finite sum `∑ᶠ`; every
  statement that uses it has `µ` finitely supported (on a rectangle, or by hypothesis).
* `Q i j := {(a, b) ∈ ℤ² : a ≥ i, b < j}`, the quadrant with corner `(i, j)`.
* A rectangle `R = [x..x′) × [y..y′)` is `Rect.mk x x' y y'` (integers; empty when `x′ ≤ x` or
  `y′ ≤ y`). `R.toSet` is its set of positions and `R.positions` the same as a finset.
* `(i, j)` lies strictly inside `R` iff `x < i < x′` and `y < j < y′`.
* `(a′, b′)` lies strictly to the lower left of `(a, b)` iff `a′ > a` and `b′ < b`.
* `R.restrict µ` is `µ` on `R` and `0` elsewhere.
* `rowSum µ a = Σ_b µ_ab`, `colSum µ b = Σ_a µ_ab`; `nonzeroRows µ R` / `nonzeroCols µ R` are the
  rows / columns of `R` that contain a nonzero entry of `µ` (for `µ ≥ 0` supported on `R`, exactly
  the rows / columns with nonzero sum).
* `IsRectReplacement µ R µ̂` is the conclusion of Lemma 7.5 for `µ` on `R`: `µ̂ ≥ 0` is supported
  on `R`, has the same row and column sums as `µ`, at most `r + c − 1` nonzero entries
  (`r`, `c` = number of nonzero rows / columns of `µ`), and for all integers `i, j`,
  `µ(Q_ij) ≤ µ̂(Q_ij) ≤ µ(R)`, the first inequality being an equality unless `(i, j)` lies strictly
  inside `R`.
-/

namespace MongeApprox.Sparsify

/-- The measure `µ(S) := Σ_{(a,b) ∈ S} µ_ab` of a set of positions. -/
noncomputable def mass (μ : ℤ × ℤ → ℝ) (S : Set (ℤ × ℤ)) : ℝ :=
  ∑ᶠ z ∈ S, μ z

/-- The quadrant with corner `(i, j)`: `Q_ij := {(a, b) ∈ ℤ² : a ≥ i, b < j}`. -/
def Q (i j : ℤ) : Set (ℤ × ℤ) :=
  {z | i ≤ z.1 ∧ z.2 < j}

/-- A rectangle `[x..x′) × [y..y′)` of positions (rows `[x..x′)`, columns `[y..y′)`). -/
structure Rect where
  x : ℤ
  x' : ℤ
  y : ℤ
  y' : ℤ

/-- The positions of a rectangle, as a set. -/
def Rect.toSet (R : Rect) : Set (ℤ × ℤ) :=
  {z | R.x ≤ z.1 ∧ z.1 < R.x' ∧ R.y ≤ z.2 ∧ z.2 < R.y'}

/-- The positions of a rectangle, as a finset. -/
noncomputable def Rect.positions (R : Rect) : Finset (ℤ × ℤ) :=
  Finset.Ico R.x R.x' ×ˢ Finset.Ico R.y R.y'

/-- The restriction of `µ` to `R`: `µ` on the positions of `R`, `0` elsewhere. -/
noncomputable def Rect.restrict (R : Rect) (μ : ℤ × ℤ → ℝ) (z : ℤ × ℤ) : ℝ :=
  open Classical in
  if z ∈ R.toSet then μ z else 0

/-- `(i, j)` lies strictly inside `R = [x..x′) × [y..y′)`: `x < i < x′` and `y < j < y′`. -/
def StrictlyInside (i j : ℤ) (R : Rect) : Prop :=
  R.x < i ∧ i < R.x' ∧ R.y < j ∧ j < R.y'

/-- The position `(a', b')` lies strictly to the lower left of `(a, b)`: `a' > a` and `b' < b`. -/
def StrictlyLowerLeft (a' b' a b : ℤ) : Prop :=
  a < a' ∧ b' < b

/-- The row sum `Σ_b µ_ab` of row `a`. -/
noncomputable def rowSum (μ : ℤ × ℤ → ℝ) (a : ℤ) : ℝ :=
  ∑ᶠ b : ℤ, μ (a, b)

/-- The column sum `Σ_a µ_ab` of column `b`. -/
noncomputable def colSum (μ : ℤ × ℤ → ℝ) (b : ℤ) : ℝ :=
  ∑ᶠ a : ℤ, μ (a, b)

/-- The rows of `R` that contain a nonzero entry of `µ`. -/
noncomputable def nonzeroRows (μ : ℤ × ℤ → ℝ) (R : Rect) : Finset ℤ :=
  open Classical in
  (Finset.Ico R.x R.x').filter fun a => ∃ b ∈ Finset.Ico R.y R.y', μ (a, b) ≠ 0

/-- The columns of `R` that contain a nonzero entry of `µ`. -/
noncomputable def nonzeroCols (μ : ℤ × ℤ → ℝ) (R : Rect) : Finset ℤ :=
  open Classical in
  (Finset.Ico R.y R.y').filter fun b => ∃ a ∈ Finset.Ico R.x R.x', μ (a, b) ≠ 0

/-- The number of nonzero entries of `µ` inside `R`. -/
noncomputable def nonzeroCount (μ : ℤ × ℤ → ℝ) (R : Rect) : ℕ :=
  open Classical in
  (R.positions.filter fun z => μ z ≠ 0).card

/-- The conclusion of Lemma 7.5 for `µ` on `R`: `µ̂` is a nonnegative matrix supported on `R`
with the same row and column sums as `µ` and at most `r + c − 1` nonzero entries (`r`, `c` the
numbers of nonzero rows and columns of `µ`, so the bound is written `count + 1 ≤ r + c`), and
`µ(Q_ij) ≤ µ̂(Q_ij) ≤ µ(R)` for all integers `i, j`, with equality in the first inequality
unless `(i, j)` lies strictly inside `R`. -/
def IsRectReplacement (μ : ℤ × ℤ → ℝ) (R : Rect) (μhat : ℤ × ℤ → ℝ) : Prop :=
  (∀ z, 0 ≤ μhat z) ∧
  (∀ z, z ∉ R.toSet → μhat z = 0) ∧
  (∀ a, rowSum μhat a = rowSum μ a) ∧
  (∀ b, colSum μhat b = colSum μ b) ∧
  nonzeroCount μhat R + 1 ≤ (nonzeroRows μ R).card + (nonzeroCols μ R).card ∧
  (∀ i j : ℤ,
    mass μ (Q i j) ≤ mass μhat (Q i j) ∧ mass μhat (Q i j) ≤ mass μ R.toSet ∧
    (¬ StrictlyInside i j R → mass μ (Q i j) = mass μhat (Q i j)))

end MongeApprox.Sparsify


