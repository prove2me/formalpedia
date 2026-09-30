-- Prove2me | Definitions.Def_KKBinPacking_GeometricGrouping_Instance
-- name    : KKBinPacking_GeometricGrouping_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T17:04:14.958857+00:00
-- url     : https://prove2.me/theorems/588b9e32-4c83-45d2-8168-874e22fe5749
-- title:
--   Bin-packing instances, packings, $OPT$, $SIZE$, $n$, $m$ and the smallest size $a(I)$
-- statement:
--   An **instance** $I$ of the one-dimensional bin-packing problem is a finite multiset of piece sizes, each a real number strictly between $0$ and $1$. For an instance $I$:
--
--   1. $n(I)$ is the number of pieces (counted with multiplicity), $m(I)$ the number of distinct sizes, $SIZE(I)$ the sum of all piece sizes, and $a(I)$ the smallest piece size.
--   2. A **packing** of $I$ is a finite multiset of bins, each bin a multiset of sizes, such that the bins together contain exactly the pieces of $I$ and every bin has total size at most $1$. Its **cost** is the number of bins.
--   3. $OPT(I)$ is the minimum cost of a packing of $I$.
--
--   These are the objects of §2 of the paper, shared by every statement of the mission.
--
--   **Formalization Note** An instance is a `Multiset ℝ` together with the predicate `IsInstance I` (every size in the open interval $(0,1)$). The paper's "rational number between 0 and 1" is read as the open interval (the grouping argument of Theorem 2 needs every size to be below $1$), and real sizes generalize rational ones. A packing is a `Multiset (Multiset ℝ)` whose `join` is $I$; empty bins are allowed and counted. $OPT(I)$ is the infimum over natural numbers of the costs of packings; for an instance the set is nonempty (one piece per bin), so the infimum is attained. `minSize I` is $a(I)$ for nonempty $I$; on the empty multiset it returns $1$, and every statement using it assumes $I \neq \emptyset$.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 312, §2 (model, OPT(I), n(I), m(I), SIZE(I), a(I))

import Mathlib

namespace KKBinPacking.GeometricGrouping

/-- An instance of one-dimensional bin packing (p. 312): a finite multiset of piece sizes,
each strictly between `0` and `1`. -/
def IsInstance (I : Multiset ℝ) : Prop := ∀ x ∈ I, 0 < x ∧ x < 1

/-- `n(I)`, the number of pieces of `I` (p. 312). -/
def numPieces (I : Multiset ℝ) : ℕ := Multiset.card I

/-- `m(I)`, the number of distinct piece sizes of `I` (p. 312). -/
noncomputable def numSizes (I : Multiset ℝ) : ℕ := I.toFinset.card

/-- `SIZE(I)`, the sum of the sizes of all pieces of `I` (p. 312). -/
def SIZE (I : Multiset ℝ) : ℝ := I.sum

/-- `a(I)`, the smallest piece size of `I` (p. 312). Only meaningful for nonempty `I`; every
theorem using it assumes `I ≠ 0`. On the empty multiset it returns `1` (so `ln(1/a(I)) = 0`). -/
noncomputable def minSize (I : Multiset ℝ) : ℝ :=
  if h : I.toFinset.Nonempty then I.toFinset.min' h else 1

/-- A packing of `I`: a multiset of bins (each a multiset of piece sizes) whose union is
exactly `I` and in which every bin has total size at most `1`. Its cost is its number of
bins, `Multiset.card P`; empty bins are allowed and counted. -/
def IsPacking (I : Multiset ℝ) (P : Multiset (Multiset ℝ)) : Prop :=
  P.join = I ∧ ∀ b ∈ P, b.sum ≤ 1

/-- `OPT(I)`, the minimum number of bins in a packing of `I` (p. 312). For an instance the set
is nonempty (one piece per bin), so the infimum is attained. -/
noncomputable def OPT (I : Multiset ℝ) : ℕ :=
  sInf {B : ℕ | ∃ P : Multiset (Multiset ℝ), IsPacking I P ∧ Multiset.card P = B}

end KKBinPacking.GeometricGrouping


