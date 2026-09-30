-- Prove2me | Definitions.Def_KKBinPacking_LinearGrouping_Instance
-- name    : KKBinPacking_LinearGrouping_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:17:02.064398+00:00
-- url     : https://prove2.me/theorems/8d4b8613-1250-4231-9354-93a1f0991dac
-- title:
--   Bin-packing instances, packings, $OPT$, $SIZE$, $n$, $m$ and the order $I \le J$
-- statement:
--   An **instance** $I$ of the one-dimensional bin-packing problem is a finite multiset of piece sizes, each a real number strictly between $0$ and $1$. For an instance $I$:
--
--   1. $n(I)$ is the number of pieces (counted with multiplicity), $m(I)$ the number of distinct sizes, and $SIZE(I)$ the sum of all piece sizes.
--   2. A **packing** of $I$ is a finite multiset of bins, each bin a multiset of sizes, such that the bins together contain exactly the pieces of $I$ and every bin has total size at most $1$. Its **cost** is the number of bins.
--   3. $OPT(I)$ is the minimum cost of a packing of $I$.
--   4. For instances $I, J$ one writes $I \le J$ if there is a one-to-one map $f$ from the pieces of $I$ into the pieces of $J$ with $SIZE(x) \le SIZE(f(x))$ for every piece $x$ of $I$.
--
--   These are the objects of §2 and §4 of the paper, shared by every statement of the mission.
--
--   **Formalization Note** An instance is a `Multiset ℝ` together with the predicate `IsInstance I` (every size in the open interval $(0,1)$); the paper's "rational number between 0 and 1" is read as the open interval, and real sizes generalize rational ones. A packing is a `Multiset (Multiset ℝ)` whose `join` is $I$; empty bins are allowed and counted. $OPT(I)$ is the infimum over natural numbers of the costs of packings; for an instance the set is nonempty (one piece per bin), so the infimum is attained. The order $I \le J$ is encoded as: some sub-multiset $J_0 \le J$ can be matched to $I$ piece by piece with $x \le f(x)$ (`Multiset.Rel`).
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 312, §2 (model, OPT(I), n(I), m(I), SIZE(I)); p. 314, §4 Linear Grouping (the order I ≤ J)

import Mathlib

namespace KKBinPacking.LinearGrouping

/-- An instance of one-dimensional bin packing (p. 312): a finite multiset of piece sizes,
each strictly between `0` and `1`. -/
def IsInstance (I : Multiset ℝ) : Prop := ∀ x ∈ I, 0 < x ∧ x < 1

/-- `n(I)`, the number of pieces of `I` (p. 312). -/
def numPieces (I : Multiset ℝ) : ℕ := Multiset.card I

/-- `m(I)`, the number of distinct piece sizes of `I` (p. 312). -/
noncomputable def numSizes (I : Multiset ℝ) : ℕ := I.toFinset.card

/-- `SIZE(I)`, the sum of the sizes of all pieces of `I` (p. 312). -/
def SIZE (I : Multiset ℝ) : ℝ := I.sum

/-- A packing of `I`: a multiset of bins (each a multiset of piece sizes) whose union is
exactly `I` and in which every bin has total size at most `1`. Its cost is its number of
bins, `Multiset.card P`; empty bins are allowed and counted. -/
def IsPacking (I : Multiset ℝ) (P : Multiset (Multiset ℝ)) : Prop :=
  P.join = I ∧ ∀ b ∈ P, b.sum ≤ 1

/-- `OPT(I)`, the minimum number of bins in a packing of `I` (p. 312). For an instance the set
is nonempty (one piece per bin), so the infimum is attained. -/
noncomputable def OPT (I : Multiset ℝ) : ℕ :=
  sInf {B : ℕ | ∃ P : Multiset (Multiset ℝ), IsPacking I P ∧ Multiset.card P = B}

/-- The order `I ≤ J` of p. 314: there is a one-to-one map `f` from the pieces of `I` into the
pieces of `J` with `SIZE(x) ≤ SIZE(f(x))` for every piece `x` of `I`. Encoded as: some
sub-multiset `J₀` of `J` is matched to `I` piece by piece with `x ≤ f(x)`. -/
def InstLE (I J : Multiset ℝ) : Prop :=
  ∃ J₀ : Multiset ℝ, J₀ ≤ J ∧ Multiset.Rel (· ≤ ·) I J₀

end KKBinPacking.LinearGrouping


