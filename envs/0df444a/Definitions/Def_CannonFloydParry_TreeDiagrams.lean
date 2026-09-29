-- Prove2me | Definitions.Def_CannonFloydParry_TreeDiagrams
-- name    : CannonFloydParry_TreeDiagrams
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-16T21:07:01.583807+00:00
-- url     : https://prove2.me/theorems/05445fd1-8dca-46a3-812d-3a57e527aba0
-- title:
--   Tree diagrams for Thompson's group $F$
-- statement:
--   The rest of section 2's vocabulary: standard dyadic intervals and
--   partitions, tree diagrams and the element of $F$ a diagram represents, reducedness, the
--   generators $X_n$, the words they form, and the positive elements. Everything in section 2 that
--   mentions $F$ is here; the two standard-dyadic predicates do not mention it, but they belong
--   with the diagrams they qualify. The tree type and the partition its leaves cut out are imported
--   from the companion definition, as is $F$ itself; neither is redefined here.
--
--   **Standard dyadic intervals and partitions.** A *standard dyadic interval* is one of the form
--   $[a/2^n, (a+1)/2^n]$ with $a$ and $n$ nonnegative integers and $a+1 \le 2^n$ (p. 219), stated as
--   a relation between the two endpoints. A *standard dyadic partition* of $[0,1]$ is given by its
--   increasing list of breakpoints, starting at $0$, ending at $1$, and with every consecutive pair
--   a standard dyadic interval (p. 220). Since a standard dyadic interval has distinct endpoints,
--   that consecutive-pair condition already forces the list to increase.
--
--   **Tree diagrams.** A *tree diagram* is an ordered pair of trees with the same number of leaves
--   (p. 221); the first is the domain tree, the second the range tree. An element $f$ of $F$ is *the
--   function of* a tree diagram when $f$ is affine on every interval of the partition cut out by the
--   domain tree and carries that partition's breakpoints, in order, to those of the partition cut
--   out by the range tree. Note that membership in $F$ does not by itself make $f$ affine on the
--   intervals of that partition: it provides only *some* finite set of breakpoints off which $f$ is
--   affine, and that set need not sit inside the domain tree's marks. Nothing here asks the slopes
--   to be powers of two; for these maps that is a consequence rather than a hypothesis.
--
--   **Generators.** The source's $X_0 = A$ and $X_n = A^{-(n-1)} B A^{n-1}$ for $n \ge 1$ (p. 217),
--   so that $X_1 = B$; $A$ and $B$ are the two generators already constructed in the imported
--   definition of $F$. An element of $F$ is *positive* when it is a product
--   $X_0^{b_0} X_1^{b_1} \cdots X_n^{b_n}$ with every exponent a nonnegative integer (p. 224).
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 pp. 219-224 (standard dyadic partitions, tree diagrams, positive elements) and section 1 p. 217 (the generators X_n)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Mathlib

/-!
# Tree diagrams for Thompson's group `F`

Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*,
L'Enseignement Mathématique (2) **42** (1996), 215–256, §2 (pages 219–224), with the
generators `Xₙ` from §1 (page 217).

The rest of §2's vocabulary: standard dyadic intervals and partitions, tree diagrams and the
element of `F` a diagram represents, reducedness, the generators `Xₙ`, the words they form, and
the positive elements.  Everything in §2 that mentions `F` is here; the two standard-dyadic
predicates do not mention it, but they belong with the diagrams they qualify.

Two files are imported and neither is redefined here.  `Def_CannonFloydParry` supplies `F`,
`UI`, `IsThompson`, `IsDyadic`, `extend`, and the generators `mapA` and `mapB`, so that
`X₀ = mapA` and `X₁ = mapB`.  `Def_CannonFloydParry_Trees` supplies the tree type `TTree` and,
in particular, `leafCount` and `marks` — the partition of `[0,1]` cut out by a tree's leaves —
which is what a tree diagram is read against.
-/

namespace CannonFloydParry

/-! ### Standard dyadic intervals and partitions -/

/-- A **standard dyadic interval** in `[0,1]`: one of the form `[a / 2 ^ n, (a + 1) / 2 ^ n]`
with `a` and `n` nonnegative integers and `a ≤ 2 ^ n - 1` (CFP p. 219).  Stated as a relation
on the two endpoints. -/
def IsStandardDyadicInterval (x y : ℝ) : Prop :=
  ∃ a n : ℕ, a + 1 ≤ 2 ^ n ∧ x = (a : ℝ) / 2 ^ n ∧ y = ((a : ℝ) + 1) / 2 ^ n

/-- A **standard dyadic partition** of `[0,1]`: a partition `0 = x₀ < ⋯ < xₙ = 1` all of whose
intervals are standard dyadic intervals (CFP p. 220), as the list of its breakpoints.

`List.IsChain` says consecutive entries are related, and `IsStandardDyadicInterval x y` already
forces `x < y`, so the increasing condition is not stated separately. -/
def IsStandardDyadicPartition (xs : List ℝ) : Prop :=
  xs.head? = some 0 ∧ xs.getLast? = some 1 ∧ xs.IsChain IsStandardDyadicInterval

/-! ### Tree diagrams -/

/-- A **tree diagram** (CFP p. 221): an ordered pair of trees with the same number of leaves.
`dom` is the *domain tree*, `ran` the *range tree*. -/
structure TreeDiagram where
  dom : TTree
  ran : TTree
  leaves_eq : dom.leafCount = ran.leafCount

/-- `L` is **affine on every interval** cut out by the list `xs` of breakpoints: between each
consecutive pair there are `a`, `c` with `L z = a * z + c` throughout the closed interval.

This is CFP's "linear on every interval of the partition" (p. 220).  Nothing here asks the
slope to be a power of two; for the maps this is applied to that is a consequence, not a
hypothesis.

The pieces are cut out by *consecutive entries in list order*, not by the set of entries, and
the condition is imposed on the closed interval, so consecutive constraints overlap at the
shared endpoint.  On a list of fewer than two entries there is nothing to check, and on a pair
that decreases the interval is empty and nothing is required — the predicate does not itself
demand an increasing list.  It is only ever applied to `marks`, which does increase. -/
def AffineOnPieces (L : ℝ ≃o ℝ) (xs : List ℝ) : Prop :=
  xs.IsChain (fun u v => ∃ a c : ℝ, ∀ z ∈ Set.Icc u v, L z = a * z + c)

/-- `f` is **the function of the tree diagram** `d` (CFP p. 221): `f` lies in `F`, is affine on
every interval of the partition cut out by the domain tree, and carries the breakpoints of that
partition, in order, to those of the partition cut out by the range tree.

Membership in `F` does not by itself make `f` affine on the intervals of the domain tree's
partition: it provides only *some* finite set of breakpoints off which `f` is affine, and that
set need not sit inside the tree's marks. -/
def Represents (d : TreeDiagram) (f : UI ≃o UI) : Prop :=
  f ∈ F ∧ AffineOnPieces (extend f) d.dom.marks ∧
    d.dom.marks.map (extend f) = d.ran.marks

/-- A tree diagram is **reduced** when no position admits a caret in *both* trees: there is no
`k` such that the `k`th and `(k+1)`th leaves of the domain tree are siblings and the `k`th and
`(k+1)`th leaves of the range tree are siblings (CFP p. 221).

CFP phrase it as the absence of carets `C` in the domain tree and `D` in the range tree at a
common position; deleting such a pair, keeping their roots, would give a smaller tree diagram
for the same element, which is why its absence is the right notion of irreducibility. -/
def IsReduced (d : TreeDiagram) : Prop :=
  ∀ k : ℕ, ¬ (d.dom.caretAt k = true ∧ d.ran.caretAt k = true)


/-! ### The generators `Xₙ` -/

/-- CFP's generators (p. 217): `X₀ = A` and `Xₙ = A^{-(n-1)} B A^{n-1}` for `n ≥ 1`.  In
particular `X₁ = B`.  `A` and `B` are `mapA` and `mapB` of the imported bundle. -/
noncomputable def X : ℕ → UI ≃o UI
  | 0 => mapA
  | n + 1 => (mapA ^ n)⁻¹ * mapB * mapA ^ n

/-- `X₀` is `A`. -/
@[simp] theorem X_zero : X 0 = mapA := rfl

/-- `X₁` is `B`. -/
@[simp] theorem X_one : X 1 = mapB := by
  show (mapA ^ 0)⁻¹ * mapB * mapA ^ 0 = mapB
  simp

/-- The word `X i ^ c₀ * X (i+1) ^ c₁ * ⋯`, reading exponents off a list and starting the index
at `i`. -/
noncomputable def wordFrom (i : ℕ) : List ℕ → UI ≃o UI
  | [] => 1
  | c :: cs => X i ^ c * wordFrom (i + 1) cs

/-- The positive word `X₀ ^ c₀ * X₁ ^ c₁ * ⋯ * Xₙ ^ cₙ` determined by a list of nonnegative
exponents, smallest index leftmost.  This is the shape of CFP's positive elements (p. 224), and
the left half of their normal form; the right half is the inverse of such a word. -/
noncomputable def word (cs : List ℕ) : UI ≃o UI := wordFrom 0 cs

/-- The **positive** elements of `F` (CFP p. 224): the products `X₀^{b₀} ⋯ Xₙ^{bₙ}` with every
`bₖ` a nonnegative integer. -/
def IsPositive (f : UI ≃o UI) : Prop := ∃ cs : List ℕ, f = word cs

/-- CFP's conditions on the exponent data of a normal form (p. 224).  Writing `n + 1` for the
common length, the two lists are nonempty and of equal length; **exactly one** of the last
entries `aₙ`, `bₙ` is nonzero; and if `aₖ` and `bₖ` are both positive for some `k < n`, then
`a_{k+1}` or `b_{k+1}` is positive.

Entries are read with `List.getD` and default `0`, so an index past the end reads as `0`; the
length condition means that never happens for the indices actually constrained. -/
def IsNormalFormData (as bs : List ℕ) : Prop :=
  as ≠ [] ∧ as.length = bs.length ∧
    ((as.getD (as.length - 1) 0 = 0 ∧ 0 < bs.getD (as.length - 1) 0) ∨
      (0 < as.getD (as.length - 1) 0 ∧ bs.getD (as.length - 1) 0 = 0)) ∧
    ∀ k, k + 1 < as.length →
      0 < as.getD k 0 → 0 < bs.getD k 0 → 0 < as.getD (k + 1) 0 ∨ 0 < bs.getD (k + 1) 0

end CannonFloydParry


