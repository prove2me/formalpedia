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
--   generators $X_n$, the words they form, the positive elements and the normal-form data. The two
--   standard-dyadic predicates do not mention $F$, but they belong with the diagrams they qualify;
--   “negative” elements (p. 224) are not defined here. The tree type and the partition its leaves
--   cut out are imported from the companion trees definition, and $F$ from the Cannon–Floyd–Parry
--   definition of section 1; neither is redefined here.
--
--   **Standard dyadic intervals and partitions.** p. 219: “Define a *standard dyadic interval* in
--   $[0, 1]$ to be an interval of the form $\bigl[\frac{a}{2^n}, \frac{a+1}{2^n}\bigr]$, where $a$,
--   $n$ are nonnegative integers with $a \le 2^n - 1$.” It is stated as a relation between the two
--   endpoints, with the bound written $a + 1 \le 2^n$.
--
--   p. 220: “A partition $0 = x_0 < x_1 < x_2 < \cdots < x_n = 1$ of $[0, 1]$ determines intervals
--   $[x_{i-1}, x_i]$ for $i = 1, \dots, n$ which are called the *intervals of the partition*. A
--   partition of $[0,1]$ is called a *standard dyadic partition* if and only if the intervals of the
--   partition are standard dyadic intervals.” A standard dyadic partition is given here by its
--   increasing list of breakpoints, starting at $0$, ending at $1$, and with every consecutive pair
--   a standard dyadic interval. Since a standard dyadic interval has distinct endpoints, that
--   consecutive-pair condition already forces the list to increase.
--
--   **Tree diagrams.** p. 221: “Formally, a *tree diagram* is an ordered pair $(R, S)$ of
--   $\mathcal{T}$-trees such that $R$ and $S$ have the same number of leaves.” And p. 221: “The tree
--   $R$ is called the *domain tree* of the diagram, and $S$ is called the *range tree* of the
--   diagram.” The $\mathcal{T}$-trees are those of the imported tree type.
--
--   The element of $F$ a diagram represents has no single defining sentence; it is pieced together
--   from two passages of p. 221: “Suppose given $f \in F$. Lemma 2.2 shows that there exist standard
--   dyadic partitions $P$ and $Q$ such that $f$ is linear on the intervals of $P$ and maps them to
--   the intervals of $Q$. To $f$ is associated the tree diagram $(R, S)$, where $R$ is the
--   $\mathcal{T}$-tree corresponding to $P$ and $S$ is the $\mathcal{T}$-tree corresponding to $Q$.”
--   and “Furthermore, if $(R, S)$ is a tree diagram, then it is clear that there exists $f \in F$
--   such that $f$ is linear on every leaf of $R$ and $f$ maps the leaves of $R$ to the leaves of
--   $S$.” An element $f$ of $F$ is *the function of* a tree diagram when $f$ is affine on every
--   interval of the partition cut out by the domain tree and carries that partition's breakpoints,
--   in order, to those of the partition cut out by the range tree. Note that membership in $F$ does
--   not by itself make $f$ affine on the intervals of that partition: it provides only *some* finite
--   set of breakpoints off which $f$ is affine, and that set need not sit inside the domain tree's
--   marks. Nothing here asks the slopes to be powers of two; for these maps that is a consequence
--   rather than a hypothesis.
--
--   p. 221: “In the other direction, if there exists a positive integer $n$ such that the
--   $n^{\text{th}}$ and $(n + 1)^{\text{th}}$ leaves of $R$, respectively $S$, are the vertices of a
--   caret $C$, respectively $D$, then deleting all of $C$ and $D$ but the roots from $R$ and $S$
--   leads to a new tree diagram for $f$. If there do not exist such carets $C$, $D$ in $R$, $S$, then
--   the tree diagram $(R, S)$ is said to be *reduced*.” Here a tree diagram is reduced when there is
--   no position $k$ such that the $k$th and $(k+1)$th leaves are the two children of one vertex both
--   in the domain tree and in the range tree, leaves being counted from $0$, so that $k$ is the
--   source's $n - 1$.
--
--   **Generators.** p. 217: “Now define functions $X_0, X_1, X_2, \dots$ in $F$ so that $X_0 = A$
--   and $X_n = A^{-(n-1)} B A^{n-1}$ for $n \ge 1$.” In particular $X_1 = B$; $A$ and $B$ are the two
--   generators already constructed in the imported definition of $F$.
--
--   p. 224: “The functions in $F$ of the form $X_0^{b_0} X_1^{b_1} X_2^{b_2} \cdots X_n^{b_n}$ with
--   $b_k \ge 0$ for $k = 0, \dots, n$ will be called *positive*.”
--
--   p. 224, Corollary-Definition 2.7: “Every nontrivial element of $F$ can be expressed in unique
--   normal form
--   $X_0^{b_0} X_1^{b_1} X_2^{b_2} \cdots X_n^{b_n} X_n^{-a_n} \cdots X_2^{-a_2} X_1^{-a_1} X_0^{-a_0}$,
--   where $n, a_0, \dots, a_n, b_0, \dots, b_n$ are nonnegative integers such that i) exactly one
--   of $a_n$ and $b_n$ is nonzero and ii) if $a_k > 0$ and $b_k > 0$ for some integer $k$ with
--   $0 \le k < n$, then $a_{k+1} > 0$ or $b_{k+1} > 0$.” The bundle defines only the conditions on
--   this exponent data: two nonempty lists $a_0, \dots, a_n$ and $b_0, \dots, b_n$ of nonnegative
--   integers, of the same length, satisfying i) and ii).
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


