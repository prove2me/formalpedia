-- Prove2me | Definitions.Def_RTStringIndex_Main_PST
-- name    : RTStringIndex_Main_PST
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:26.759265+00:00
-- url     : https://prove2.me/theorems/9ec70e5a-d9ba-4d55-9b0f-852ba0a16d3e
-- title:
--   The path-decomposed suffix tree: big/small nodes, centroid paths, and w-links
-- statement:
--   Fix a threshold $\tau$. A **big/small partition** of the suffix-tree nodes makes every node of weight at least $2\tau$ big, every node of weight at most $\tau$ small, and every ancestor of a big node big.
--
--   A **level-$i$ centroid path** runs from a node $u$ up to its ancestor $v$ with
--   $$\mathrm{weight}(u)\ge 2^i\tau,\qquad \mathrm{weight}(v)\le (2^{i+1}+2^{i-2})\tau,$$
--   and the parent of $v$ lies on a path of level at least $i+1$. A **centroid decomposition** assigns every big node to exactly one path. A path $h$ owns the edge from $\mathrm{parent}(\mathrm{head}(h))$ to $\mathrm{head}(h)$. The parent of $h$ in the **centroid-path tree** is the path containing $\mathrm{parent}(\mathrm{head}(h))$, and $\mathrm{label}(h)$ is the string read from $\mathrm{parent}(\mathrm{head}(h))$ down to $\mathrm{tail}(h)$.
--
--   For a location $x$, $w_x$ is its lowest big ancestor-or-self, and $\mathrm{path}(x)$ is the path containing $w_x$.
--
--   For a path $h$ and a string $s$, $\mathrm{wlink}(h,s)$ is the deepest path $h'$ in the centroid-path tree such that some node $u\in h$ has a generalized Weiner link labelled $s$ to a location $\nu\in h'$, i.e. $\mathrm{label}(\nu)=s\cdot\mathrm{label}(u)$. It is $\mathrm{NULL}$ if no such $h'$ exists.
--
--   These definitions are the data structure of Sections 3–7 and 11; every lemma about it holds for every admissible state.
--
--   **Formalization Note** A path is stored as the pair (parent of its head, its tail), with no top for the root path; its locations are those strictly below the top and at or above the tail. $2^{i-2}$ is a real power.
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), §3, p. 5 (big/small nodes, level-i centroid paths, centroid-path tree); Fig. 3, p. 6; §4, p. 7 (label(h)); §5, p. 8 (generalized Weiner links, wlink); §6, p. 13 (path(l)); §10, p. 24 (w_x); PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_SuffixTree

set_option autoImplicit false

namespace RTStringIndex.Main

/-! # The path-decomposed suffix tree: big and small nodes, centroid paths and w-links

Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), §3, p.5: "A PST node with at least
2τ leaf descendants is always big, and a node with at most τ leaf descendants is always small …
all ancestors of a big node are big … A level-i centroid path, for i ≥ 0, is a path between a node
u and its ancestor v such that: (i) weight(u) ≥ 2^i τ and weight(v) ≤ (2^{i+1} + 2^{i−2})τ; (ii) the
parent of v is on a level-j centroid path for j ≥ i + 1. Every node of the big subtree is assigned
to exactly one centroid path … the parent of a path h is the path that contains parent(head(h))";
Fig. 3, p.6: "every edge of the big subtree belongs to some centroid path, and the edge from
parent(head(h)) to head(h) belongs to h"; §5, p.8: "For a centroid path h and a nonempty string s,
we define wlink(h, s) to be the lowest centroid path h′ such that there is a Weiner link labeled
with s from some node u ∈ h to a location ν ∈ h′. Here, lowest means deepest in the centroid-path
tree. If no such path exists, we set wlink(h, s) = NULL"; p.8: "there is a Weiner link from a node
u to a location ν labeled with a string s … iff label(ν) = s · label(u)"; §6, p.13: `path(l)`,
`w_l`; §10, p.24: "let w_x = x if x is big, and … the lowest big ancestor of x otherwise".

**Formalization Note.** The big/small partition and the centroid decomposition are not unique;
every statement quantifies over **all** of them satisfying the conditions of p.5. A centroid path
`h` is the pair `(top, tail)`: `tail` is its lowest node, `top = some p` with `p = parent(head(h))`,
or `top = none` for the path through the root. The locations of `h` are those strictly below `top`
and at or above `tail`, so the edge into `head(h)` belongs to `h` (Fig. 3); its nodes are the
explicit nodes among them. Levels are a function `lev`; `2^{i−2}` is a real power with integer
exponent. "Lowest" for paths is maximal depth in the centroid-path tree. `wlinkNull` is
`wlink(h, s) = NULL`; `IsWLinkTarget h s h′` is `wlink(h, s) = h′`. -/

open Classical

/-- A centroid path, as `(top, tail)`: `top = parent(head)` (`none` for the root path). -/
abbrev CPath := Option (List Chr) × List Chr

/-- The string depth of `parent(head(h))` (`0` for the root path, as in §10, p.24). -/
def topDepth (h : CPath) : ℕ := (h.1.map List.length).getD 0

/-- The location `ν` lies on the centroid path `h`. -/
def InPath (h : CPath) (ν : List Chr) : Prop :=
  (match h.1 with
    | none => True
    | some p => p <+: ν ∧ p ≠ ν) ∧ ν <+: h.2

/-- `v = head(h)`: the highest explicit node on `h`. -/
def IsHead (S : Finset (List Chr)) (h : CPath) (v : List Chr) : Prop :=
  IsNode S v ∧ InPath h v ∧ ∀ w, IsNode S w → InPath h w → v <+: w

/-- `label(h)`: the concatenation of the edge labels of `h`, from `parent(head(h))` to
`tail(h)`. -/
def pathLabel (h : CPath) : List Chr := h.2.drop (topDepth h)

/-- The big/small partition of p.5 with threshold `τ`. -/
def IsBigSmall (S : Finset (List Chr)) (τ : ℝ) (Big : Set (List Chr)) : Prop :=
  (∀ x ∈ Big, IsNode S x) ∧
  (∀ x, IsNode S x → 2 * τ ≤ (weight S x : ℝ) → x ∈ Big) ∧
  (∀ x, IsNode S x → (weight S x : ℝ) ≤ τ → x ∉ Big) ∧
  (∀ x ∈ Big, ∀ y, IsNode S y → y <+: x → y ∈ Big)

/-- The centroid path decomposition of the big subtree (p.5), with levels `lev`. -/
def IsCentroidDecomp (S : Finset (List Chr)) (τ : ℝ) (Big : Set (List Chr))
    (D : Finset CPath) (lev : CPath → ℕ) : Prop :=
  (∀ h ∈ D, h.2 ∈ Big) ∧
  (∀ h ∈ D, ∀ p, h.1 = some p → p ∈ Big ∧ p <+: h.2 ∧ p ≠ h.2) ∧
  (∀ h ∈ D, ∀ x, IsNode S x → InPath h x → x ∈ Big) ∧
  (∀ x ∈ Big, ∃! h, h ∈ D ∧ InPath h x) ∧
  (∀ h ∈ D, (2 : ℝ) ^ lev h * τ ≤ (weight S h.2 : ℝ)) ∧
  (∀ h ∈ D, ∀ v, IsHead S h v →
    (weight S v : ℝ) ≤ ((2 : ℝ) ^ (lev h + 1) + (2 : ℝ) ^ ((lev h : ℤ) - 2)) * τ) ∧
  (∀ h ∈ D, ∀ p, h.1 = some p → ∀ g ∈ D, InPath g p → lev h + 1 ≤ lev g)

/-- An admissible PST state: a big/small partition with threshold `τ` and a centroid path
decomposition of its big subtree. -/
def Admissible (S : Finset (List Chr)) (τ : ℝ) (Big : Set (List Chr)) (D : Finset CPath)
    (lev : CPath → ℕ) : Prop :=
  IsBigSmall S τ Big ∧ IsCentroidDecomp S τ Big D lev

/-- The location `ν` lies in the big subtree (on some centroid path). -/
def InBigSubtree (D : Finset CPath) (ν : List Chr) : Prop := ∃ h ∈ D, InPath h ν

/-- `w` is the lowest big ancestor-or-self of the location `x` (`w_x`, §10). -/
def IsLowestBigAnc (Big : Set (List Chr)) (x w : List Chr) : Prop :=
  w ∈ Big ∧ w <+: x ∧ ∀ w', w' ∈ Big → w' <+: x → w'.length ≤ w.length

/-- `h = path(x)`: the centroid path containing `w_x`. -/
def IsPathOf (Big : Set (List Chr)) (D : Finset CPath) (x : List Chr) (h : CPath) : Prop :=
  h ∈ D ∧ ∃ w, IsLowestBigAnc Big x w ∧ InPath h w

/-- `g` is the parent of `c` in the centroid-path tree: `g` contains `parent(head(c))`. -/
def IsPathParent (D : Finset CPath) (g c : CPath) : Prop :=
  g ∈ D ∧ c ∈ D ∧ ∃ p, c.1 = some p ∧ InPath g p

/-- `g` is an ancestor of `c` in the centroid-path tree, or `g = c`. -/
def PathAnc (D : Finset CPath) (g c : CPath) : Prop :=
  Relation.ReflTransGen (IsPathParent D) g c

/-- The depth of `h` in the centroid-path tree: its number of proper ancestors. -/
noncomputable def pathDepth (D : Finset CPath) (h : CPath) : ℕ :=
  (D.filter (fun g => PathAnc D g h ∧ g ≠ h)).card

/-- `h` is a leaf of the centroid-path tree. -/
def IsLeafPath (D : Finset CPath) (h : CPath) : Prop := h ∈ D ∧ ∀ c, ¬ IsPathParent D h c

/-- `g` is the lowest common ancestor of `g₁` and `g₂` in the centroid-path tree. -/
def IsPathLCA (D : Finset CPath) (g₁ g₂ g : CPath) : Prop :=
  PathAnc D g g₁ ∧ PathAnc D g g₂ ∧ ∀ g', PathAnc D g' g₁ → PathAnc D g' g₂ → PathAnc D g' g

/-- `h′` is a candidate for `wlink(h, s)`: some node `u ∈ h` has a (generalized) Weiner link
labelled `s` to a location `ν = s · label(u)` on `h′`. -/
def IsWCand (S : Finset (List Chr)) (D : Finset CPath) (h : CPath) (s : List Chr)
    (h' : CPath) : Prop :=
  h ∈ D ∧ h' ∈ D ∧ ∃ u, IsNode S u ∧ InPath h u ∧ IsLoc S (s ++ u) ∧ InPath h' (s ++ u)

/-- `wlink(h, s) = h′`: the deepest candidate in the centroid-path tree. -/
def IsWLinkTarget (S : Finset (List Chr)) (D : Finset CPath) (h : CPath) (s : List Chr)
    (h' : CPath) : Prop :=
  IsWCand S D h s h' ∧ ∀ g, IsWCand S D h s g → pathDepth D g ≤ pathDepth D h'

/-- `wlink(h, s) = NULL`: there is no candidate. -/
def wlinkNull (S : Finset (List Chr)) (D : Finset CPath) (h : CPath) (s : List Chr) : Prop :=
  ∀ h', ¬ IsWCand S D h s h'

/-- `ν` is the lowest location of the big subtree whose label is a prefix of `x`. -/
def IsLowestBigMatch (D : Finset CPath) (x ν : List Chr) : Prop :=
  ν <+: x ∧ InBigSubtree D ν ∧ ∀ μ, μ <+: x → InBigSubtree D μ → μ.length ≤ ν.length

/-- `u` is the root of a small subtree: a small node whose parent is big. -/
def IsSmallRoot (S : Finset (List Chr)) (Big : Set (List Chr)) (u : List Chr) : Prop :=
  IsNode S u ∧ u ∉ Big ∧ ∃ p, IsParent S p u ∧ p ∈ Big

end RTStringIndex.Main


