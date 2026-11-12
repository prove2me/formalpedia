-- Prove2me | Definitions.Def_RTStringIndex_Main_Leaves
-- name    : RTStringIndex_Main_Leaves
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:34.3018+00:00
-- url     : https://prove2.me/theorems/4937d8fe-ba7f-41f8-9ed7-5f7fdc65b796
-- title:
--   The leaf list $L_L$, representative lists $L_H$, blocks, and significant symbols
-- statement:
--   The centroid paths are listed in **preorder** $L_C$ of the centroid-path tree, children ordered lexicographically by their leaves. The leaf list $L_L$ lists the leaves group by group: the group of $g_1$, then that of $g_2$, and so on, where the group of a path $g$ is the leaves $l$ with $\mathrm{path}(l)=g$. Inside a group the order is arbitrary.
--
--   For a set $R=R(v)$, $H(v)=\{\mathrm{path}(x):x\in R\}$, and $g_R(v)$ is the path of $v$. A **representative list** $L_H$ contains one leaf $l_h\in R$ with $\mathrm{path}(l_h)=h$ for every $h\in H(v)\setminus\{g_R(v)\}$, and nothing else. The (inclusive) predecessor and successor of a leaf $l_q$ in $L_H$ are the largest leaf of $L_H$ not after $l_q$ and the smallest leaf of $L_H$ not before $l_q$ in $L_L$.
--
--   A **block** is a contiguous piece of $L_L$.
--
--   A symbol $a$ is **significant** in a node $u$ if at least a $1/\rho$ fraction of the leaves below $u$ are marked $a$. It is significant in a leaf $l$ if it is significant in $\mathrm{head}(h)$ for some ancestor-or-self $h$ of $\mathrm{path}(l)$. A leaf is significant if its mark is significant in it.
--
--   The parameters are $\tau=\log^5 n$ and $\rho=\log^2 n$, with $\log=\log_2$.
--
--   **Formalization Note** $L_L$ is any position function that is injective on the leaves and respects the grouping. Siblings in $L_C$ are compared by the lexicographic order of their tails, with $\$$ the largest symbol.
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), §6, pp. 13–15 (L_C, L_L, H(v), L_H, predecessor/successor, blocks, significant symbols); §2, p. 4 (τ = log⁵ n, ρ = log² n); p. 23 (log = log₂); PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_PST

set_option autoImplicit false

namespace RTStringIndex.Main

/-! # The leaf list `L_L`, representative lists `L_H` and significant symbols

Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), §6, p.13: "All centroid paths are
stored in pre-order in a list L_C: Children h_i of the same path h are ordered by the lexicographic
order of leaf(h_i). We maintain a list L_L containing all leaves of the PST … The list L_L is the
concatenation, for i = 1, …, s, of the groups of leaves l satisfying path(l) = g_i. Within each
group, the leaves may appear in an arbitrary order"; "The set L_H contains one representative leaf
l_h ∈ R with path(l_h) = h for every h ∈ H(v) \ {g_R(v)}, where g_R(v) is the centroid path of v.
We define the predecessor (resp. successor) of a leaf l_q in L_H as the largest (resp. smallest)
leaf in L_H that is smaller than or equal to l_q (resp. larger than or equal to l_q), with respect
to L_L"; §6, p.14: "The list L_L is divided into blocks"; §6, p.15: "A symbol a is significant in a
node u if at least a 1/ρ-fraction of the leaf descendants of u are marked with a. A symbol a is
significant in a leaf l if it is significant in head(h) for some path h that is an ancestor of
path(l) in the centroid-path tree, including path(l) itself. A leaf is significant if its marking
symbol is significant in it."

**Formalization Note.** `L_L` is a position function `pos` on the leaves, injective on them, that
lists the groups of leaves in the preorder `L_C`; every such list is allowed (the order inside a
group is arbitrary). Siblings in `L_C` are compared by the lexicographic order of their tails
(`List Chr` with `$ = ⊤` largest), which is the order of any leaves below them. A block is the set
of leaves whose positions lie in an interval. -/

open Classical

/-- `g` strictly precedes `g′` in the preorder `L_C` of the centroid-path tree. -/
def PathBefore (D : Finset CPath) (g g' : CPath) : Prop :=
  (PathAnc D g g' ∧ g ≠ g') ∨
  ∃ p c c', IsPathParent D p c ∧ IsPathParent D p c' ∧ c.2 < c'.2 ∧ PathAnc D c g ∧ PathAnc D c' g'

/-- `pos` lists the leaves of `S` as `L_L`: injective on the leaves, and grouped by `path(l)` in
the order `L_C`. -/
def IsLeafList (S : Finset (List Chr)) (Big : Set (List Chr)) (D : Finset CPath)
    (pos : List Chr → ℕ) : Prop :=
  Set.InjOn pos (S : Set (List Chr)) ∧
  ∀ l ∈ S, ∀ l' ∈ S, ∀ g g', IsPathOf Big D l g → IsPathOf Big D l' g' → PathBefore D g g' →
    pos l < pos l'

/-- `LH` is a representative list for `R` (`L_H`): one leaf of `R` for each path of
`H = {path(x) : x ∈ R}` other than `g_R`, and nothing else. -/
def IsRepList (Big : Set (List Chr)) (D : Finset CPath) (R : Finset (List Chr)) (gR : CPath)
    (LH : Finset (List Chr)) : Prop :=
  LH ⊆ R ∧ (∀ x ∈ LH, ¬ IsPathOf Big D x gR) ∧
  ∀ x ∈ R, ∀ h, IsPathOf Big D x h → h ≠ gR → ∃! y, y ∈ LH ∧ IsPathOf Big D y h

/-- `x` is the inclusive predecessor of `q` in `LH` with respect to `L_L`. -/
def IsPredIn (pos : List Chr → ℕ) (LH : Finset (List Chr)) (q x : List Chr) : Prop :=
  x ∈ LH ∧ pos x ≤ pos q ∧ ∀ y ∈ LH, pos y ≤ pos q → pos y ≤ pos x

/-- `x` is the inclusive successor of `q` in `LH` with respect to `L_L`. -/
def IsSuccIn (pos : List Chr → ℕ) (LH : Finset (List Chr)) (q x : List Chr) : Prop :=
  x ∈ LH ∧ pos q ≤ pos x ∧ ∀ y ∈ LH, pos q ≤ pos y → pos x ≤ pos y

/-- The symbol `a` is significant in the node `u`: at least a `1/ρ` fraction of the leaves below
`u` are marked with `a`. -/
def IsSignificantAt (S : Finset (List Chr)) (ρ : ℝ) (u : List Chr) (a : ℕ) : Prop :=
  (weight S u : ℝ) ≤ ρ * (markCount S u a : ℝ)

/-- The symbol `a` is significant in the leaf `l`: significant in `head(h)` for some ancestor-or-
self `h` of `path(l)` in the centroid-path tree. -/
def IsSignificantIn (S : Finset (List Chr)) (Big : Set (List Chr)) (D : Finset CPath) (ρ : ℝ)
    (l : List Chr) (a : ℕ) : Prop :=
  ∃ g h v, IsPathOf Big D l g ∧ PathAnc D h g ∧ IsHead S h v ∧ IsSignificantAt S ρ v a

/-- The block of `L_L` between the positions `lo` and `hi`. -/
noncomputable def block (S : Finset (List Chr)) (pos : List Chr → ℕ) (lo hi : ℕ) :
    Finset (List Chr) :=
  S.filter (fun l => lo ≤ pos l ∧ pos l ≤ hi)

/-- The letters of `T` that mark a significant leaf of the block `B`. -/
noncomputable def sigSymbols (T : List ℕ) (Big : Set (List Chr)) (D : Finset CPath) (ρ : ℝ)
    (B : Finset (List Chr)) : Finset ℕ :=
  T.toFinset.filter (fun a => ∃ l ∈ B, IsMarked (sufSet T) l a ∧
    IsSignificantIn (sufSet T) Big D ρ l a)

/-- The threshold `τ = log⁵ n` (p.4; `log = log₂`, p.23). -/
noncomputable def tauPar (n : ℕ) : ℝ := Real.logb 2 n ^ 5

/-- The significance parameter `ρ = log² n` (p.4). -/
noncomputable def rhoPar (n : ℕ) : ℝ := Real.logb 2 n ^ 2

end RTStringIndex.Main


