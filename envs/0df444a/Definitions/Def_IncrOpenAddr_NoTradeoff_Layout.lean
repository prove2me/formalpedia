-- Prove2me | Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
-- name    : IncrOpenAddr_NoTradeoff_Layout
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:34:43.681168+00:00
-- url     : https://prove2.me/theorems/d76d7b8d-53df-4d1d-872a-45140e754727
-- title:
--   The forest of perfect binary trees (App. A.1), the epoch schedule (1), phases, local lists and probe schedule (App. A.2), and the search bound (Definition 2.3)
-- statement:
--   **Forest layout.** For a table of $n\ge 8$ slots write $n=2^L+m$ with $L=\lfloor\log_2 n\rfloor$, $0\le m<2^L$. The array is split into trees $T_1,\dots,T_\alpha$: one tree of each size $2^{L-1},\dots,8,4$, a second tree of size $4$, one more tree of size $2^b$ for each set bit $b\ge2$ of $m$, in non-increasing order of size, and a final single-node tree of $n \bmod 4$ slots if $4\nmid n$. A tree of $2^{h+1}$ slots has **height** $h$ (the small node has height $1$) and $2^{h-1}$ leaves. Levels are counted from the leaves (level $1$) to the root (level $h$); $T_i[j,k]$ is the $k$-th node (from $0$) at level $j$, and its children are $T_i[j-1,2k]$, $T_i[j-1,2k+1]$. Each tree occupies a contiguous block of the array as an implicit heap: node $[j,k]$ has heap index $p=2^{h-j}+k$, the root ($p=1$) covers the first four slots of its tree, node $p\ge2$ the slots at offsets $2p,2p+1$. The level-$j$ ancestor of leaf $\ell$ is $T_i[j,\lfloor \ell/2^{j-1}\rfloor]$, and its subtree is the level-$j$ **home subtree**.
--
--   **Schedule (1).** With a constant $\eta>0$: $t_0=0$, $t_i=\sum_{r<i}|T_r|+\lfloor(1-\eta)|T_i|\rfloor$ for $i<\alpha$, $t_\alpha=n$; insertion number $c+1$ belongs to **epoch** $i$ when $t_{i-1}\le c<t_i$. In epoch $i\ge2$, after $r=c-t_{i-1}$ insertions of the epoch, with $h$ the height of $T_{i-1}$, the insertion is in the **final phase** $h+1$ if $5r\ge|T_{i-1}|$, and in phase $\min\{h+1,\lfloor|T_{i-1}|/(|T_{i-1}|-5r)\rfloor\}$ otherwise. `phaseLength i j` counts the insertions of epoch $i$ in phase $j$; `phaseEnd i j` is the number of insertions performed when phase $j$ of epoch $i$ ends.
--
--   **Local lists and the probe schedule.** For an element with home leaf $\ell$ in $T_i$, the **local list** of $T_i$ alternates the ancestor list (the leaf, then its ancestors up to the root) with the expanding-subtree list (the level-$1$, level-$2$, …, level-$h$ home subtrees, each in breadth-first order), four probes per node (a node with fewer than four slots rereads its first slot). The **merged schedule**: in round $r=0,1,\dots$, for $a=0,\dots,r$ in turn, visit $T_{2^a},\dots,T_{2^{a+1}-1}$ in order, reading the first $2^{\lfloor(r-a)/2\rfloor}$ probes of each local list (all of it if shorter); a visit to $T_i$ with $i>\alpha$ is that many probes of a fixed address. `scheduleEvents` lists the probes of the first $R$ rounds as events "$k$-th probe of $T_i$'s local list".
--
--   **Search bound (Definition 2.3).** For an element $u$ in node $U$ of $T_i$ with home leaf $\ell=L_i(u)$: $q(u)=D\,i\,j^2$ if $U$ is the level-$j$ ancestor of $\ell$, and otherwise $q(u)=D\,i\,4^h$ with $h$ the smallest level such that $U$ lies in the level-$h$ home subtree.
--
--   **Formalization Note.** Trees are numbered from $1$, array addresses from $0$; a node is a triple (tree, level, index) with validity predicate `Node.Valid`.
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 7–9 (PDF 8–10), §2.1 and (1); p. 10–11 (PDF 11–12), §2.2 and Definition 2.3; p. 34–35 (PDF 35–36), App. A.1–A.2

import Mathlib

set_option autoImplicit false

/-!
# The forest layout, the schedule, the probe schedule and the search bound

Farach-Colton, Krapivin, Kuszmaul, arXiv:2611.04186 (manuscript sha256 9486c2b8…):
§2.1 (p. 7–9, PDF 8–10), the forest of perfect binary trees, the epoch boundaries (1) and the
phases; App. A.1 (p. 34–35, PDF 35–36), the tree sizes and heap addresses for arbitrary `n ≥ 8`;
§2.2 and App. A.2 (p. 10, 35, PDF 11, 36), the local lists and their merge; Definition 2.3
(p. 11, PDF 12), the search bound.

Conventions.
* Trees are numbered `i = 1, …, α` (`α = numTrees n`), as in the paper.  Levels are counted from
  the leaves (level 1) to the root (level `height n i`); `⟨i, j, k⟩` is the paper's `T_i[j, k]`,
  the `k`-th node (from `0`, left to right) at level `j` of `T_i`.
* Array addresses are natural numbers `0, …, n - 1`.
* A leaf of `T_i` is identified with its index `ℓ < numLeaves n i`; the level-`j` ancestor of
  leaf `ℓ` is `⟨i, j, ℓ / 2^(j-1)⟩`.
-/

namespace IncrOpenAddr.NoTradeoff

/-- The tree sizes of App. A.1, in layout order: write `n = 2^L + m` with `L = ⌊log₂ n⌋`; one tree
of each size `2^(L-1), …, 8, 4`, a second tree of size `4`, one more tree of size `2^b` for each
set bit `b ≥ 2` of `m`, sorted by non-increasing size, and a final single-node tree of `n mod 4`
slots if `n` is not a multiple of four. -/
def treeSizes (n : ℕ) : List ℕ :=
  let L := Nat.log 2 n
  let m := n - 2 ^ L
  ((List.range (L - 2)).flatMap fun t =>
      let b := L - 1 - t
      List.replicate (1 + (if m.testBit b then 1 else 0) + (if b = 2 then 1 else 0)) (2 ^ b)) ++
    (if n % 4 = 0 then [] else [n % 4])

/-- `α`, the number of trees. -/
def numTrees (n : ℕ) : ℕ := (treeSizes n).length

/-- `|T_i|`, the number of slots of tree `i` (`1 ≤ i ≤ α`; `0` otherwise). -/
def treeSize (n i : ℕ) : ℕ := if i = 0 then 0 else (treeSizes n).getD (i - 1) 0

/-- The array offset of tree `i`: `Σ_{r < i} |T_r|`. -/
def treeOffset (n i : ℕ) : ℕ := ((treeSizes n).take (i - 1)).sum

/-- The height of tree `i`: a tree of `2^(h+1)` slots has height `h`; the final small node has
height `1`. -/
def height (n i : ℕ) : ℕ := if 4 ≤ treeSize n i then Nat.log 2 (treeSize n i) - 1 else 1

/-- The number of leaves of tree `i`. -/
def numLeaves (n i : ℕ) : ℕ := 2 ^ (height n i - 1)

/-- A node `T_i[j, k]`. -/
structure Node where
  tree : ℕ
  level : ℕ
  idx : ℕ
  deriving DecidableEq, Repr

/-- `v` is a node of the layout for `n`. -/
def Node.Valid (n : ℕ) (v : Node) : Prop :=
  1 ≤ v.tree ∧ v.tree ≤ numTrees n ∧ 1 ≤ v.level ∧ v.level ≤ height n v.tree ∧
    v.idx < 2 ^ (height n v.tree - v.level)

/-- The array addresses covered by node `v` (App. A.1 heap layout): node `[j, k]` has heap index
`p = 2^(h - j) + k`; the root (`p = 1`) covers the first four slots of its tree (all slots of the
final small node), node `p ≥ 2` the slots at offsets `2p, 2p + 1`. -/
def slots (n : ℕ) (v : Node) : List ℕ :=
  let o := treeOffset n v.tree
  let p := 2 ^ (height n v.tree - v.level) + v.idx
  if p = 1 then (List.range (min 4 (treeSize n v.tree))).map (o + ·) else [o + 2 * p, o + 2 * p + 1]

/-- The level-`j` ancestor in tree `i` of leaf `ℓ`. -/
def ancestor (i ℓ j : ℕ) : Node := ⟨i, j, ℓ / 2 ^ (j - 1)⟩

/-- `u` lies in the subtree of `v`. -/
def InSubtree (u v : Node) : Prop :=
  u.tree = v.tree ∧ u.level ≤ v.level ∧ u.idx / 2 ^ (v.level - u.level) = v.idx

instance (u v : Node) : Decidable (InSubtree u v) := by unfold InSubtree; infer_instance

/-- The nodes of the subtree of `v`, from level `v.level` down to level `lo`. -/
def subtreeNodesFrom (lo : ℕ) (v : Node) : List Node :=
  (List.range (v.level + 1 - lo)).flatMap fun d =>
    (List.range (2 ^ d)).map fun t => (⟨v.tree, v.level - d, 2 ^ d * v.idx + t⟩ : Node)

/-- All nodes of the subtree of `v`, in breadth-first order. -/
def subtreeNodes (v : Node) : List Node := subtreeNodesFrom 1 v

/-- All nodes of the layout. -/
def allNodes (n : ℕ) : List Node :=
  (List.range (numTrees n)).flatMap fun t =>
    subtreeNodes ⟨t + 1, height n (t + 1), 0⟩

/-! ## The schedule (1) and the phases -/

/-- The epoch boundaries (1): `t_0 = 0`, `t_i = Σ_{r<i} |T_r| + ⌊(1 - η)|T_i|⌋` for `i < α`,
`t_α = n` (and `n` beyond). -/
noncomputable def epochEnd (n : ℕ) (η : ℝ) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if numTrees n ≤ i then n
  else treeOffset n i + ⌊(1 - η) * (treeSize n i : ℝ)⌋₊

/-- The epoch of the insertion made when `c` elements are present (insertion `c + 1`): the
least `i ≥ 1` with `c < t_i`. -/
noncomputable def epochOf (n : ℕ) (η : ℝ) (c : ℕ) : ℕ := by
  classical
  exact ((List.range (numTrees n)).map (· + 1)).find? (fun i => decide (c < epochEnd n η i))
    |>.getD (numTrees n)

/-- The phase of the insertion made when `c` elements are present, in an epoch `i ≥ 2`: with
`r = c - t_{i-1}` insertions already made in the epoch and `h` the height of `T_{i-1}`, it is the
final phase `h + 1` if `5r ≥ |T_{i-1}|`, and `min {h + 1, ⌊|T_{i-1}| / (|T_{i-1}| - 5r)⌋}`
otherwise.  Phase `0` stands for epoch one, which has no phases. -/
noncomputable def phaseOf (n : ℕ) (η : ℝ) (c : ℕ) : ℕ :=
  let i := epochOf n η c
  if i ≤ 1 then 0 else
    let T := treeSize n (i - 1)
    let h := height n (i - 1)
    let r := c - epochEnd n η (i - 1)
    if T ≤ 5 * r then h + 1 else min (h + 1) (T / (T - 5 * r))

/-- The number of insertions of epoch `i` that belong to phase `j`. -/
noncomputable def phaseLength (n : ℕ) (η : ℝ) (i j : ℕ) : ℕ :=
  ((List.range (epochEnd n η i - epochEnd n η (i - 1))).filter
    (fun r => phaseOf n η (epochEnd n η (i - 1) + r) = j)).length

/-- The number of insertions performed when phase `j` of epoch `i` ends:
`t_{i-1}` plus the insertions of epoch `i` in phases `≤ j`. -/
noncomputable def phaseEnd (n : ℕ) (η : ℝ) (i j : ℕ) : ℕ :=
  epochEnd n η (i - 1) + ((List.range (epochEnd n η i - epochEnd n η (i - 1))).filter
    (fun r => phaseOf n η (epochEnd n η (i - 1) + r) ≤ j)).length

/-! ## The local lists and the probe schedule (§2.2, App. A.2) -/

/-- Interleave two lists, `a₁ b₁ a₂ b₂ …`, then the rest of the longer one. -/
def interleave {α : Type} : List α → List α → List α
  | [], bs => bs
  | a :: as, bs => match bs with
    | [] => a :: as
    | b :: bs' => a :: b :: interleave as bs'

/-- The four probes spent on a node: its slots, then its first slot again until four. -/
def nodeProbes (n : ℕ) (v : Node) : List ℕ :=
  let s := slots n v
  s ++ List.replicate (4 - s.length) (s.headD 0)

/-- The local list of tree `i` for an element with home leaf `ℓ` (array addresses): the ancestor
list (leaf `ℓ`, then its ancestors up to the root) alternated with the expanding-subtree list
(the level-1 home subtree, the level-2 home subtree, …, the whole tree, each in breadth-first
order), four probes per node read. -/
def localList (n i ℓ : ℕ) : List ℕ :=
  let h := height n i
  let anc := (List.range h).map fun d => ancestor i ℓ (d + 1)
  let exp := (List.range h).flatMap fun d => subtreeNodes (ancestor i ℓ (d + 1))
  (interleave anc exp).flatMap (nodeProbes n)

/-- The probe events of round `r` of the merged schedule (App. A.2): for `a = 0, …, r` in turn,
visit the trees `T_{2^a}, …, T_{2^(a+1) - 1}` in order, reading the first `2^⌊(r-a)/2⌋` probes of
each one's local list (all of it if it is shorter).  The event `some (i, k)` is the `k`-th probe
(`k ≥ 1`) of `T_i`'s local list; `none` is a probe of the fixed address spent on a tree `i > α`.
`len i` is the length of `T_i`'s local list. -/
def roundEvents (α : ℕ) (len : ℕ → ℕ) (r : ℕ) : List (Option (ℕ × ℕ)) :=
  (List.range (r + 1)).flatMap fun a =>
    (List.range (2 ^ a)).flatMap fun t =>
      let i := 2 ^ a + t
      let cnt := 2 ^ ((r - a) / 2)
      if i ≤ α then (List.range (min cnt (len i))).map (fun k => some (i, k + 1))
      else List.replicate cnt none

/-- The first `R` rounds of the merged probe schedule of an element whose home leaf in `T_i` is
`leaf i` (a query probe sequence, as events). -/
def scheduleEvents (n : ℕ) (leaf : ℕ → ℕ) (R : ℕ) : List (Option (ℕ × ℕ)) :=
  (List.range R).flatMap (roundEvents (numTrees n) (fun i => (localList n i (leaf i)).length))

/-! ## The search bound (Definition 2.3) -/

/-- The smallest `h ≥ U.level` such that node `U` lies in the level-`h` home subtree of leaf `ℓ`
(the height of the tree if there is none, which happens only for nodes outside the tree). -/
def homeLevel (n ℓ : ℕ) (U : Node) : ℕ :=
  ((List.range (height n U.tree + 1 - U.level)).map (U.level + ·)).find?
    (fun h => decide (U.idx / 2 ^ (h - U.level) = ℓ / 2 ^ (h - 1))) |>.getD (height n U.tree)

/-- The search bound `q(u)` of Definition 2.3, for an element in tree `T_i` (`i = U.tree`), in
node `U`, with home leaf `ℓ = L_i(u)`: `D·i·j²` if `U` is the level-`j` ancestor of `u`, else
`D·i·4^h` with `h` the smallest level of a home subtree of `u` containing `U`. -/
def searchBound (n D ℓ : ℕ) (U : Node) : ℕ :=
  let h := homeLevel n ℓ U
  if h = U.level then D * U.tree * U.level ^ 2 else D * U.tree * 4 ^ h

end IncrOpenAddr.NoTradeoff


