-- Prove2me | Definitions.Def_LogStarBinPacking_AdmissibleTreeData
-- name    : LogStarBinPacking_AdmissibleTreeData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:36.829997+00:00
-- url     : https://prove2.me/theorems/37382b03-48d0-4a01-9fa5-464abb9c183a
-- title:
--   $d$-admissible trees, their marked copies and the integers $p_\ell$, $D_*$, $S_d$
-- statement:
--   Fix an integer $d\ge1$. A **$d$-admissible tree** is a finite rooted tree $T^\circ$ with disjoint red and blue markings (a marking is a set of non-root vertices) such that:
--
--   1. all leaves have depth $L\ge1$, and every root-to-leaf path has exactly $2d-1$ marked vertices;
--   2. each depth $1\le\ell\le L$ has the same positive number $p_\ell$ of red and of blue vertices;
--   3. retaining the root-to-leaf paths with at least $d$ red (respectively blue) vertices gives copies $T^+$ (respectively $T^-$), both nonempty, with retained red and blue vertices $\mathcal M^+$, $\mathcal M^-$; they satisfy $|\mathcal M^\sigma\cap V_\ell(T^\sigma)|\le p_\ell$ and $|\mathcal M^\sigma\cap\pi|\ge d$ for every root-to-leaf path $\pi$ of $T^\sigma$;
--   4. any markings $\mathcal A^+,\mathcal A^-$ of $T^+,T^-$ with
--   $$
--   |\mathcal A^+\cap V_\ell(T^+)|+|\mathcal A^-\cap V_\ell(T^-)|\le p_\ell\qquad(1\le\ell\le L)
--   $$
--   leave some root-to-leaf path of $T^+$ or of $T^-$ unhit.
--
--   Put $P=\sum_{\ell=1}^Lp_\ell$, $H=|V(T^+)|+|V(T^-)|$, and let $D_*\ge1$ bound every vertex's number of children in either copy. The record holds the tree, its markings, both copies and their marks, $L$, $(p_1,\dots,p_L)$, $D_*$ and $S_d$, together with its binary encoding.
--
--   These trees are the competing trees of [OAI26]; their size governs the size of the whole construction (Lemma 3.2).
--
--   **Formalization Note** A rooted tree with all leaves at depth $L$ is the set of its leaf addresses (lists of natural numbers of length $L$); its vertices are their prefixes, the root is the empty address. A copy is labelled by the original addresses.
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), §3.1, Admissible trees, p.13; Lemma 3.2, p.13

import Mathlib
import Definitions.Def_BinPackingGap

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- The vertex set of the finite rooted tree whose leaves have the addresses `leaves`: every
prefix of a leaf address; the root is the empty address `[]`, and the depth of a vertex is the
length of its address. -/
def treeVertices (leaves : Finset (List ℕ)) : Finset (List ℕ) :=
  leaves.biUnion fun l => (Finset.range (l.length + 1)).image l.take

/-- The vertex set of the root-to-leaf path ending at the leaf `l`. -/
def rootPath (l : List ℕ) : Finset (List ℕ) := (Finset.range (l.length + 1)).image l.take

/-- The vertices of `S` at distance `ℓ` from the root. -/
def atDepth (S : Finset (List ℕ)) (ℓ : ℕ) : Finset (List ℕ) := S.filter fun w => w.length = ℓ

/-- The children of the vertex `w` in the tree with vertex set `Vs`. -/
def children (Vs : Finset (List ℕ)) (w : List ℕ) : Finset (List ℕ) :=
  Vs.filter fun u => u.length = w.length + 1 ∧ w <+: u

/-- **The output of Lemma 3.2: a `d`-admissible tree, its marked copies and the integers
`p₁, …, p_L, D∗, S_d`.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items
per Bin*, manuscript (sha256 1d88425d…), §3.1, "Admissible trees", p.13, and Lemma 3.2, p.13.

The definition on p.13: fix an integer `d ≥ 1`. A `d`-admissible tree is a finite rooted tree
`T◦` with disjoint red and blue markings (a marking is a subset of `V(T) ∖ {r(T)}`) such that all
leaves have depth `L ≥ 1`, every root-to-leaf path has exactly `2d − 1` marked vertices, and each
depth `1 ≤ ℓ ≤ L` has the same positive number `p_ℓ` of red and blue vertices. In separate copies,
retain the union of root-to-leaf paths with at least `d` red (respectively, blue) vertices to obtain
`T⁺` (respectively, `T⁻`), without contracting edges; both copies must be nonempty. `M⁺` and `M⁻`
are the retained red and blue vertices. Both copies have leaf depth `L`, and for `σ ∈ {+, −}`,
`|M^σ ∩ V_ℓ(T^σ)| ≤ p_ℓ` (`1 ≤ ℓ ≤ L`) and `|M^σ ∩ π| ≥ d` (`π ∈ Π(T^σ)`). Finally, any markings
`A⁺, A⁻` of `T⁺, T⁻` with `|A⁺ ∩ V_ℓ(T⁺)| + |A⁻ ∩ V_ℓ(T⁻)| ≤ p_ℓ` (`1 ≤ ℓ ≤ L`) must leave a path
unhit: `A^σ ∩ π = ∅` for some `σ` and `π ∈ Π(T^σ)`. `P = ∑ p_ℓ`, `H = |V(T⁺)| + |V(T⁻)|`, and
`D∗ ≥ 1` is an integer upper bound on every vertex's number of children in either copy.

**Formalization Note** A finite rooted tree with all leaves at depth `L` is given by the finite set
of its leaf addresses (lists of natural numbers of length `L`); its vertices are the prefixes of the
leaves, the root is `[]`. The record lists, as lists of addresses, the leaves of `T◦`, the red and
blue vertices, the leaves of `T⁺` and `T⁻`, the marks `M⁺` and `M⁻`; then `L`, the list
`[p₁, …, p_L]`, `D∗` and `S_d`. A copy is labelled by the original addresses (the paper's
`(σ, v) ↦ v`), so `T⁺` is the tree on the retained leaves of `T◦`. -/
structure AdmissibleTreeData where
  leaves : List (List ℕ)
  red : List (List ℕ)
  blue : List (List ℕ)
  plusLeaves : List (List ℕ)
  minusLeaves : List (List ℕ)
  plusMarks : List (List ℕ)
  minusMarks : List (List ℕ)
  depth : ℕ
  quotas : List ℕ
  branchBound : ℕ
  sizeBound : ℕ

namespace AdmissibleTreeData

/-- `p_ℓ`, the `ℓ`-th entry of `[p₁, …, p_L]` (`1 ≤ ℓ ≤ L`). -/
def quota (o : AdmissibleTreeData) (ℓ : ℕ) : ℕ := o.quotas.getD (ℓ - 1) 0

/-- `P = ∑_{ℓ=1}^{L} p_ℓ`. -/
def P (o : AdmissibleTreeData) : ℕ := o.quotas.sum

/-- `H = |V(T⁺)| + |V(T⁻)|`. -/
def H (o : AdmissibleTreeData) : ℕ :=
  (treeVertices o.plusLeaves.toFinset).card + (treeVertices o.minusLeaves.toFinset).card

/-- The record is a `d`-admissible tree `T◦` with its marked copies `T⁺, T⁻`, markings `M⁺, M⁻`,
the integers `p_ℓ` and an integer `D∗ ≥ 1` bounding all child counts in the copies (p.13). -/
def IsAdmissible (d : ℕ) (o : AdmissibleTreeData) : Prop :=
  let T := o.leaves.toFinset
  let R := o.red.toFinset
  let Bl := o.blue.toFinset
  let L := o.depth
  let Tp := o.plusLeaves.toFinset
  let Tm := o.minusLeaves.toFinset
  let Mp := o.plusMarks.toFinset
  let Mm := o.minusMarks.toFinset
  -- all leaves have depth `L ≥ 1`
  1 ≤ L ∧ T.Nonempty ∧ (∀ l ∈ T, l.length = L) ∧
  -- disjoint red and blue markings
  R ⊆ (treeVertices T).erase [] ∧ Bl ⊆ (treeVertices T).erase [] ∧ Disjoint R Bl ∧
  -- every root-to-leaf path has exactly `2d − 1` marked vertices
  (∀ l ∈ T, ((R ∪ Bl) ∩ rootPath l).card = 2 * d - 1) ∧
  -- each depth `1 ≤ ℓ ≤ L` has `p_ℓ > 0` red and `p_ℓ` blue vertices
  o.quotas.length = L ∧
  (∀ ℓ, 1 ≤ ℓ → ℓ ≤ L →
    0 < o.quota ℓ ∧ (atDepth R ℓ).card = o.quota ℓ ∧ (atDepth Bl ℓ).card = o.quota ℓ) ∧
  -- the copies `T⁺`, `T⁻`, both nonempty, and their marks `M⁺`, `M⁻`
  Tp = T.filter (fun l => d ≤ (R ∩ rootPath l).card) ∧
  Tm = T.filter (fun l => d ≤ (Bl ∩ rootPath l).card) ∧
  Tp.Nonempty ∧ Tm.Nonempty ∧
  Mp = R ∩ treeVertices Tp ∧ Mm = Bl ∩ treeVertices Tm ∧
  -- `|M^σ ∩ V_ℓ(T^σ)| ≤ p_ℓ` and `|M^σ ∩ π| ≥ d`
  (∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → (atDepth Mp ℓ).card ≤ o.quota ℓ ∧ (atDepth Mm ℓ).card ≤ o.quota ℓ) ∧
  (∀ l ∈ Tp, d ≤ (Mp ∩ rootPath l).card) ∧ (∀ l ∈ Tm, d ≤ (Mm ∩ rootPath l).card) ∧
  -- markings within the shared quotas leave a path unhit
  (∀ Ap Am : Finset (List ℕ), Ap ⊆ (treeVertices Tp).erase [] →
    Am ⊆ (treeVertices Tm).erase [] →
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → (atDepth Ap ℓ).card + (atDepth Am ℓ).card ≤ o.quota ℓ) →
    (∃ l ∈ Tp, Disjoint Ap (rootPath l)) ∨ (∃ l ∈ Tm, Disjoint Am (rootPath l))) ∧
  -- `D∗ ≥ 1` bounds every vertex's number of children in either copy
  1 ≤ o.branchBound ∧
  (∀ w ∈ treeVertices Tp, (children (treeVertices Tp) w).card ≤ o.branchBound) ∧
  (∀ w ∈ treeVertices Tm, (children (treeVertices Tm) w).card ≤ o.branchBound)

/-- The binary encoding of a list of addresses. -/
def addressListBits (A : List (List ℕ)) : List Bool :=
  BinaryEncoding.listBits (BinaryEncoding.listBits BinaryEncoding.natBits) A

/-- The binary encoding of the record, field by field. -/
def bits (o : AdmissibleTreeData) : List Bool :=
  addressListBits o.leaves ++ addressListBits o.red ++ addressListBits o.blue ++
  addressListBits o.plusLeaves ++ addressListBits o.minusLeaves ++
  addressListBits o.plusMarks ++ addressListBits o.minusMarks ++
  BinaryEncoding.natBits o.depth ++ BinaryEncoding.listBits BinaryEncoding.natBits o.quotas ++
  BinaryEncoding.natBits o.branchBound ++ BinaryEncoding.natBits o.sizeBound

end AdmissibleTreeData

end LogStarBinPacking


