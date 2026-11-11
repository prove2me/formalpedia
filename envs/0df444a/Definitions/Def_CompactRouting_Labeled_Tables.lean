-- Prove2me | Definitions.Def_CompactRouting_Labeled_Tables
-- name    : CompactRouting_Labeled_Tables
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:06:34.6552+00:00
-- url     : https://prove2.me/theorems/ab1a7b88-4625-4b0f-9d3c-e4c66c9a40a6
-- title:
--   The labels $L(v)$ and routing tables $RT(u)$ of §4.1 and their sizes in bits
-- statement:
--   Given a hierarchy, pivots $p_i$ and **tree labels** $L(x,T(C(w)))$ (a bit string for every cluster root $w$ and vertex $x$; written $\mathrm{tl}(w,x)$), §4.1 defines the label of $v$ and the routing table of $u$:
--   $$L(v)=\big\langle \mathrm{id}(v),\ \{\langle i,\ h_i(v),\ \mathrm{id}(p_i(v)),\ L(v,T(C(p_i(v)))),\ L(p_i(v),T(C(p_i(v))))\rangle : i\in[k]\}\big\rangle,$$
--   $$RT(u)=L(u)\ \cup\ \{\langle \mathrm{id}(w),L(u,T(C(w)))\rangle: w\in B(u)\}\ \cup\ \{\langle\mathrm{id}(x),L(x,T(C(u)))\rangle : x\in C(u)\},$$
--   the last two parts being separately tagged dictionaries keyed by identifiers. Sizes $|L(v)|$, $|RT(u)|$ are lengths in bits of a fixed self-delimiting encoding.
--
--   **Formalization Note.** A natural number $z$ is encoded by $\ell$ ones, a zero and its $\ell$ binary digits ($\ell$ the number of binary digits of $z$); a bit string by its length and its bits; a list by its length and its entries. $\mathrm{id}(x)=x+1$; the height $h_i(v)$ is stored as $\lfloor h_i(v)\rfloor$, exact for integer weights (fn. 5). The tree labels are a parameter `tl w x`; the cluster trees themselves are not constructed.
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 12 (§4.1, L(v), RT(u))

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Clusters

/-!
# The labels `L(v)` and routing tables `RT(u)` of §4.1, and their sizes in bits

Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), §4.1, p. 12:
`L(v) = ⟨id(v), {⟨i, h_i(v), id(p_i(v)), L(v, T(C(p_i(v)))), L(p_i(v), T(C(p_i(v))))⟩ | i ∈ [k]}⟩`
and `RT(u) = L(u) ∪ {⟨id(w), L(u, T(C(w)))⟩ | w ∈ B(u)} ∪ {⟨id(x), L(x, T(C(u)))⟩ | x ∈ C(u)}`,
the last two parts being separately tagged dictionaries keyed by identifiers.

Conventions.
* The tree labels are a parameter `tl : Fin n → Fin n → List Bool`: `tl w x` is the label
  `L(x, T(C(w)))` of `x` in the cluster tree of `w`, a bit string.
* `id(x) = x + 1` for `x : Fin n`. A height `h_i(v)` is stored as the natural number
  `⌊h_i(v)⌋` (exact for integer weights, footnote 5).
* Sizes are in bits: a natural number `z` is written self-delimitingly as `len` ones, a zero,
  and the `len` binary digits of `z` (`len` = number of binary digits); a bit string is its
  length followed by its bits; a list is its length followed by its entries.
-/

namespace CompactRouting.Labeled

open TZLevelsADO

/-- Self-delimiting binary code of a natural number (Elias-gamma style). -/
def encNat (z : ℕ) : List Bool :=
  List.replicate (Nat.digits 2 z).length true ++ false :: (Nat.digits 2 z).map fun d => decide (d = 1)

/-- A bit string written as its length followed by its bits. -/
def encBits (b : List Bool) : List Bool :=
  encNat b.length ++ b

/-- A list written as its length followed by the codes of its entries. -/
def encList {α : Type} (f : α → List Bool) (l : List α) : List Bool :=
  encNat l.length ++ (l.map f).flatten

/-- One entry `⟨i, h_i(v), id(p_i(v)), L(v, T(C(p_i(v)))), L(p_i(v), T(C(p_i(v))))⟩` of `L(v)`. -/
structure LabelEntry where
  /-- the level `i` -/
  level : ℕ
  /-- the height `h_i(v)` -/
  height : ℕ
  /-- the identifier `id(p_i(v))` -/
  pivotId : ℕ
  /-- `L(v, T(C(p_i(v))))` -/
  ownTreeLabel : List Bool
  /-- `L(p_i(v), T(C(p_i(v))))` -/
  pivotTreeLabel : List Bool

/-- The label `L(v) = ⟨id(v), {entries}⟩`. -/
structure Label where
  /-- `id(v)` -/
  id : ℕ
  /-- the entries for `i ∈ [k]` -/
  entries : List LabelEntry

/-- The routing table `RT(u)`: the label `L(u)` and the two tagged dictionaries. -/
structure Table where
  /-- `L(u)` -/
  label : Label
  /-- the bunch part `{⟨id(w), L(u, T(C(w)))⟩ | w ∈ B(u)}` -/
  bunchPart : List (ℕ × List Bool)
  /-- the cluster part `{⟨id(x), L(x, T(C(u)))⟩ | x ∈ C(u)}` -/
  clusterPart : List (ℕ × List Bool)

/-- Bit code of a label entry. -/
def LabelEntry.enc (e : LabelEntry) : List Bool :=
  encNat e.level ++ encNat e.height ++ encNat e.pivotId ++ encBits e.ownTreeLabel ++
    encBits e.pivotTreeLabel

/-- Bit code of a label. -/
def Label.enc (L : Label) : List Bool :=
  encNat L.id ++ encList LabelEntry.enc L.entries

/-- Bit code of a dictionary entry `⟨id, tree label⟩`. -/
def encPair (e : ℕ × List Bool) : List Bool :=
  encNat e.1 ++ encBits e.2

/-- Bit code of a routing table (the three parts in order, each self-delimiting). -/
def Table.enc (T : Table) : List Bool :=
  T.label.enc ++ encList encPair T.bunchPart ++ encList encPair T.clusterPart

/-- `|L(v)|`, the size of a label in bits. -/
def Label.size (L : Label) : ℕ := L.enc.length

/-- `|RT(u)|`, the size of a routing table in bits. -/
def Table.size (T : Table) : ℕ := T.enc.length

/-- The identifier `id(x) = x + 1 ∈ {1, …, n}`. -/
def vid {n : ℕ} (x : Fin n) : ℕ := x.val + 1

/-- §4.1, p. 12: the label `L(v)` built from the hierarchy `A`, the pivots `p` and the tree
labels `tl`. -/
noncomputable def labelOf {G : Graph} {k : ℕ} (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n)
    (tl : Fin G.n → Fin G.n → List Bool) (v : Fin G.n) : Label :=
  { id := vid v
    entries := (List.range k).map fun i =>
      { level := i
        height := ⌊height A i v⌋₊
        pivotId := vid (p i v)
        ownTreeLabel := tl (p i v) v
        pivotTreeLabel := tl (p i v) (p i v) } }

/-- §4.1, p. 12: the routing table `RT(u)`. -/
noncomputable def tableOf {G : Graph} {k : ℕ} (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n)
    (tl : Fin G.n → Fin G.n → List Bool) (u : Fin G.n) : Table :=
  { label := labelOf A p tl u
    bunchPart := (bunch A u).toList.map fun w => (vid w, tl w u)
    clusterPart := (cluster A u).toList.map fun x => (vid x, tl u x) }

end CompactRouting.Labeled


