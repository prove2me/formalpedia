-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Trie
-- name    : APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Trie
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:23.274124+00:00
-- url     : https://prove2.me/theorems/b0764f14-8e9f-4b01-b2e1-60577917f7d4
-- title:
--   Array-based tries and representation invariants
-- statement:
--   A trie for strings over eleven symbols is stored in an integer list $T$. Each vertex occupies eleven cells: above the fixed key depth they hold child addresses, with zero meaning absent; at the key depth the first cell holds the value. For a vertex address $p$, following a key is defined recursively by
--
--   $$\operatorname{walk}(T,p,[])=p,\qquad
--   \operatorname{walk}(T,p,d::w)=\operatorname{walk}\bigl(T,\operatorname{toNat}(T[p+d]),w\bigr).$$
--
--   Lookup reads the cell at the resulting address. Missing list entries read as zero. Insertion creates an eleven-zero-cell block when a child pointer is absent, follows the remaining key, and stores the value at its terminal vertex.
--
--   The representation predicates record aligned, distinct vertex blocks, valid parent-child pointers, a zero-filled free region, and the absence convention at address zero. For key length $L$, roots $r_i$, partial stored values $f(i,w)$, and a vertex-address map $v$, the representation requires
--
--   $$v(i,[])=r_i,\qquad f(i,w)=\operatorname{some}(z)\Rightarrow |w|=L\ \land\ v(i,w)\ne0\ \land\ T[v(i,w)]=z.$$
--
--   It permits additional stored keys. Separate predicates describe valid walks, valid insertions, and extensions preserving old vertices and unrelated values. This bundle supplies operations and invariants for later correctness and cost theorems.
--
--   References:
--
--   1. [Source formalization, lines 54–85](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L54-L85).
--   2. [Source formalization, lines 114–115](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L114-L115).
--   3. [Source formalization, lines 140–157](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L140-L157).
--   4. [Source formalization, lines 283–289](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L283-L289).
--   5. [Source formalization, lines 300–307](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L300-L307).
--   6. [Source formalization, lines 421–427](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L421-L427).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L54-L85; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L114-L115; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L140-L157; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L283-L289; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L300-L307; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/Trie.lean#L421-L427

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Tries in one array (Section 4.3)

"for each tile we store its boxes, with their values, in a standard trie on their strings of L
symbols.  Thus […] looking up or inserting a box, takes O(L) operations."  Here a string is a list
of L digits below 11, for the ten terms and the star.

All tries live in one array of integers and are numbered; the number of a trie is the number of its
tile.  A vertex is a block of eleven consecutive cells, one for each symbol, holding the address of
the child, or 0 if there is none; a vertex at depth L holds the value of its box in its first cell.
A box is stored if the pointers for its L symbols lead from the root of the trie to such a vertex
(`trieWalk`).  A new vertex is appended at the end of the array (`trieNew`).  The two operations
are `trieInsert` and `trieLookup`.

The interface is `TrieRep`: "the array holds tries with these roots and these stored values".  It
holds for an array without tries (`TrieRep.empty`), it is kept by a new trie (`TrieRep.new`) and by
an insertion (`TrieRep.insert`), and it says what a lookup returns (`TrieRep.lookup`).  `WalkOK` and
`InsertOK` say in addition that every address met on the way lies inside the array
(`TrieRep.walkOK`, `TrieRep.insertOK`).

The proof.  The pair (i, w) names the vertex of trie number i to which the prefix w leads.  The
invariant `TrieInv` gives every vertex its address nd (i, w), 0 if there is none.  `TrieRep` says
that such an nd exists, with nd (i, []) = roots i and the value v in the cell nd x for every entry
f x = some v.
1. Three steps keep the invariant: a new root, a new child, a value written at depth L
   (`TrieInv.newRoot`, `TrieInv.newChild`, `TrieInv.setVal`).  The first gives `TrieRep.new`.
2. An insertion is a sequence of new children and then one write.  Each step extends the tries
   (`TrieExt`): no vertex moves, no root appears, no value of another string changes.  `Inserted`
   collects what holds at the end, and `trieInsert_spec` proves it by induction on the rest of the
   string.  This gives `TrieRep.insert` and `TrieRep.insertOK`.
3. A lookup goes from the vertex of a prefix to the vertex of the next prefix (`trieWalk_spec`).
   This gives `TrieRep.lookup` and `TrieRep.walkOK`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The operations -/

/-- The vertex reached from the vertex p by following the symbols of a string. -/
def trieWalk (T : List ℤ) (p : ℕ) : List ℕ → ℕ
  | [] => p
  | d :: l => trieWalk T (T.getD (p + d) 0).toNat l

/-- The value stored for a string in the trie with the given root (for a string that is stored; see
`TrieRep.lookup`). -/
def trieLookup (T : List ℤ) (root : ℕ) (key : List ℕ) : ℤ := T.getD (trieWalk T root key) 0

/-- The array with a new vertex (without children) at its end; its address is the old length. -/
def trieNew (T : List ℤ) : List ℤ := T ++ List.replicate 11 0

/-- The array after storing the value v for a string, starting from the vertex p. -/
def trieInsert (T : List ℤ) (p : ℕ) : List ℕ → ℤ → List ℤ
  | [], v => T.set p v
  | d :: l, v =>
    if T.getD (p + d) 0 = 0 then trieInsert (trieNew (T.set (p + d) T.length)) T.length l v
    else trieInsert T (T.getD (p + d) 0).toNat l v

/-- Following a string from the vertex p, every vertex met is inside the array and every pointer
read is positive. -/
def WalkOK (T : List ℤ) (p : ℕ) : List ℕ → Prop
  | [] => 0 < p ∧ p + 11 ≤ T.length
  | d :: l => 0 < p ∧ p + 11 ≤ T.length ∧ 0 < T.getD (p + d) 0 ∧ WalkOK T (T.getD (p + d) 0).toNat l

/-- An insertion of a string from the vertex p follows the array as it changes: every vertex met is
inside the array, and every pointer read is 0 or positive. -/
def InsertOK (T : List ℤ) (p : ℕ) : List ℕ → Prop
  | [] => 0 < p ∧ p + 11 ≤ T.length
  | d :: l => 0 < p ∧ p + 11 ≤ T.length ∧
      if T.getD (p + d) 0 = 0 then InsertOK (trieNew (T.set (p + d) T.length)) T.length l
      else 0 < T.getD (p + d) 0 ∧ InsertOK T (T.getD (p + d) 0).toNat l




















end ThreeSumApsp.Spec

end

namespace ThreeSumApsp.Spec

/-! ## Arrays as functions -/

/-- The cells of an array, as a function; beyond the end of the array it is 0. -/
def cells (T : List ℤ) : ℕ → ℤ := fun a => T.getD a 0






















/-! ## The invariant -/

/-- The cells μ hold tries for strings of length L.  The pair (i, w) names the vertex of trie number
i for the prefix w, and nd (i, w) is its address, or 0 if there is no such vertex.  The vertices are
blocks of eleven cells in the region from lo to fr, the first free cell. -/
structure TrieInv (L lo : ℕ) (μ : ℕ → ℤ) (nd : ℕ × List ℕ → ℕ) (fr : ℕ) : Prop where
  /-- The cell number a of a vertex above depth L points to the child for the symbol a. -/
  child : ∀ i w a, w.length < L → a < 11 → nd (i, w) ≠ 0 → μ (nd (i, w) + a) = nd (i, w ++ [a])
  /-- The vertices are aligned blocks between lo and fr. -/
  range : ∀ x, nd x ≠ 0 → lo ≤ nd x ∧ nd x + 11 ≤ fr ∧ 11 ∣ (nd x - lo)
  /-- Different prefixes have different vertices. -/
  inj : ∀ x y, nd x ≠ 0 → nd x = nd y → x = y
  /-- The parent of a vertex is a vertex. -/
  closed : ∀ i w a, nd (i, w ++ [a]) ≠ 0 → nd (i, w) ≠ 0
  /-- The cells from fr on are free. -/
  fresh : ∀ a, fr ≤ a → μ a = 0
  /-- The address 0 means: no vertex. -/
  lo_pos : 0 < lo
  /-- The free region starts at a block boundary. -/
  fr_aligned : lo ≤ fr ∧ 11 ∣ (fr - lo)

namespace TrieInv

variable {L lo fr : ℕ} {μ : ℕ → ℤ} {nd : ℕ × List ℕ → ℕ}





















































































































end TrieInv

/-! ## Insertion -/

/-- The tries (μ', nd') extend the tries (μ, nd): no vertex moves, there is no new root, and the
value of every string other than x is kept. -/
 structure TrieExt (L : ℕ) (x : ℕ × List ℕ) (μ : ℕ → ℤ) (nd : ℕ × List ℕ → ℕ) (μ' : ℕ → ℤ)
    (nd' : ℕ × List ℕ → ℕ) : Prop where
  old_vertex : ∀ y, nd y ≠ 0 → nd' y = nd y
  old_root : ∀ i, nd' (i, []) ≠ 0 → nd (i, []) ≠ 0
  old_value : ∀ i w, w.length = L → nd (i, w) ≠ 0 → (i, w) ≠ x → μ' (nd (i, w)) = μ (nd (i, w))










/-- T' with the vertices nd' is T with the vertices nd after the value v was stored for the string
x: the invariant holds, x has a vertex, the vertex holds v, and the tries have been extended. -/
 structure Inserted (L lo : ℕ) (x : ℕ × List ℕ) (v : ℤ) (T : List ℤ) (nd : ℕ × List ℕ → ℕ)
    (T' : List ℤ) (nd' : ℕ × List ℕ → ℕ) : Prop where
  inv : TrieInv L lo (cells T') nd' T'.length
  vertex : nd' x ≠ 0
  value : cells T' (nd' x) = v
  ext : TrieExt L x (cells T) nd (cells T') nd'







section

variable {L lo i : ℕ} {T : List ℤ} {nd : ℕ × List ℕ → ℕ} {w : List ℕ}








































































/-! ## Lookup -/
























end

/-! ## The interface -/

public section

/-- The array T holds, from the address lo on, tries number 0, 1, … for strings of L symbols.  The
root of trie number i is at the address roots i (0 if the trie does not exist yet), and every entry
f (i, key) = some v is stored: the string key has the value v in trie number i.  The array may hold
more than f lists. -/
def TrieRep (L lo : ℕ) (T : List ℤ) (roots : ℕ → ℕ) (f : ℕ × List ℕ → Option ℤ) : Prop :=
  ∃ nd, TrieInv L lo (cells T) nd T.length ∧ (∀ i, nd (i, []) = roots i) ∧
    ∀ i key v, f (i, key) = some v → key.length = L ∧ nd (i, key) ≠ 0 ∧ cells T (nd (i, key)) = v

namespace TrieRep













variable {L lo : ℕ} {T : List ℤ} {roots : ℕ → ℕ} {f : ℕ × List ℕ → Option ℤ}




















































































end TrieRep

end

end ThreeSumApsp.Spec


