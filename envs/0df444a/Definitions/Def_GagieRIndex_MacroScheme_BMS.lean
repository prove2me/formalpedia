-- Prove2me | Definitions.Def_GagieRIndex_MacroScheme_BMS
-- name    : GagieRIndex_MacroScheme_BMS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:47.087662+00:00
-- url     : https://prove2.me/theorems/c2085aff-af24-4f05-8ec8-1efd65f48697
-- title:
--   Definition 6, p. 28 — bidirectional macro scheme
-- statement:
--   A **bidirectional macro scheme** (BMS) of size $b$ on a sequence $S[1..n]$ is a partition $S=S_1\cdots S_b$ into consecutive blocks, each of which is either an explicit symbol (a block of length 1) or a pointer to another occurrence $S[j..j']$ of the same content elsewhere in $S$. The source map $f$ sends a position $i$ that lies at offset $i'$ inside a pointer block $S_k\to S[j..j']$ to
--   $$f(i)=j+i'-1,$$
--   and is arbitrary on explicit symbols. The scheme is correct when, for every position $i$, some iterate $f^k(i)$, $k\ge 0$, is an explicit symbol: every symbol can be recovered by following the chain of copies.
--
--   A BMS is the most general copy-based compressed representation; grammar and Lempel–Ziv representations are special cases, and its size lower-bounds theirs up to logarithmic factors.
--
--   **Formalization Note** The sequence may have any symbol type. A scheme is a list of blocks laid out consecutively from position 1, each recording its length and an optional source start $j$; the size $b$ is the length of the list. The lengths sum to $n$, every block has length at least 1, explicit blocks have length 1, and a pointer block starting at $i$ with length $\ell$ has $j\ne i$, $1\le j$, $j+\ell\le n+1$ and $S[i+t]=S[j+t]$ for $t<\ell$ (the source may overlap the block). The arbitrary value of $f$ on explicit symbols is fixed to the identity, and correctness asks that some iterate of $f$ lands on the start of an explicit block.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 28, Definition 6

import Mathlib

namespace GagieRIndex.MacroScheme

/-- A block `S_k` of a macro scheme: its length, and `some j` if it is a pointer to `S[j..]`
(`none` if it is an explicit symbol). -/
structure Block where
  len : ℕ
  src : Option ℕ

/-- The first position of block `k` when the blocks are laid out consecutively from position 1. -/
def blockStart (B : List Block) (k : ℕ) : ℕ := 1 + ((B.take k).map Block.len).sum

/-- The index of the block containing position `x`, if any. -/
def blockOf (B : List Block) (x : ℕ) : Option ℕ :=
  (List.range B.length).find?
    (fun k => blockStart B k ≤ x && x < blockStart B k + (B.getD k ⟨0, none⟩).len)

/-- The source map `f` of Definition 6 (p. 28): `f(i) = j + i′ − 1` when `S[i] = S_k[i′]` lies in a
block `S_k` pointing to `S[j..j′]`; the identity on explicit symbols (the page leaves it arbitrary). -/
def srcMap (B : List Block) (x : ℕ) : ℕ :=
  match blockOf B x with
  | some k => match (B.getD k ⟨0, none⟩).src with
    | some j => j + (x - blockStart B k)
    | none => x
  | none => x

/-- `B` is a (correct) bidirectional macro scheme of `S[1..n]` (Definition 6, p. 28); its size is
`B.length`. The blocks partition `[1..n]`; an explicit block has length 1; a pointer block
`S[i..i′]` points to a different occurrence `S[j..j′]` inside `[1..n]`; and from every position
some iterate of `f` reaches an explicit symbol. -/
def IsBMS {α : Type*} (n : ℕ) (S : ℕ → α) (B : List Block) : Prop :=
  (B.map Block.len).sum = n ∧
  (∀ b ∈ B, 1 ≤ b.len ∧ (b.src = none → b.len = 1)) ∧
  (∀ k (hk : k < B.length), ∀ j, (B[k]).src = some j →
      j ≠ blockStart B k ∧ 1 ≤ j ∧ j + (B[k]).len ≤ n + 1 ∧
      ∀ t < (B[k]).len, S (blockStart B k + t) = S (j + t)) ∧
  ∀ x, 1 ≤ x → x ≤ n → ∃ m k, ∃ hk : k < B.length,
      (B[k]).src = none ∧ (srcMap B)^[m] x = blockStart B k

end GagieRIndex.MacroScheme


