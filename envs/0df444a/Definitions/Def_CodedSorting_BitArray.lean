-- Prove2me | Definitions.Def_CodedSorting_BitArray
-- name    : CodedSorting_BitArray
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:06:31.212192+00:00
-- url     : https://prove2.me/theorems/8c96cecd-3e1c-4b71-addc-0505f46e4984
-- title:
--   Bit arrays on a word disk and the address-field interchange
-- statement:
--   A bit array of $V=PG\ell2^{2u}$ bits has its positions indexed by tuples
--
--   $$(p,t,g,d,z)\in[P]\times[2^u]\times[G]\times[2^u]\times[\ell],$$
--
--   stored in lexicographic order with $z$ varying fastest, so that the tuple is at position $\big((((p2^u+t)G+g)2^u+d)\ell+z\big)$. The **address-field interchange** of width $u$ moves the bit at $(p,t,g,d,z)$ to $(p,d,g,t,z)$; as a map on positions it decodes $p,t,g,d,z$ from the position and re-encodes $(p,d,g,t,z)$.
--
--   The array is stored contiguously on a disk of $w$-bit words: bit $j$ of the array is bit $j \bmod w$ (the coefficient of $2^{j\bmod w}$) of disk word $\lfloor j/w\rfloor$, and every other bit of the disk is $0$.
--
--   These are the input and output conventions of Lemma 6.1, and the interchange map is reused for the transpose of Columnsort (Proposition 7.1).
--
--   **Formalization Note** The packing of $w$ bits into a word is reduced modulo $2^w$ only to give it the word type; the sum is already below $2^w$.
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §6.1, pp.18–19 (PDF 19–20), and Figure 3, p.9 (PDF 10)

import Mathlib
import Definitions.Def_CodedSorting_Machine

namespace CodedSorting

/-! # Bit arrays and the address-field interchange

arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §6.1, pp.18–19. -/

/-- The position of bit `(p, t, g, d, z) ∈ [P] × [2^u] × [G] × [2^u] × [ℓ]` in a bit array stored in
lexicographic order of `(p, t, g, d, z)`, with `z` varying fastest (§6.1, p.19). -/
def bitAddr (G ℓ u : ℕ) (p t g d z : ℕ) : ℕ :=
  (((p * 2 ^ u + t) * G + g) * 2 ^ u + d) * ℓ + z

/-- The address-field interchange as a map on positions (§6.1, p.19): the bit at position
`bitAddr G ℓ u p t g d z` moves to position `bitAddr G ℓ u p d g t z`. The coordinates are read off
the position `a` as `z = a mod ℓ`, `d`, `g`, `t` the next mixed-radix digits, and `p` the rest. -/
def interchangeIndex (G ℓ u : ℕ) (a : ℕ) : ℕ :=
  let z := a % ℓ
  let d := (a / ℓ) % 2 ^ u
  let g := (a / ℓ / 2 ^ u) % G
  let t := (a / ℓ / 2 ^ u / G) % 2 ^ u
  let p := a / ℓ / 2 ^ u / G / 2 ^ u
  bitAddr G ℓ u p d g t z

/-- Pack a bit sequence into words: word `i` holds bits `i·w, …, i·w + w − 1`, bit `i·w + b` as
bit `b` of the word (its coefficient of `2^b`).

**Formalization Note.** The sum is below `2^w`, so the reduction `mod 2^w` changes nothing; it only
makes the value a `Word w` by construction. -/
def packBits (w : ℕ) (f : ℕ → Bool) (i : ℕ) : Word w :=
  ⟨(∑ b : Fin w, if f (i * w + b) then 2 ^ (b : ℕ) else 0) % 2 ^ w,
    Nat.mod_lt _ (Nat.two_pow_pos w)⟩

/-- Bit `j` of a word disk: bit `j mod w` of disk word `⌊j / w⌋` (paper.md decision 13: "a bit
array stored contiguously on disk", §6.1, p.18). -/
def readBit {w : ℕ} (d : Disk w) (j : ℕ) : Bool :=
  Nat.testBit (d (j / w)) (j % w)

/-- The disk holding the bit array `bits` of `V` bits contiguously from bit `0` (words
`0, …, ⌈V/w⌉ − 1`); every other bit, and hence every other word, is `0`. -/
def bitArrayDisk {V : ℕ} (w : ℕ) (bits : Fin V → Bool) : Disk w :=
  packBits w (fun j => if h : j < V then bits ⟨j, h⟩ else false)

end CodedSorting


