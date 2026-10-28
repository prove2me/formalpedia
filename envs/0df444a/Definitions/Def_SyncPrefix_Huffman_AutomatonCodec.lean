-- Prove2me | Definitions.Def_SyncPrefix_Huffman_AutomatonCodec
-- name    : SyncPrefix_Huffman_AutomatonCodec
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-27T07:39:03.184771+00:00
-- url     : https://prove2.me/theorems/327e1738-9a31-4c8d-85a2-48fe41ca9766
-- title:
--   Total unary decoder `decodeAutomaton` and Lemma 5 encoding map `huffmanEncodeMap`
-- statement:
--   This definition introduces a total parser `decodeAutomaton` for the separator-terminated unary encoding `Automaton.encode` over $\mathrm{Option\ Bool}$, together with the induced total transformation `huffmanEncodeMap` for the Lemma 5 construction (Ryzhikov and Szykuła, 2018, p. 6).
--
--   Specifically, `readUnaryOpt` extracts a single unary number terminated by `none`, `readUnaryList` extracts a fixed-length sequence of unary numbers, and `decodeAutomaton` parses the state count $n$, alphabet size $k$, and the $n \cdot k$ transition entries $A.\delta(q, a)$ in row-major order:
--
--   $$
--   \mathrm{huffmanEncodeMap}(w) = \mathrm{encode}(\mathrm{huffmanOfStronglyAcyclic}(\mathrm{decodeAutomaton}(w))).
--   $$
--
--   This separates the exact round-trip identity $\mathrm{decodeAutomaton}(\mathrm{encode}(A)) = A$ from the polynomial-time machine complexity of `huffmanEncodeMap`.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 6, Lemma 5

import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_SyncPrefix_Huffman_Lemma5Construction
import Definitions.Def_CookPvsNP_defs

namespace SyncPrefix.Huffman

/-- Read one separator-terminated (`none`-terminated) unary natural number from an `Option Bool`
stream. -/
def readUnaryOpt : List (Option Bool) → ℕ × List (Option Bool)
  | [] => (0, [])
  | none :: xs => (0, xs)
  | some _ :: xs =>
      let p := readUnaryOpt xs
      (p.1 + 1, p.2)

/-- Read `m` consecutive separator-terminated unary natural numbers from an `Option Bool` stream. -/
def readUnaryList : ℕ → List (Option Bool) → List ℕ × List (Option Bool)
  | 0, w => ([], w)
  | m + 1, w =>
      let p := readUnaryOpt w
      let q := readUnaryList m p.2
      (p.1 :: q.1, q.2)

/-- Total decoder reconstructing an `Automaton` from its unary `Option Bool` encoding `A.encode`. -/
def decodeAutomaton (w : List (Option Bool)) : Automaton :=
  let p₁ := readUnaryOpt w
  let n := p₁.1
  let p₂ := readUnaryOpt p₁.2
  let k := p₂.1
  let table := (readUnaryList (n * k) p₂.2).1
  { n := n
    k := k
    δ := fun q a =>
      let v := table.getD (q.val * k + a.val) 0
      if h : v < n then ⟨v, h⟩ else q }

/-- Total encoding map for the Lemma 5 Huffman-decoder construction: decodes an input string as an
automaton `A` and re-encodes `huffmanOfStronglyAcyclic A`. -/
def huffmanEncodeMap (w : List (Option Bool)) : List (Option Bool) :=
  (huffmanOfStronglyAcyclic (decodeAutomaton w)).encode

end SyncPrefix.Huffman


