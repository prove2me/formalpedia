-- Prove2me | Definitions.Def_SyncPrefix_Huffman_Constructions
-- name    : SyncPrefix_Huffman_Constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:57.336983+00:00
-- url     : https://prove2.me/theorems/a59af888-6106-4111-b247-451a284cbc97
-- title:
--   pp. 5–8 — the pipe automaton of Theorem 2, codes and absorbing pairs, composition of codes, the tree-substitution decoder, the Wielandt code
-- statement:
--   This file defines the objects built in the proofs of Theorem 2 and Corollary 8.
--
--   **The pipe automaton** (p. 5). For a Set Cover instance with points $x_1, \dots, x_p$ and sets $c_1, \dots, c_m$, the automaton has one letter per set, a "pipe" of states $q^{(j)}_1, \dots, q^{(j)}_p$ for every point $x_j$, and one more state $f$. For $1 \le i \le p - 1$ the letter $k$ maps $q^{(j)}_i$ to $f$ if $x_j \in c_k$ and to $q^{(j)}_{i+1}$ otherwise; every letter maps $q^{(j)}_p$ and $f$ to $f$.
--
--   **Codes** (p. 7). For a set $X$ of words over an alphabet $\Sigma$:
--
--   1. $X$ is a **code** if no word factors into elements of $X$ in two different ways;
--   2. a code is **complete** if every word is a factor of a word of $X^*$;
--   3. a pair $(\ell, r)$ of words of $X^*$ is **absorbing** if $\ell\Sigma^* \cap \Sigma^* r \subseteq X^*$, and its length is $|\ell| + |r|$;
--   4. a complete code with an absorbing pair is **synchronizing**;
--   5. $X$ is a **prefix code** if $\varepsilon \notin X$ and no element of $X$ is a proper prefix of another, and a **maximal** prefix code if it is contained in no other prefix code.
--
--   **Composition** (p. 7). For a code $Y$ over $\Sigma_Y$, a code $Z$ over $\Sigma_Z$ and a bijection $\beta : \Sigma_Y \to Z$, extended to words by $\beta(y_1 \cdots y_k) = \beta(y_1) \cdots \beta(y_k)$,
--   $$Y \circ_\beta Z = \{\beta(y) : y \in Y\}.$$
--
--   **The composition decoder** (pp. 7–8). Given an automaton $H_Y$ over $\Sigma_Y$ and a finite prefix code $Z$ with tree $T_Z$, the states are the pairs $(q, p)$ of a state $q$ of $H_Y$ and an inner vertex $p$ of $T_Z$ (a proper prefix of a codeword, the root being $\varepsilon$). The pair $(q, \varepsilon)$ is $q$ itself; reading a letter $x$ at $(q, p)$ moves to $(q, px)$ if $px$ is an inner vertex, and to $(\delta_Y(q, b), \varepsilon)$ if $px$ is the leaf $\beta(b)$.
--
--   **The Wielandt code** (p. 8). For $L \ge 1$, $Z_L = 0\{0,1\}^{L-1} \cup 1\{0,1\}^{L}$.
--
--   **Formalization Note** The state $j\,p + i$ ($0 \le i, j < p$) is $q^{(j+1)}_{i+1}$ and the state $p^2$ is $f$. Words are Lean lists and sets of words are Mathlib's `Language`, with its Kleene star $X^*$; `lang Z` is the language of a finite set of words. `absorbLength` is the infimum of lengths of absorbing pairs (junk `0` if there is none). The decoder's state set always contains $\varepsilon$, and its third branch ($px$ neither a codeword nor a proper prefix of one) is a junk value that is never used when $Z$ is a maximal prefix code. The letters $0, 1$ are `false`, `true`.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 5 (proof of Theorem 2), p. 7 (codes, absorbing pairs, complete and synchronizing codes, composition), pp. 7–8 (the Huffman decoder of the composition), p. 8 (proof of Corollary 8, the code Z)

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_SyncPrefix_Huffman_Complexity

namespace SyncPrefix.Huffman

open SetCoverThreshold.SetCover Computability

/-! ### The pipe automaton of Theorem 2 (p. 5) -/

/-- The automaton of the proof of Theorem 2 built from a Set Cover instance with `p = I.n`
points and the sets `c_0, …, c_{m-1}` of `I.sets`: one letter per set, and `p · p + 1` states.
Points and sets are numbered from `0`: the state `j * p + i` (`j, i < p`) is the `(i+1)`-st
state of the pipe of the point `x_j`, and the state `p * p` is `f`. A letter `a` maps `f` to `f`;
it maps the state `j * p + i` to `f` if `i + 1 = p` or `x_j ∈ c_a`, and to `j * p + i + 1`
otherwise. -/
def scAutomaton (I : SCInstance) : Automaton where
  n := I.n * I.n + 1
  k := I.sets.length
  δ := fun q a =>
    if h : q.val < I.n * I.n then
      if q.val % I.n + 1 = I.n ∨
          (⟨q.val / I.n, Nat.div_lt_of_lt_mul h⟩ : Fin I.n) ∈ I.sets.get a then
        ⟨I.n * I.n, Nat.lt_succ_self _⟩
      else ⟨q.val + 1, by omega⟩
    else ⟨I.n * I.n, Nat.lt_succ_self _⟩

/-! ### Codes (§5, p. 7) -/

section Codes

variable {α β : Type}

/-- The language of a finite set of words. -/
def lang (Z : Finset (List α)) : Language α := {w | w ∈ Z}

/-- A code: no word is a concatenation of codewords in two different ways. (This excludes the
empty word from a code.) -/
def IsCode (X : Language α) : Prop :=
  ∀ xs ys : List (List α), (∀ x ∈ xs, x ∈ X) → (∀ y ∈ ys, y ∈ X) →
    xs.flatten = ys.flatten → xs = ys

/-- A complete code: a code such that every word is a factor of a word of `X∗`. -/
def IsCompleteCode (X : Language α) : Prop :=
  IsCode X ∧ ∀ w : List α, ∃ v₁ v₂ : List α, v₁ ++ w ++ v₂ ∈ X∗

/-- `(l, r)` is an absorbing pair of `X`: `l, r ∈ X∗` and `l Σ∗ ∩ Σ∗ r ⊆ X∗`. -/
def IsAbsorbing (X : Language α) (l r : List α) : Prop :=
  l ∈ X∗ ∧ r ∈ X∗ ∧ ∀ w : List α, l <+: w → r <:+ w → w ∈ X∗

/-- A synchronizing code: a complete code having an absorbing pair. -/
def IsSyncCode (X : Language α) : Prop :=
  IsCompleteCode X ∧ ∃ l r, IsAbsorbing X l r

/-- The length `|l| + |r|` of a shortest absorbing pair (junk `0` if there is none). -/
noncomputable def absorbLength (X : Language α) : ℕ :=
  sInf {L | ∃ l r, IsAbsorbing X l r ∧ l.length + r.length = L}

/-- A prefix code: the empty word is not a codeword, and no codeword is a prefix of another. -/
def IsPrefixCode (X : Language α) : Prop :=
  [] ∉ X ∧ ∀ x ∈ X, ∀ y ∈ X, x <+: y → x = y

/-- A maximal prefix code: a prefix code contained in no other prefix code. -/
def IsMaximalPrefixCode (X : Language α) : Prop :=
  IsPrefixCode X ∧ ∀ X' : Language α, IsPrefixCode X' → X ≤ X' → X' = X

/-- The substitution `β(y) = β(y₁)β(y₂)⋯β(y_k)` of codewords of `Z` for the letters of `y`. -/
def subst {Z : Language α} (e : β ≃ {z // z ∈ Z}) (y : List β) : List α :=
  (y.map fun b => (e b).val).flatten

/-- The composition `Y ∘_β Z = {β(y) | y ∈ Y}` of a code `Y` over `β` with a code `Z` over `α`
through a bijection `β : Σ_Y → Z`. -/
def compose (Y : Language β) (Z : Language α) (e : β ≃ {z // z ∈ Z}) : Language α :=
  {x | ∃ y ∈ Y, x = subst e y}

end Codes

/-! ### The tree-substitution decoder (pp. 7–8) and the Wielandt code (p. 8) -/

section Decoder

variable {σ α β : Type} [DecidableEq α]

/-- All prefixes of codewords of `Z`: the vertices of the tree `T_Z`. -/
def allPrefixes (Z : Finset (List α)) : Finset (List α) :=
  Z.biUnion fun z => z.inits.toFinset

/-- The prefixes of codewords that are not codewords, together with the empty word: for a
prefix code `Z` with `[] ∉ Z` these are exactly the inner vertices of `T_Z` (the empty word, the
root, is then already one of them). -/
def properPrefixes (Z : Finset (List α)) : Finset (List α) :=
  insert [] ((allPrefixes Z).filter fun p => p ∉ Z)

/-- The states of the decoder: a state `q` of `H_Y` and an inner vertex `p` of `T_Z`. The pair
`(q, [])` is `q` itself; `(q, p)` with `p ≠ []` is the new state at vertex `p` of the copy of
`T_Z` hanging from `q`. -/
abbrev DecoderState (σ : Type) (Z : Finset (List α)) : Type :=
  σ × {p // p ∈ properPrefixes Z}

/-- The state `q` of `H_Y` inside the decoder (the root of its copy of `T_Z`). -/
def rootState (Z : Finset (List α)) (q : σ) : DecoderState σ Z :=
  (q, ⟨[], Finset.mem_insert_self _ _⟩)

/-- The decoder of the composition (pp. 7–8): from `(q, p)`, the letter `x` moves to the vertex
`p x` of the copy of `T_Z` at `q`; when `p x` is a leaf, i.e. the codeword `β(b)`, it moves to
the state `δ_Y(q, b)` of `H_Y` instead. The last branch (`p x` neither a codeword nor a prefix of
one) is never taken when `Z` is a maximal prefix code; it is a junk value. -/
def composeDecoder (δY : σ → β → σ) (Z : Finset (List α)) (e : β ≃ {z // z ∈ Z}) :
    DecoderState σ Z → α → DecoderState σ Z := fun s x =>
  if h : s.2.val ++ [x] ∈ Z then rootState Z (δY s.1 (e.symm ⟨s.2.val ++ [x], h⟩))
  else if h' : s.2.val ++ [x] ∈ properPrefixes Z then (s.1, ⟨s.2.val ++ [x], h'⟩)
  else rootState Z s.1

end Decoder

/-- The code `Z_L = 0{0,1}^{L-1} ∪ 1{0,1}^{L}` of the proof of Corollary 8 (p. 8), with the
paper's letters `0, 1` written `false, true`. -/
def wielandtCode (L : ℕ) : Finset (List Bool) :=
  (Finset.univ.image fun v : Fin (L - 1) → Bool => false :: List.ofFn v) ∪
    (Finset.univ.image fun v : Fin L → Bool => true :: List.ofFn v)

end SyncPrefix.Huffman


