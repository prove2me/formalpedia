-- Prove2me | Definitions.Def_AuctionMatroidInt_Supplement_StreamAlg
-- name    : AuctionMatroidInt_Supplement_StreamAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:21:32.747294+00:00
-- url     : https://prove2.me/theorems/9e202053-504f-4a49-8083-91353c207c80
-- title:
--   Deterministic multi-pass semi-streaming algorithms with independence oracles
-- statement:
--   In the **semi-streaming setting** for matroid intersection on the ground set $[n]$, the elements arrive one by one as a stream, the algorithm may read the stream in several sequential passes, it may query independence oracles of $M_1$ and $M_2$, and its space is the number of machine words it stores.
--
--   A **stream algorithm** for $[n]$ consists of an initial memory and a transition rule. The memory is a finite list of words, each holding either a natural number or (the name of) a ground-set element. At every micro-step the rule sees the current memory and the arriving element (or an end-of-pass signal) and chooses one action:
--
--   1. **query** oracle $i\in\{1,2\}$ on a set $S$, and replace the memory by one chosen from the Boolean answer (the same element keeps arriving);
--   2. **consume** the arriving element, replacing the memory; after the last element comes the end-of-pass signal, and consuming it starts a new pass from the first element;
--   3. **halt** with an output set $X\subseteq[n]$.
--
--   The **run** on a stream order $\sigma$ (the same order in every pass) with given oracle answers is the sequence of configurations: memory, position in the stream, number of passes started (1 at the start), number of queries made, and the output once halted. A halted configuration no longer changes.
--
--   **Formalization Note** The paper names no instruction set; computation inside a transition is free (the query-complexity convention of §2.1), but the algorithm remembers nothing outside its memory, and the memory is measured at every micro-step, so working memory is charged. Which queries are allowed is the separate predicate `StreamAlg.IsLegal`.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §6.1, p.30 (PDF p.32) and footnote 3, p.5 (PDF p.7)

import Mathlib

namespace AuctionMatroidInt.Supplement

/-- **A memory cell (machine word) of a semi-streaming algorithm.**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), footnote 3, p.5: "We measure the
space complexity by the number of machine words, and we assume that each machine word has
O(log n) bits."

A cell holds either a number (`num k`) or a stored element of the ground set `[n]` (`elem e`).

**Formalization Note.** Elements are kept apart from numbers so that "the elements stored in
memory" (§6.1, p.30) is well defined: an element is stored exactly when some cell is `elem e`.
An element cell occupies one word (an element name has O(log n) bits); the size of `num` cells
is bounded in the theorem that uses the model. -/
inductive Cell (n : ℕ) where
  /-- A word holding the number `k`. -/
  | num : ℕ → Cell n
  /-- A word holding (the name of) the ground-set element `e`. -/
  | elem : Fin n → Cell n
  deriving DecidableEq

namespace Cell

variable {n : ℕ}

/-- Rename the ground-set elements by the permutation `τ`; numbers are unchanged. -/
def relabel (τ : Equiv.Perm (Fin n)) : Cell n → Cell n
  | num k => num k
  | elem e => elem (τ e)

end Cell

/-- The set of ground-set elements stored in the memory `m` (the elements `e` with a cell
`elem e` in `m`). -/
def storedElems {n : ℕ} (m : List (Cell n)) : Finset (Fin n) :=
  Finset.univ.filter (fun e => Cell.elem e ∈ m)

/-- **One action of a semi-streaming algorithm**, chosen from its memory and the arriving
element:
* `query i S k`: ask the independence oracle of `M_{i+1}` whether `S` is independent and replace
  the memory by `k b`, where `b` is the Boolean answer (the current element keeps arriving);
* `consume m'`: replace the memory by `m'` and move on to the next element of the stream (after
  the last element, the end-of-pass signal; consuming that signal starts a new pass);
* `halt X`: stop with output `X`. -/
inductive StreamAction (n : ℕ) where
  | query : Fin 2 → Finset (Fin n) → (Bool → List (Cell n)) → StreamAction n
  | consume : List (Cell n) → StreamAction n
  | halt : Finset (Fin n) → StreamAction n

namespace StreamAction

variable {n : ℕ}

/-- Rename every element occurring in an action by the permutation `τ`. -/
def relabel (τ : Equiv.Perm (Fin n)) : StreamAction n → StreamAction n
  | query i S k => query i (S.map τ.toEmbedding) (fun b => (k b).map (Cell.relabel τ))
  | consume m => consume (m.map (Cell.relabel τ))
  | halt X => halt (X.map τ.toEmbedding)

end StreamAction

/-- **Deterministic multi-pass semi-streaming algorithms with independence oracles.**
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), §6.1, p.30: "In the multi-pass streaming
model, the elements of the input arrive one by one as a stream, and an algorithm may read the
stream several times. Each reading of the stream is called a pass. … In the semi-streaming
setting of the matroid intersection problem, the elements of the ground set E arrive one by one
as a stream. The algorithm has access to independence oracles for M1 and M2, which can be queried
only on subsets of the elements stored in memory." Footnote 3, p.5: space is the number of
machine words.

A `StreamAlg n` (for the ground set `[n]`) is an initial memory `init` and a transition rule
`step`: given the current memory (a list of words) and the arriving element (`some e`, or `none`
for the end-of-pass signal), it chooses a `StreamAction`.

**Formalization Note.** The paper names no instruction set. This is the query-complexity
convention of §2.1 (computation is free, oracle calls are counted) with the space and access
restrictions of §6.1: the algorithm remembers nothing but its memory, which is measured at every
micro-step (so working memory is charged too). The restriction of queries to stored elements,
and the opacity of elements, are the separate predicate `StreamAlg.IsLegal`. -/
structure StreamAlg (n : ℕ) where
  /-- The memory before the first element arrives. -/
  init : List (Cell n)
  /-- The action taken in memory `m` while the element `x` arrives (`none`: end of pass). -/
  step : List (Cell n) → Option (Fin n) → StreamAction n

/-- A configuration of a run: the memory, the position in the stream (equal to the stream's
length while the end-of-pass signal is pending), the number of passes started, the number of
oracle queries made, and the output once the algorithm has halted. -/
structure StreamConfig (n : ℕ) where
  mem : List (Cell n)
  pos : ℕ
  passes : ℕ
  queries : ℕ
  out : Option (Finset (Fin n))

namespace StreamAlg

variable {n : ℕ}

/-- The start of a run: initial memory, first pass started, nothing queried, not halted. -/
def start (A : StreamAlg n) : StreamConfig n :=
  ⟨A.init, 0, 1, 0, none⟩

/-- One micro-step of the run of `A` on the stream `σ` with oracle answers `O`
(`O i S = true` meaning "`S` is independent in `M_{i+1}`"). A halted configuration is fixed. -/
def next (A : StreamAlg n) (O : Fin 2 → Finset (Fin n) → Bool) (σ : List (Fin n))
    (c : StreamConfig n) : StreamConfig n :=
  match c.out with
  | some _ => c
  | none =>
    match A.step c.mem σ[c.pos]? with
    | .query i S k => { c with mem := k (O i S), queries := c.queries + 1 }
    | .consume m =>
      if c.pos < σ.length then { c with mem := m, pos := c.pos + 1 }
      else { c with mem := m, pos := 0, passes := c.passes + 1 }
    | .halt X => { c with out := some X }

/-- The configuration after `t` micro-steps of the run of `A` on the stream `σ` (the same order
in every pass) with oracle answers `O`. -/
def config (A : StreamAlg n) (O : Fin 2 → Finset (Fin n) → Bool) (σ : List (Fin n)) :
    ℕ → StreamConfig n
  | 0 => A.start
  | t + 1 => A.next O σ (A.config O σ t)

end StreamAlg

end AuctionMatroidInt.Supplement


