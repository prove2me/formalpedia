-- Prove2me | Definitions.Def_SyncPrefix_Huffman_Automata
-- name    : SyncPrefix_Huffman_Automata
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:29.810068+00:00
-- url     : https://prove2.me/theorems/eb0e642b-e332-462b-b5e3-06d5cf5bba6f
-- title:
--   §2, pp. 2–3 — complete automata, synchronizing words and their shortest length, strongly acyclic automata, Huffman decoders, the instance encoding
-- statement:
--   This file fixes the automata of Ryzhikov and Szykuła's paper.
--
--   A **complete deterministic automaton** is a transition function $\delta : Q \times \Sigma \to Q$ on a set of states $Q$ and an alphabet $\Sigma$; there is no initial or final state. It extends to words by $\delta(q, \varepsilon) = q$ and $\delta(q, wx) = \delta(\delta(q, w), x)$.
--
--   1. A word $w$ is **synchronizing** if there is a state $q$ with $\delta(q', w) = q$ for every state $q'$; the automaton is **synchronizing** if it has a synchronizing word, and $\ell(\delta)$ denotes the length of a shortest one.
--   2. A state $q$ is a **sink** if $\delta(q, a) = q$ for every letter $a$. The automaton is **strongly acyclic** if every cycle is a self-loop (a run that returns to a state $q$ never visits another state) and every state with a self-loop is a sink.
--   3. The automaton is **strongly connected** if every ordered pair of states is joined by a word. A **first-return word** of a state $r$ is a nonempty word $w$ with $\delta(r, w) = r$ such that no nonempty proper prefix $u$ of $w$ has $\delta(r, u) = r$.
--   4. A **Huffman decoder** is a strongly connected complete automaton with a state $r$ whose set of first-return words is finite. That set is then a finite maximal prefix code, the code the automaton decodes.
--
--   The input of the problem Short Sync Word is an automaton with states $\{0, \dots, n-1\}$ and letters $\{0, \dots, k-1\}$, written over a three-letter alphabet as $n$ in unary, a separator, $k$ in unary, a separator, and then, for each state $q$ and each letter $a$ in increasing order, the value $\delta(q, a)$ in unary followed by a separator. The code has length polynomial in $n$ and $k$ and determines the automaton.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** States and letters are arbitrary types in the generic definitions, and `Fin n`, `Fin k` for instances. `syncLength` is defined as an infimum over the lengths of synchronizing words, so it is `0` (a junk value) for a non-synchronizing automaton; every statement assumes or proves synchronization. The unary encoding uses `some true` for a unary digit and `none` as the separator.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, pp. 2–3, §2 (automata, strongly connected, simple cycles, self-loops, sink states, strongly acyclic, first return words, Huffman decoders, synchronizing words, the problem Short Sync Word)

import Mathlib

namespace SyncPrefix.Huffman

/-! Complete deterministic automata, synchronizing words, strongly acyclic automata and Huffman
decoders (Ryzhikov–Szykuła, arXiv:1806.06299v1, §2, pp. 2–3). An automaton is given by its
transition function `δ : σ → α → σ` (states `σ`, letters `α`); there is no initial or final state. -/

section Generic

variable {σ α : Type}

/-- The extended transition function: `run δ q w = δ(q, w)`, with `δ(q, wx) = δ(δ(q, w), x)`. -/
def run (δ : σ → α → σ) (q : σ) (w : List α) : σ := w.foldl δ q

/-- `w` is a synchronizing word: it maps every state to one and the same state `q`. -/
def IsSyncWord (δ : σ → α → σ) (w : List α) : Prop := ∃ q, ∀ q', run δ q' w = q

/-- The automaton is synchronizing: it has a synchronizing word. -/
def IsSynchronizing (δ : σ → α → σ) : Prop := ∃ w, IsSyncWord δ w

/-- The length of a shortest synchronizing word. Junk value `0` when `δ` is not synchronizing
(`sInf ∅ = 0`); every statement assumes or proves `IsSynchronizing δ`. -/
noncomputable def syncLength (δ : σ → α → σ) : ℕ :=
  sInf {ℓ | ∃ w : List α, w.length = ℓ ∧ IsSyncWord δ w}

/-- A sink state: every letter maps it to itself. -/
def IsSink (δ : σ → α → σ) (q : σ) : Prop := ∀ a, δ q a = q

/-- Strongly acyclic (p. 3): every cycle is a self-loop (a run that returns to `q` never leaves
`q`), and every state with a self-loop is a sink state. -/
def StronglyAcyclic (δ : σ → α → σ) : Prop :=
  (∀ q w, run δ q w = q → ∀ i ≤ w.length, run δ q (w.take i) = q) ∧
    (∀ q a, δ q a = q → IsSink δ q)

/-- Strongly connected: every ordered pair of states is joined by a word. -/
def StronglyConnected (δ : σ → α → σ) : Prop := ∀ q q', ∃ w, run δ q w = q'

/-- `w` is a first-return word of `r`: nonempty, maps `r` to `r`, and no nonempty proper prefix
maps `r` to `r`. -/
def IsFirstReturn (δ : σ → α → σ) (r : σ) (w : List α) : Prop :=
  w ≠ [] ∧ run δ r w = r ∧ ∀ i, 0 < i → i < w.length → run δ r (w.take i) ≠ r

/-- A Huffman decoder (p. 3): a strongly connected complete automaton with a state `r` whose set
of first-return words is finite (that set is then a finite maximal prefix code). -/
def IsHuffmanDecoder (δ : σ → α → σ) : Prop :=
  StronglyConnected δ ∧ ∃ r, {w | IsFirstReturn δ r w}.Finite

end Generic

/-- An instance of Short Sync Word restricted to complete automata: `n` states `Fin n`,
`k` letters `Fin k`, and the transition table `δ`. -/
structure Automaton where
  n : ℕ
  k : ℕ
  δ : Fin n → Fin k → Fin n

/-- Encoding over `Option Bool`: `n` in unary (`some true`), a separator `none`, `k` in unary,
`none`, then for each state `q` and each letter `a` (in increasing order) the value `δ q a` in
unary followed by `none`. -/
def Automaton.encode (A : Automaton) : List (Option Bool) :=
  List.replicate A.n (some true) ++ none :: List.replicate A.k (some true) ++ none ::
    (List.finRange A.n).flatMap fun q =>
      (List.finRange A.k).flatMap fun a => List.replicate (A.δ q a).val (some true) ++ [none]

end SyncPrefix.Huffman


