-- Prove2me | Definitions.Def_XorParallelRepetition_Exponential_Contradiction
-- name    : XorParallelRepetition_Exponential_Contradiction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:07.700061+00:00
-- url     : https://prove2.me/theorems/4b0b3fef-ea05-40d7-81ea-347e5cf98cea
-- title:
--   Definitions 2.2 and 3.2 — ordered contradictions, reading sequences and $H_N$
-- statement:
--   Let $\Psi$ be a generalized XOR game. An **ordered contradiction of length $N$** is a sequence of supported challenges $(e_1,t_1),\dots,(e_N,t_N)$ and signs $s_1,\dots,s_N\in\{-1,1\}$ such that
--
--   1. $\prod_{j=1}^{N}\omega_p^{s_jt_j}\ne1$;
--   2. for each player $i$, writing $v_{i,j}$ for the question of player $i$ in $e_j$, the formal word $\prod_{j=1}^{N}v_{i,j}^{s_j}$ reduces to the empty word by canceling a symbol with an adjacent inverse of itself.
--
--   The cancellation is free reduction: the order of the letters matters, and a symbol is never its own inverse, also for $p=2$.
--
--   The **reading sequence** of player $i$ is $h_i=(h_i(0),\dots,h_i(N))$, where $h_i(j)$ is the number of symbols that remain after the first $j$ letters have been read with cancellation. For an ordered contradiction $R$, let $\max_ih_i$ be the maximum in the lexicographic order, and the all-zero sequence if there are no players. For a game that has an ordered contradiction of length $N$,
--
--   $$
--   H_N(\Psi)=\min_{R\in\mathcal R_N}\ \max_i h_i ,
--   $$
--
--   where $\mathcal R_N$ is the collection of all ordered contradictions of length $N$ and the minimum is lexicographic.
--
--   The parameter $H_N$ is the quantity that strictly decreases under gluing (Lemma 3.3).
--
--   **Formalization Note** Signs are booleans, `true` for $+1$. Cancellation is `FreeGroup.Red`. The stack obtained by reading a prefix with cancellation is the reduced form of that prefix, so $h_i(j)$ is written as the length of `FreeGroup.reduce` of the prefix. `heightParam` takes the existence of an ordered contradiction as an argument, so it has no value on a game without one; the minimum exists since the lexicographic order on $\mathbb N^{N+1}$ is a well order.
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Definition 2.2, printed p. 9, PDF p. 9; §3.2 and Definition 3.2, printed p. 11, PDF p. 11

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames

/-!
# Ordered contradictions, reading sequences and the parameter `H_N`

Source: Braverman and Minzer, STOC 2027 submission #195, Definition 2.2 (printed/PDF p. 9) and
§3.2, Definition 3.2 (p. 11).
-/

namespace XorParallelRepetition.Exponential

universe u

variable {p : ℕ} {ι : Type}

/-- The field element `±1` of a sign; `true` is `+1` and `false` is `-1`. -/
def signValue (p : ℕ) (s : Bool) : ZMod p :=
  if s then 1 else -1

/-- The signed word of a player: the letter at position `j` is the question `q j` with exponent
`+1` when `s j = true` and `-1` when `s j = false`. -/
def signedWord {α : Type*} {N : ℕ} (q : Fin N → α) (s : Fin N → Bool) : List (α × Bool) :=
  List.ofFn fun j => (q j, s j)

/-- An ordered contradiction of length `N` for `Ψ` (Definition 2.2): supported challenges and
signs such that `∏_j ω_p^{s_j t_j} ≠ 1`, and such that for each player the signed word of its
questions reduces to the empty word by canceling adjacent inverse letters.  The cancellation is
the free reduction of `FreeGroup.Red`: order matters, and a letter is the inverse of another only
if it is the same symbol with the opposite sign. -/
structure OrderedContradiction (Ψ : GeneralizedXorGame.{u} p ι) (N : ℕ) where
  /-- The challenges `(e_j, t_j)`. -/
  challenge : Fin N → (∀ i, Ψ.Q i) × ZMod p
  /-- The signs `s_j`. -/
  sign : Fin N → Bool
  /-- Every challenge is supported. -/
  mem_support : ∀ j, challenge j ∈ Ψ.μ.support
  /-- The right hand side does not trivialize. -/
  rhs_ne_one : ∏ j, phase p (signValue p (sign j) * (challenge j).2) ≠ 1
  /-- The left hand side trivializes combinatorially. -/
  word_cancels : ∀ i, FreeGroup.Red (signedWord (fun j => (challenge j).1 i) sign) []

/-- `Ψ` has an ordered contradiction of length `N`. -/
def HasOrderedContradiction (Ψ : GeneralizedXorGame.{u} p ι) (N : ℕ) : Prop :=
  Nonempty (OrderedContradiction Ψ N)

open Classical in
/-- The reading sequence `h_i = (h_i(0), …, h_i(N))` of player `i` (§3.2): `h_i(j)` is the number
of symbols remaining after the first `j` symbols of its word are read with adjacent inverse
letters canceled, that is the length of the reduced form of the prefix of length `j`.  It is an
element of the lexicographically ordered type of sequences. -/
noncomputable def OrderedContradiction.readingSeq {Ψ : GeneralizedXorGame.{u} p ι} {N : ℕ}
    (R : OrderedContradiction Ψ N) (i : ι) : Lex (Fin (N + 1) → ℕ) :=
  toLex fun j =>
    (FreeGroup.reduce ((signedWord (fun j => (R.challenge j).1 i) R.sign).take j)).length

/-- The lexicographic maximum over players of the reading sequences, with the all-zero sequence
when there are no players. -/
noncomputable def OrderedContradiction.maxReadingSeq [Fintype ι]
    {Ψ : GeneralizedXorGame.{u} p ι} {N : ℕ} (R : OrderedContradiction Ψ N) :
    Lex (Fin (N + 1) → ℕ) :=
  if h : (Finset.univ : Finset ι).Nonempty then Finset.univ.sup' h R.readingSeq
  else toLex fun _ => 0

/-- `H_N(Ψ)` (Definition 3.2), for a game that has an ordered contradiction of length `N`: the
lexicographic minimum, over all such contradictions, of the maximal reading sequence.  The
minimum exists because the lexicographic order on sequences of naturals of a fixed length is a
well order and the candidate set is non-empty by hypothesis.  With no players every candidate is
the all-zero sequence, so `H_N(Ψ) = (0, …, 0)`. -/
noncomputable def heightParam [Fintype ι] (Ψ : GeneralizedXorGame.{u} p ι) (N : ℕ)
    (h : HasOrderedContradiction Ψ N) : Lex (Fin (N + 1) → ℕ) :=
  (wellFounded_lt (α := Lex (Fin (N + 1) → ℕ))).min
    (Set.range fun R : OrderedContradiction Ψ N => R.maxReadingSeq)
    (Set.range_nonempty_iff_nonempty.2 h)

end XorParallelRepetition.Exponential


