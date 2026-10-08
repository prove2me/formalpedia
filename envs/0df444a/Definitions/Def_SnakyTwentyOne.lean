-- Prove2me | Definitions.Def_SnakyTwentyOne
-- name    : SnakyTwentyOne
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:23.776554+00:00
-- url     : https://prove2.me/theorems/9aa200b0-5e32-4b9f-bc67-389947c5b047
-- statement:
--   The block sets up a prototype for a maker-breaker style game on the integer grid, together with an abstract strategy-play framework. Cells are pairs of integers, and snaky is the fixed six-cell shape {(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}. For each of eight indices r, orient r transforms a cell (x,y) by one of the eight maps (x,y), (y,x), (x,−y), (−y,x), (−x,y), (y,−x), (−x,−y), (−y,−x), and placement r t p is orient r p plus a translation t. HasSnaky(M) is the proposition that some orientation index r and translation t exist such that every cell of snaky, after being placed by r and t, lies in the finite set M. For an infinite type α with decidable equality, a Policy is a function taking a remaining-round count and two finite sets (the maker's and the breaker's chosen elements) and returning an element of α. Starting from initial sets M₀ and B₀, playState σ N β M₀ B₀ k gives the pair of sets after k rounds: in round k the maker adds the policy's choice σ(N−k) applied to the current sets, while the breaker adds β k, where β is a fixed sequence of breaker moves. makerAt gives the maker's move at round k. LegalRepliesBeforeFinal says that for every k with k+1<N, the breaker's move β k is neither the maker's new move at that round nor already in the maker's current set, and is not already in the breaker's current set. The block defines these notions only and states no theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyTwentyOne.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SnakyTwentyOne.lean; bytes 16..1586
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace SnakyPrototype
variable {α : Type*} [DecidableEq α]
abbrev Cell := ℤ × ℤ
def snaky : Finset Cell := {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}
def orient (r : Fin 8) (p : Cell) : Cell :=
  match r.val with
  | 0 => (p.1, p.2)
  | 1 => (p.2, p.1)
  | 2 => (p.1, -p.2)
  | 3 => (-p.2, p.1)
  | 4 => (-p.1, p.2)
  | 5 => (p.2, -p.1)
  | 6 => (-p.1, -p.2)
  | _ => (-p.2, -p.1)
def placement (r : Fin 8) (t p : Cell) : Cell := orient r p + t
def HasSnaky (M : Finset Cell) : Prop :=
  ∃ (r : Fin 8) (t : Cell), snaky.image (placement r t) ⊆ M
end SnakyPrototype
namespace SnakyPrototype.OrdinaryStrategy
variable {α : Type*} [DecidableEq α] [Infinite α]
abbrev Policy (α : Type*) := ℕ → Finset α → Finset α → α
def playState (σ : Policy α) (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) :
    ℕ → Finset α × Finset α
  | 0 => (M₀, B₀)
  | k + 1 =>
      let state := playState σ N β M₀ B₀ k
      (insert (σ (N - k) state.1 state.2) state.1, insert (β k) state.2)
def makerAt (σ : Policy α) (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) (k : ℕ) : α :=
  let state := playState σ N β M₀ B₀ k
  σ (N - k) state.1 state.2
def LegalRepliesBeforeFinal (σ : Policy α) (N : ℕ) (β : ℕ → α)
    (M₀ B₀ : Finset α) : Prop :=
  ∀ k, k + 1 < N →
    β k ∉ insert (makerAt σ N β M₀ B₀ k) (playState σ N β M₀ B₀ k).1 ∧
    β k ∉ (playState σ N β M₀ B₀ k).2
end SnakyPrototype.OrdinaryStrategy

namespace SnakyPrototype
open OrdinaryStrategy



end SnakyPrototype
end OAI


