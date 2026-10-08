-- Prove2me | Definitions.Def_SnakyConditional
-- name    : SnakyConditional
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:23.549492+00:00
-- url     : https://prove2.me/theorems/8b0d52e9-d2d9-4a88-a838-f5c7b7e5ee3d
-- statement:
--   Cells are integer lattice points ℤ×ℤ, and snaky is the six-cell shape {(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}. For each r in Fin 8, orient r is one of eight explicit coordinate maps on a cell (x,y): (x,y), (y,x), (x,−y), (−y,x), (−x,y), (y,−x), (−x,−y), (−y,−x) for r=0,…,7 respectively, and placement r t p applies orient r to p and then translates by t. HasSnaky(M) is the proposition that a finite set M of cells contains some placed copy of snaky, meaning there exist r and a translation t such that the image of snaky under placement r t is a subset of M. In the OrdinaryStrategy namespace, for a type α with decidable equality, a Policy is a function taking a natural number, a finite set of maker elements and a finite set of breaker elements, and returning an element of α. Given a policy σ, a horizon N, a breaker sequence β : ℕ → α and starting sets M₀ and B₀, playState gives the pair of sets after k rounds: round k+1 inserts into the maker set the element σ(N−k, current maker set, current breaker set), and inserts β k into the breaker set. makerAt is the maker's move at round k, and LegalRepliesBeforeFinal says that for every k with k+1<N, the breaker's choice β k is neither in the maker set after that round's maker move is added nor in the breaker set before round k. No theorem is stated; these are only definitions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyConditional.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SnakyConditional.lean; bytes 16..1454
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI.SnakyConditional

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

namespace OrdinaryStrategy

variable {α : Type*} [DecidableEq α]

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
end OrdinaryStrategy

open OrdinaryStrategy



end OAI.SnakyConditional


