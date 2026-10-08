-- Prove2me | Definitions.Def_EntangledGames
-- name    : EntangledGames
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:09.948981+00:00
-- url     : https://prove2.me/theorems/37a8afa2-1eec-4607-b148-25824f91bf16
-- statement:
--   A two-player game with natural-number parameters x, y, a, b has x+1 and y+1 possible questions and a+1 and b+1 possible answers, a nonnegative probability distribution of total mass one on question pairs, and a Boolean acceptance rule. A quantum strategy for arbitrary question types and finite answer types consists of two positive finite-dimensional complex local spaces, a unit vector ψ on their tensor product, and, for each local question, positive semidefinite measurement matrices indexed by answers and summing to the identity. Its Born probability for answers a and b to questions x and y is the real part of ⟨ψ,(Aₓₐ ⊗ Bᵧᵦ)ψ⟩, expressed as a finite coordinate sum. The success probability averages these Born probabilities over accepted answer pairs and the question distribution; the entangled value ω*(G) is the supremum of this success probability over all such strategies, with no fixed dimension bound. For any natural number k, a repeated strategy receives complete k-tuples of questions and returns complete k-tuples of answers, so its measurements may depend jointly on all local questions. The number of wins counts the coordinates accepted by the original game. For any real δ, the threshold probability averages the repeated strategy’s Born probabilities for obtaining at least ⌈(ω*(G)+δ)k⌉₊ wins, with question pairs sampled independently from the original distribution. Here the natural-number ceiling rounds upward and truncates negative values to zero. The threshold value is the supremum of this probability over all repeated strategies. These definitions allow k=0 and impose no restriction on δ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EntangledGames.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EntangledGames.lean; bytes 16..2556
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace ThresholdParallelRepetition

structure Game (x y a b : ℕ) where
  questionProb : Fin (x + 1) × Fin (y + 1) → ℝ
  questionProb_nonneg : ∀ z, 0 ≤ questionProb z
  questionProb_sum : ∑ z, questionProb z = 1
  accepts : Fin (x + 1) → Fin (y + 1) → Fin (a + 1) → Fin (b + 1) → Bool

structure Strategy (X Y A B : Type) [Fintype A] [Fintype B] where
  dimA : ℕ
  dimB : ℕ
  state : Fin (dimA + 1) × Fin (dimB + 1) → ℂ
  state_unit : ∑ i, Complex.normSq (state i) = 1
  alice : X → A → Matrix (Fin (dimA + 1)) (Fin (dimA + 1)) ℂ
  bob : Y → B → Matrix (Fin (dimB + 1)) (Fin (dimB + 1)) ℂ
  alice_pos : ∀ x a, (alice x a).PosSemidef
  bob_pos : ∀ y b, (bob y b).PosSemidef
  alice_total : ∀ x, ∑ a, alice x a = 1
  bob_total : ∀ y, ∑ b, bob y b = 1

def Strategy.born {X Y A B : Type} [Fintype A] [Fintype B]
    (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  ∑ i, ∑ j, (star (S.state i) *
    (S.alice x a i.1 j.1 * S.bob y b i.2 j.2) * S.state j).re

abbrev SingleStrategy (x y a b : ℕ) :=
  Strategy (Fin (x + 1)) (Fin (y + 1)) (Fin (a + 1)) (Fin (b + 1))

def successProbability {x y a b : ℕ} (G : Game x y a b) (S : SingleStrategy x y a b) : ℝ :=
  ∑ z : Fin (x + 1) × Fin (y + 1), G.questionProb z *
    ∑ w : Fin (a + 1) × Fin (b + 1),
      if G.accepts z.1 z.2 w.1 w.2 then S.born z.1 z.2 w.1 w.2 else 0

def entangledValue {x y a b : ℕ} (G : Game x y a b) : ℝ :=
  sSup (Set.range (successProbability G))

abbrev RepeatedStrategy (x y a b k : ℕ) :=
  Strategy (Fin k → Fin (x + 1)) (Fin k → Fin (y + 1))
    (Fin k → Fin (a + 1)) (Fin k → Fin (b + 1))

def wins {x y a b k : ℕ} (G : Game x y a b)
    (xs : Fin k → Fin (x + 1)) (ys : Fin k → Fin (y + 1))
    (as : Fin k → Fin (a + 1)) (bs : Fin k → Fin (b + 1)) : ℕ :=
  ∑ i, if G.accepts (xs i) (ys i) (as i) (bs i) then 1 else 0

def thresholdProbability {x y a b k : ℕ} (G : Game x y a b) (δ : ℝ)
    (S : RepeatedStrategy x y a b k) : ℝ :=
  ∑ xs : Fin k → Fin (x + 1), ∑ ys : Fin k → Fin (y + 1),
    (∏ i, G.questionProb (xs i, ys i)) *
      ∑ as : Fin k → Fin (a + 1), ∑ bs : Fin k → Fin (b + 1),
        if ⌈(entangledValue G + δ) * (k : ℝ)⌉₊ ≤ wins G xs ys as bs
        then S.born xs ys as bs else 0

def thresholdValue {x y a b k : ℕ} (G : Game x y a b) (δ : ℝ) : ℝ :=
  sSup (Set.range (thresholdProbability (k := k) G δ))



end ThresholdParallelRepetition
end
end OAI


