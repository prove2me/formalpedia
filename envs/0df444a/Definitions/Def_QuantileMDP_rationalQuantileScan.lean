-- Prove2me | Definitions.Def_QuantileMDP_rationalQuantileScan
-- name    : QuantileMDP_rationalQuantileScan
-- status  : Definition
-- author  : @shuffle
-- created : 2026-11-14T03:01:23.275018+00:00
-- url     : https://prove2.me/theorems/d775e42d-3fa5-4262-858d-5e592cb3361d
-- title:
--   An executable rational threshold scan for quantile MDPs
-- statement:
--   Evaluate a finite integer grid using exact rational arithmetic and finite action minima. Lower tails are open at level zero and closed at positive levels.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §4, pp. 16–19. https://arxiv.org/abs/1711.05788v5

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Definitions.Def_QuantileMDP_Model

namespace QuantileMDP

/-- With rational transition probabilities, this integer-threshold
recursion uses only rational arithmetic and finite action minima. -/
def rationalTail {S A : Type*} [Fintype S] (actions : ℕ → S → Finset A)
    (hne : ∀ t s, (actions t s).Nonempty) (p : ℕ → S → A → S → ℚ)
    (r : ℕ → S → A → S → ℤ) (closed : Bool) : ℕ → ℕ → S → ℤ → ℚ
  | 0, _, _, x => if (if closed then 0 ≤ x else 0 < x) then 1 else 0
  | n + 1, t, s, x => (actions t s).inf' (hne t s) (fun a =>
      ∑ i, p t s a i * rationalTail actions hne p r closed n (t + 1) i (x - r t s a i))

def integerGrid (B : ℕ) : Finset ℤ :=
  (Finset.range (2 * B + 1)).image (fun k : ℕ => (k : ℤ) - (B : ℤ))

def maxOption {α : Type*} [LinearOrder α] (s : Finset α) : Option α := s.max
def minOption {α : Type*} [LinearOrder α] (s : Finset α) : Option α := s.min

/-- A finite scan using exact rational comparisons. Nonempty output is
proved for valid probability levels and bounded integer rewards. -/
def rationalQuantileScan {S A : Type*} [Fintype S] (actions : ℕ → S → Finset A)
    (hne : ∀ t s, (actions t s).Nonempty) (p : ℕ → S → A → S → ℚ)
    (r : ℕ → S → A → S → ℤ) (R T : ℕ) (s : S) (τ : ℚ) : Option ℤ :=
  let I := integerGrid (T * R)
  if τ = 0 then
    maxOption (I.filter fun y => rationalTail actions hne p r false T 0 s y = 0)
  else
    minOption (I.filter fun y => τ ≤ rationalTail actions hne p r true T 0 s y)

end QuantileMDP


