-- Prove2me | Definitions.Def_LimitedBFGS_SQN_pcgPairs
-- name    : LimitedBFGS_SQN_pcgPairs
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-28T20:49:35.722921+00:00
-- url     : https://prove2.me/theorems/b27f5aba-2edf-47f1-8eea-ae9dd8d555b4
-- title:
--   The window of PCG correction pairs stored by the limited-storage BFGS iteration
-- statement:
--   Let $x_k$ be the iterates of the preconditioned conjugate gradient method with fixed preconditioner $H_0$ applied to $f(x) = \tfrac12 x^\top A x + b^\top x$ with exact line searches, and let $g_k = A x_k + b$.
--
--   `pcgPair A b H₀ x₀ k` is the pair $(s_k, y_k) = (x_{k+1} - x_k,\; g_{k+1} - g_k)$: the secant pair that the limited-storage BFGS iteration stores after its step from $x_k$.
--
--   `pcgPairs A b H₀ x₀ m k` is the list of the most recent `m` such pairs, `pcgPair … (k − min(k,m))` up to `pcgPair … (k −1)`, oldest first. It is defined by exactly the update rule of Nocedal's iteration (17): start empty at `k = 0`, and at each step append the new pair and then drop the oldest entries until at most `m` remain. Using this recursive form rather than a closed formula in `min k m` keeps the term definitionally equal to the state component of `sqnIter`.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 778, iteration (17).

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- The consecutive difference pair of the PCG iteration at index `k`: `s_k = x_{k+1} − x_k`
and `y_k = g_{k+1} − g_k`, the pair that iteration (17) stores after the step from `x_k`. -/
noncomputable def pcgPair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (k : ℕ) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  ((pcgIter A b H₀ x₀ (k + 1)).x - (pcgIter A b H₀ x₀ k).x,
   grad A b (pcgIter A b H₀ x₀ (k + 1)).x - grad A b (pcgIter A b H₀ x₀ k).x)

/-- The window of PCG correction pairs retained after `m` steps of limited storage: the pairs
`(s_j, y_j)` for `j = k − min(k, m), …, k − 1`, oldest first. The recursive presentation
is *identical* to the update performed by `sqnIter` (Nocedal 1980, p. 778, iteration (17)):
the new pair is appended and the oldest entries are dropped once more than `m` are stored. -/
noncomputable def pcgPairs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (m : ℕ) :
    ℕ → List ((Fin n → ℝ) × (Fin n → ℝ))
  | 0 => []
  | k + 1 =>
    let ps := pcgPairs A b H₀ x₀ m k ++ [pcgPair A b H₀ x₀ k]
    ps.drop (ps.length - m)

end LimitedBFGS.SQN


