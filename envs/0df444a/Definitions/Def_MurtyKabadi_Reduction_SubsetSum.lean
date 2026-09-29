-- Prove2me | Definitions.Def_MurtyKabadi_Reduction_SubsetSum
-- name    : MurtyKabadi_Reduction_SubsetSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:12:47.481751+00:00
-- url     : https://prove2.me/theorems/541fd730-46e8-405f-a8ec-67022467c718
-- title:
--   The subset sum problem (Problem 5) and its size $l$ (p. 123)
-- statement:
--   The data of a subset sum instance are positive integers $d_0;\ d_1, \dots, d_n$. The instance is **solvable** (Problem 5 has answer "yes") if there is an integer vector $y = (y_j) \in \mathbb Z^n$ with
--   $$\sum_{j=1}^n d_j y_j = d_0, \qquad 0 \le y_j \le 1,\ j = 1, \dots, n,$$
--   that is, if some subset of $\{d_1, \dots, d_n\}$ sums to $d_0$.
--
--   The **size** $l$ of the instance is the total number of digits in all the data $d_0, d_1, \dots, d_n$, counted in decimal:
--   $$l = \#\text{digits}(d_0) + \sum_{j=1}^n \#\text{digits}(d_j).$$
--   It fixes the precision $\varepsilon < 2^{-nl^2}$ of the reduction.
--
--   **Formalization Note** The data are natural numbers; their positivity is a hypothesis of the theorems that use them. The digit count is `(Nat.digits 10 a).length`, which is the usual number of decimal digits for $a \ge 1$. The paper says "digits" without a base; decimal is the literal reading and gives the smaller $l$, hence the larger admissible $\varepsilon$.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 123, Problem 5 and the definition of l

import Mathlib

namespace MurtyKabadi.Reduction

/-- Problem 5, the subset sum problem (p. 123): with data `d₀; d₁, …, d_n`, is there an integer
vector `y` with `∑ d_j y_j = d₀` and `0 ≤ y_j ≤ 1` for all `j`? -/
def SubsetSumSolvable {n : ℕ} (d : Fin n → ℕ) (d0 : ℕ) : Prop :=
  ∃ y : Fin n → ℤ, (∀ j, 0 ≤ y j ∧ y j ≤ 1) ∧ ∑ j, (d j : ℤ) * y j = d0

/-- The size `l` of the subset sum instance (p. 123): the total number of (decimal) digits in
all the data `d₀, d₁, …, d_n`. -/
def digitCount {n : ℕ} (d : Fin n → ℕ) (d0 : ℕ) : ℕ :=
  (Nat.digits 10 d0).length + ∑ j, (Nat.digits 10 (d j)).length

end MurtyKabadi.Reduction


