-- Prove2me | Definitions.Def_AzumaWeightedSums_StrongLaw_ReversedSum
-- name    : AzumaWeightedSums_StrongLaw_ReversedSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:48:42.619816+00:00
-- url     : https://prove2.me/theorems/ff78dba1-3bd5-4667-8538-34fcbf3fd032
-- title:
--   Weight partial sums $A_n$ and reversed weighted sums $\bar S_n = a_n x_1 + \dots + a_1 x_n$
-- statement:
--   Let $(a_n)_{n\ge1}$ be a sequence of real weights and $(x_n)_{n\ge1}$ a sequence of real random variables. Put
--
--   $$A_n = a_1 + a_2 + \dots + a_n, \qquad \bar S_n = a_n x_1 + a_{n-1} x_2 + \dots + a_1 x_n = \sum_{j=1}^{n} a_{n-j+1}\, x_j,$$
--
--   with $A_0 = 0$ and $\bar S_0 = 0$. In $\bar S_n$ the weights are applied in reverse order: the earliest variable $x_1$ receives the newest weight $a_n$ and the newest variable $x_n$ receives $a_1$. Consequently $(\bar S_n)$ is in general not a martingale in $n$, which is what distinguishes Azuma's Theorem 3 from the strong law for the direct sums $a_1x_1+\dots+a_nx_n$.
--
--   For example, $\bar S_2 = a_2 x_1 + a_1 x_2$ and $\bar S_3 = a_3x_1 + a_2x_2 + a_1x_3$.
--
--   **Formalization Note** Indices start at $1$ (sums over $\{1,\dots,n\}$); $a_0$ and $x_0$ are never used. The weight index $n+1-j$ is a natural-number subtraction, exact because $j\le n$ in the sum.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 362, §4 (definition of S̄_n); p. 363, Corollary 3 (definition of A_n)

import Mathlib

namespace AzumaWeightedSums.StrongLaw

/-- The partial sums of the weights, `A_n = a_1 + a_2 + ⋯ + a_n` (Azuma 1967, Corollary 3,
p. 363); `A_0 = 0`. Indices are 1-based; `a 0` is never used. -/
def A (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, a j

/-- The reversed weighted sum `S̄_n = a_n x_1 + a_{n-1} x_2 + ⋯ + a_1 x_n`
(Azuma 1967, §4, p. 362), i.e. `S̄_n = ∑_{j=1}^n a_{n-j+1} x_j`; `S̄_0 = 0`.
The natural-number subtraction `n + 1 - j` is exact because `j ≤ n`. -/
def Sbar {Ω : Type*} (a : ℕ → ℝ) (x : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, a (n + 1 - j) * x j ω

end AzumaWeightedSums.StrongLaw


