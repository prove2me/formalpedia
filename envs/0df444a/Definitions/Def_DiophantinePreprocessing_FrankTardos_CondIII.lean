-- Prove2me | Definitions.Def_DiophantinePreprocessing_FrankTardos_CondIII
-- name    : DiophantinePreprocessing_FrankTardos_CondIII
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:39:15.956079+00:00
-- url     : https://prove2.me/theorems/e018f078-51c5-49e8-8fd9-31579e58b374
-- title:
--   Sup norm of an integer vector and condition (iii) of the decomposition
-- statement:
--   For an integer vector $v = (v(1), \dots, v(n)) \in \mathbb{Z}^n$ write
--   $$\|v\|_\infty = \max_{1 \le j \le n} |v(j)|,$$
--   with the convention $\|v\|_\infty = 0$ when $n = 0$.
--
--   Let $N$ and $k$ be natural numbers, let $\lambda_1, \dots, \lambda_k$ be real numbers and $v_1, \dots, v_k \in \mathbb{Z}^n$ integer vectors. The family satisfies **condition (iii)** (with the integer $N$) if for every $i = 2, \dots, k$ the vector $v_i$ is nonzero and
--   $$\frac{\lambda_i}{\lambda_{i-1}} \le \frac{1}{N \, \|v_i\|_\infty}.$$
--
--   Condition (iii) says that the coefficients of a decomposition $w = \sum_{i=1}^k \lambda_i v_i$ decrease so fast that each term is negligible against the previous one when $w$ is tested against a small integer vector. It is shared by Theorem 3.1, Lemma 3.2 and Theorem 3.3 of the paper.
--
--   **Formalization Note** Indices are natural numbers and only $i \in \{1, \dots, k\}$ matter; $\lambda$ and $v$ are functions on $\mathbb{N}$. The quotient inequality is written multiplicatively, $\lambda_i \cdot N \cdot \|v_i\|_\infty \le \lambda_{i-1}$, together with $v_i \ne 0$, which the page presupposes by dividing by $\|v_i\|_\infty$; for positive $\lambda$ and $N \ge 1$ the two forms are equivalent. $\|v\|_\infty$ is `supNorm v`, a natural number.
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), p. 53, Theorem 3.1 condition (iii); norm notation p. 50

import Mathlib

namespace DiophantinePreprocessing.FrankTardos

/-- The ℓ∞ norm `‖v‖∞ = max_j |v(j)|` of an integer vector, as a natural number
(it is `0` for the zero vector and for `n = 0`). -/
def supNorm {n : ℕ} (v : Fin n → ℤ) : ℕ :=
  Finset.univ.sup (fun j => (v j).natAbs)

/-- Condition (iii) of Frank–Tardos, Theorem 3.1, for a decomposition `w = ∑_{i=1}^k λ_i v_i`
indexed by `i = 1, …, k`: for `i = 2, …, k` the vector `v_i` is nonzero and
`λ_i / λ_{i-1} ≤ 1 / (N ‖v_i‖∞)`, written multiplicatively as `λ_i · N · ‖v_i‖∞ ≤ λ_{i-1}`. -/
def CondIII {n : ℕ} (N k : ℕ) (lam : ℕ → ℝ) (v : ℕ → Fin n → ℤ) : Prop :=
  ∀ i ∈ Finset.Icc 2 k, v i ≠ 0 ∧ lam i * ((N : ℝ) * (supNorm (v i) : ℝ)) ≤ lam (i - 1)

end DiophantinePreprocessing.FrankTardos


