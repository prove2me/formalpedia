-- Prove2me | Definitions.Def_SubSuperStoch_SubSpec_Setting
-- name    : SubSuperStoch_SubSpec_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:30:45.886973+00:00
-- url     : https://prove2.me/theorems/f0a7040d-315e-428d-941a-fd6726171e21
-- title:
--   §2.1–2.2, pp. 4–5 — row sums Λ_i, ‖·‖_∞, eigenvalues, sub-stochastic matrices (Definition 2.1), non-zero element chains
-- statement:
--   This file fixes the matrix notation of §2.1 of Shi, Zheng, Shao and Cheng and the two notions their spectral bounds are about.
--
--   Let $F=[f_{ij}]\in\mathbb R^{n\times n}$ be a real square matrix.
--
--   1. **Row sums.** $\Lambda_i[F]=\sum_{j=1}^n f_{ij}$ is the sum of the $i$th row of $F$.
--   2. **Infinite norm.** $\|F\|_\infty=\max\{\sum_{j=1}^n |f_{ij}| \mid i=1,\dots,n\}$ is the largest absolute row sum.
--   3. **Eigenvalues.** The eigenvalues of $F$ are taken in $\mathbb C$: they form the spectrum of $F$ regarded as a complex matrix. A bound $\rho(F)\le b$ on the spectral radius is the statement that $|\mu|\le b$ for every complex eigenvalue $\mu$ of $F$.
--   4. **Sub-stochastic matrices (Definition 2.1).** $F$ is sub-stochastic if it is nonnegative, $f_{ij}\ge 0$ for all $i,j$, and
--   $$\Lambda_i[F]\le 1\qquad (i=1,\dots,n).$$
--   5. **Non-zero element chains (Theorem 2.2).** For indices $i=i_0,i_1,\dots,i_L=k$, the chain
--   $$\mathcal C_{i\to k}:\ [F]_{k i_{r}},\ \dots,\ [F]_{i_2 i_1},\ [F]_{i_1 i}\qquad (L=r+1)$$
--   is a non-zero element chain if every listed entry $[F]_{i_{t+1} i_t}$ is non-zero and consecutive indices differ, $i_{t+1}\ne i_t$. Its number of elements is $|\mathcal C_{i\to k}|=L$. Each entry has the later index as its row and the earlier index as its column.
--
--   These objects are the vocabulary of Theorems 2.2 and 2.3, which bound the spectral radius of a sub-stochastic matrix strictly below $1$ in terms of its row sums, its smallest positive entry and the lengths of chains leading from rows of sum less than one to rows of sum one.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin n) ℝ` with 0-based indices (the paper's $1,\dots,n$). `normInf F` is the supremum over the rows of the absolute row sums; on `Fin n` with $n\ge 1$ it is the maximum, and it is $0$ when $n=0$. `specC F` is `spectrum ℂ` of the entrywise complexification of `F`, i.e. the set of complex roots of the characteristic polynomial. A chain is a function `c : ℕ → Fin n` with `c 0 = i`, `c L = k`; `IsChain F c L` asks `F (c (t+1)) (c t) ≠ 0` and `c (t+1) ≠ c t` for `t < L`; values of `c` beyond `L` play no role.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, pp. 4–5, §2.1 Matrix notations, Definition 2.1, Theorem 2.2 (non-zero element chains)

import Mathlib

namespace SubSuperStoch.SubSpec

open Matrix

/-- `Λ_i[F] = ∑_{j=1}^n f_ij`, the `i`th row sum of `F` (§2.1, p. 4). Indices are 0-based `Fin n`. -/
def rowSum {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∑ j, F i j

/-- `‖F‖_∞ = max_i ∑_j |f_ij|`, the infinite norm of `F` (§2.1, p. 4). For `n = 0` it is `0`. -/
noncomputable def normInf {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ i, ∑ j, |F i j|

/-- The eigenvalues of the real matrix `F`, as complex numbers: the spectrum of `F` viewed as a
complex matrix. `ρ(F) ≤ b` is stated as `∀ μ ∈ specC F, ‖μ‖ ≤ b`. -/
noncomputable def specC {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : Set ℂ :=
  spectrum ℂ (F.map (algebraMap ℝ ℂ))

/-- Definition 2.1 (p. 4): `F` is sub-stochastic if it is nonnegative and `Λ_i[F] ≤ 1` for every `i`. -/
def IsSubStochastic {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ F i j) ∧ ∀ i, rowSum F i ≤ 1

/-- Non-zero element chain (Theorem 2.2, p. 5). `IsChain F c L` says that the `L` entries
`[F]_{c(t+1) c(t)}`, `t < L`, are all non-zero and consecutive indices differ, `c(t+1) ≠ c(t)`.
With `c 0 = i`, `c L = k` this is the chain `C_{i→k} = [F]_{k i_r}, …, [F]_{i₂ i₁}, [F]_{i₁ i}`
(`i_t = c t`, `L = r + 1`), and `L = |C_{i→k}|` is its number of elements. -/
def IsChain {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (c : ℕ → Fin n) (L : ℕ) : Prop :=
  ∀ t, t < L → F (c (t + 1)) (c t) ≠ 0 ∧ c (t + 1) ≠ c t

end SubSuperStoch.SubSpec


