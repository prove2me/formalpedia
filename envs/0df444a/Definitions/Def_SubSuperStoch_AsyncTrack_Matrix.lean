-- Prove2me | Definitions.Def_SubSuperStoch_AsyncTrack_Matrix
-- name    : SubSuperStoch_AsyncTrack_Matrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:25.437755+00:00
-- url     : https://prove2.me/theorems/f6bd1c90-e580-4358-8057-a4c1592d1717
-- title:
--   §2.1, Definition 2.1, Theorem 2.4, pp. 4, 7 — row sums Λ_i, ‖·‖_∞, complex eigenvalues, sub-stochastic matrices, ordered products ∏ F_s
-- statement:
--   This file fixes the matrix notation of §2.1 of Shi, Zheng, Shao and Cheng that the product theorem (Theorem 2.4) and the tracking analysis of §3 are written in.
--
--   Let $F=[f_{ij}]\in\mathbb R^{n\times n}$ be a real square matrix.
--
--   1. **Row sums.** $\Lambda_i[F]=\sum_{j=1}^n f_{ij}$ is the sum of the $i$th row of $F$.
--   2. **Infinite norm.** $\|F\|_\infty=\max\{\sum_{j=1}^n |f_{ij}| \mid i=1,\dots,n\}$ is the largest absolute row sum.
--   3. **Eigenvalues.** The eigenvalues of $F$ are taken in $\mathbb C$: they form the spectrum of $F$ regarded as a complex matrix. The statement $\rho(F)<1$ on the spectral radius means that $|\mu|<1$ for every complex eigenvalue $\mu$ of $F$.
--   4. **Sub-stochastic matrices (Definition 2.1).** $F$ is sub-stochastic if it is nonnegative, $f_{ij}\ge 0$ for all $i,j$, and
--   $$\Lambda_i[F]\le 1\qquad (i=1,\dots,n).$$
--   5. **Ordered products.** For a sequence of matrices $F_0,F_1,F_2,\dots$, a start index $a$ and a length $m$, the ordered product of $F_a,\dots,F_{a+m-1}$ multiplies later factors on the left:
--   $$\prod_{s=a}^{a+m-1}F_s = F_{a+m-1}F_{a+m-2}\cdots F_a ,$$
--   and the empty product ($m=0$) is the identity. This is the order of the paper: $\prod_{s=1}^q F_s=F_qF_{q-1}\cdots F_1$ (p. 7), and $\prod_{s=k}^{k+Ph-1}M(s)=M(k+Ph-1)\cdots M(k)$ (p. 15), because the error system evolves as $e(k+1)=M(k)e(k)$.
--
--   These objects are the vocabulary of Theorem 2.4, on products of sub-stochastic matrices, and of the convergence analysis of the asynchronous leader–follower network in §3.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin n) ℝ` with 0-based indices (the paper's $1,\dots,n$). `normInf F` is the supremum over the rows of the absolute row sums; on `Fin n` with $n\ge 1$ it is the maximum, and it is $0$ when $n=0$. `specC F` is `spectrum ℂ` of the entrywise complexification of `F`, i.e. the set of complex roots of the characteristic polynomial. `prodFrom F a m` is the ordered product $F_{a+m-1}\cdots F_a$; the paper's $\prod_{s=1}^q F_s$ is `prodFrom F 1 q`.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 4, §2.1 Matrix notations and Definition 2.1; p. 7, Theorem 2.4 and its proof ("F_qF_{q−1}⋯F_1"); p. 15, (3.8)

import Mathlib

namespace SubSuperStoch.AsyncTrack

open Matrix

/-- `Λ_i[F] = ∑_{j=1}^n f_ij`, the `i`th row sum of `F` (§2.1, p. 4). Indices are 0-based `Fin n`. -/
def rowSum {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∑ j, F i j

/-- `‖F‖_∞ = max_i ∑_j |f_ij|`, the infinite norm of `F` (§2.1, p. 4). On `Fin n` with `n ≥ 1`
the supremum of the finitely many absolute row sums is their maximum; for `n = 0` it is `0`. -/
noncomputable def normInf {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ i, ∑ j, |F i j|

/-- The eigenvalues of the real matrix `F`, as complex numbers: the spectrum of `F` viewed as a
complex matrix (= the complex roots of its characteristic polynomial). `ρ(F) < 1` is stated as
`∀ μ ∈ specC F, ‖μ‖ < 1`. -/
noncomputable def specC {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : Set ℂ :=
  spectrum ℂ (F.map (algebraMap ℝ ℂ))

/-- Definition 2.1 (p. 4): `F` is sub-stochastic if `f_ij ≥ 0` for all `i, j` and
`Λ_i[F] ≤ 1` for every `i`. -/
def IsSubStochastic {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ F i j) ∧ ∀ i, rowSum F i ≤ 1

/-- The ordered product of `m` consecutive matrices of a sequence, later factors on the left:
`prodFrom F a m = F (a + m - 1) * ⋯ * F (a + 1) * F a` (and `= 1` when `m = 0`).
So the paper's `∏_{s=1}^{q} F_s = F_q F_{q-1} ⋯ F_1` (p. 7) is `prodFrom F 1 q`, and
`∏_{s=k}^{k+Ph-1} M(s)` (p. 15) is `prodFrom M k (P * h)`. -/
def prodFrom {n : ℕ} (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (a m : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ((List.range m).map (fun t => F (a + t))).reverse.prod

end SubSuperStoch.AsyncTrack


