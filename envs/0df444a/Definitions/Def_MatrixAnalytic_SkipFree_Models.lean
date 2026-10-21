-- Prove2me | Definitions.Def_MatrixAnalytic_SkipFree_Models
-- name    : MatrixAnalytic_SkipFree_Models
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:52.815034+00:00
-- url     : https://prove2.me/theorems/81005f83-f3d0-43b8-b1f2-3d2f15a07f7e
-- title:
--   M/G/1-type (13.1) and GI/M/1-type (13.2) chains, the QBD (13.3)–(13.7) embedding an M/G/1-type chain, and the matrix H (13.9)
-- statement:
--   Let $\iota$ be a set of phases and $D_0,D_1,\dots$ and $C_0,C_1,\dots$ two sequences of real matrices indexed by $\iota$.
--
--   1. The **M/G/1-type chain** (skip-free to the left) has transition matrix (13.1),
--   $$\tilde P=\begin{bmatrix}D_0&D_1&D_2&D_3&\cdots\\C_0&C_1&C_2&C_3&\cdots\\0&C_0&C_1&C_2&\cdots\\0&0&C_0&C_1&\cdots\\\vdots&\vdots&\vdots&\vdots&\ddots\end{bmatrix}:$$
--   from $(0,i)$ it moves to $(k,j)$ with probability $(D_k)_{ij}$, and from $(n,i)$, $n\ge1$, to $(n-1+k,j)$ with probability $(C_k)_{ij}$.
--   2. The **GI/M/1-type chain** (skip-free to the right) has transition matrix (13.2),
--   $$\tilde P=\begin{bmatrix}D_0&C_0&0&0&\cdots\\D_1&C_1&C_0&0&\cdots\\D_2&C_2&C_1&C_0&\cdots\\D_3&C_3&C_2&C_1&\cdots\\\vdots&\vdots&\vdots&\vdots&\ddots\end{bmatrix}:$$
--   from $(n,i)$ it moves to $(0,j)$ with probability $(D_n)_{ij}$ and to $(n+1-k,j)$ with probability $(C_k)_{ij}$, $0\le k\le n$.
--   3. The **QBD embedding an M/G/1-type chain** (Table 13.1) is the three-dimensional process $\{(X_t,D_t,J_t)\}$ on the states $(n,d,j)$, $n,d\ge0$, $j\in\iota$, with levels $n$ and two-dimensional phases $(d,j)$, and transition matrix (13.3) with the blocks
--   $$B=\begin{bmatrix}D_0&D_1&D_2&\cdots\\0&0&0&\cdots\\\vdots&&&\ddots\end{bmatrix},\ A_0=\begin{bmatrix}0&0&0&\cdots\\I&0&0&\cdots\\0&I&0&\cdots\\\vdots&&&\ddots\end{bmatrix},\ A_1=\begin{bmatrix}C_1&C_2&C_3&\cdots\\0&0&0&\cdots\\\vdots&&&\ddots\end{bmatrix},\ A_2=\begin{bmatrix}C_0&0&\cdots\\0&0&\cdots\\\vdots&&\ddots\end{bmatrix}$$
--   (13.4)–(13.7), the block rows and columns being indexed by the sublevel $d$. A jump of the original chain from $(n,i)$ up to $(n+k,j)$ becomes the steps $(n,0,i)\to(n,k,j)\to(n+1,k-1,j)\to\dots\to(n+k,0,j)$.
--   4. The matrix $H$ (13.9) at level $n\ge1$ is
--   $$H_{ij}=\mathrm P[\tau<\infty\ \&\ (X_\tau,D_\tau,J_\tau)=(n-1,0,j)\mid(X_0,D_0,J_0)=(n,0,i)],$$
--   $\tau$ the first passage time from $\ell(n)$ to $\ell(n-1)$ in that QBD, a first-entrance path sum.
--   5. For a sequence $M_0,M_1,\dots$ and a nonnegative matrix $X$, the series $\sum_{k\ge0}M_{n+k}X^k$; with $M=C$, $X=H$ this is $\bar C_n$, with $M=D$ it is $\bar D_n$ (Theorem 13.1.5), and with $n=0$, $M=C$ it is the right-hand side $\sum_{k\ge0}C_kX^k$ of (13.10). Also the series $\sum_{k\ge0}X^kC_k=C_0+XC_1+X^2C_2+\cdots$, the right-hand side of (13.27).
--
--   **Formalization Note** The blocks are given as sequences of matrices indexed by an arbitrary phase type (the page has $1\le j\le m$; nothing below needs $m<\infty$). The series in item 5 are computed entrywise in $[0,\infty]$ with negative real entries read as $0$; under the stochasticity hypotheses of the theorems all entries are nonnegative. $H$ is defined probabilistically on the QBD (13.3), as (13.9) does, not as a solution of (13.10).
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 267–270, Eqs. (13.1)–(13.7), Table 13.1; p. 271, Eq. (13.9); p. 274 (C̄_n, D̄_n); p. 279, Eq. (13.27)

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_QBD
import Definitions.Def_MatrixAnalytic_SkipFree_Passage

namespace MatrixAnalytic.SkipFree

noncomputable section

open scoped ENNReal

/-!
The two skip-free chains of Chapter 13 of Latouche & Ramaswami (pp. 267–268) on the states
`(n, i)`, `n ≥ 0` the level and `i` the phase (an arbitrary type `ι`), with blocks
`D₀, D₁, …` and `C₀, C₁, …` given as sequences `D C : ℕ → ι → ι → ℝ`; the QBD (13.3)–(13.7)
embedding an M/G/1-type chain (Table 13.1, p. 269), whose phases are pairs `(d, j)`; the matrix
`H` (13.9); and the matrix series appearing in (13.10), (13.12) and (13.27).
-/

variable {ι : Type*}

/-- The M/G/1-type transition matrix (13.1), skip-free to the left: from `(0, i)` the chain
moves to `(k, j)` with probability `(D_k)_{ij}`; from `(n, i)`, `n ≥ 1`, it moves to
`(n − 1 + k, j)` with probability `(C_k)_{ij}`, `k ≥ 0`, and never below `n − 1`. -/
def mg1P (D C : ℕ → ι → ι → ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  fun x y =>
    if x.1 = 0 then D y.1 x.2 y.2
    else if x.1 ≤ y.1 + 1 then C (y.1 + 1 - x.1) x.2 y.2
    else 0

/-- The GI/M/1-type transition matrix (13.2), skip-free to the right: from `(n, i)` the chain
moves to `(0, j)` with probability `(D_n)_{ij}` and to `(n + 1 − k, j)` with probability
`(C_k)_{ij}` for `0 ≤ k ≤ n` (block row `n` is `D_n, C_n, C_{n−1}, …, C₁, C₀`), and never above
`n + 1`. -/
def gm1P (D C : ℕ → ι → ι → ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  fun x y =>
    if y.1 = 0 then D x.1 x.2 y.2
    else if y.1 ≤ x.1 + 1 then C (x.1 + 1 - y.1) x.2 y.2
    else 0

/-- Block `B` (13.4) of the QBD embedding an M/G/1-type chain, with phases `(d, j)`:
`B_{(0,i),(k,j)} = (D_k)_{ij}` and every row with `d ≥ 1` is zero. -/
def augB (D : ℕ → ι → ι → ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  fun a b => if a.1 = 0 then D b.1 a.2 b.2 else 0

/-- Block `A₀` (13.5): `(A₀)_{(d,i),(d',j)} = 1` if `d = d' + 1` and `i = j`, else `0`
(the deterministic step `(n, k, i) → (n + 1, k − 1, i)`, `k ≥ 1`). -/
def augA0 [DecidableEq ι] : ℕ × ι → ℕ × ι → ℝ :=
  fun a b => if a.1 = b.1 + 1 ∧ a.2 = b.2 then 1 else 0

/-- Block `A₁` (13.6): `(A₁)_{(0,i),(k,j)} = (C_{k+1})_{ij}` and every row with `d ≥ 1` is
zero. -/
def augA1 (C : ℕ → ι → ι → ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  fun a b => if a.1 = 0 then C (b.1 + 1) a.2 b.2 else 0

/-- Block `A₂` (13.7): `(A₂)_{(0,i),(0,j)} = (C₀)_{ij}`, every other entry zero. -/
def augA2 (C : ℕ → ι → ι → ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  fun a b => if a.1 = 0 ∧ b.1 = 0 then C 0 a.2 b.2 else 0

/-- The transition matrix (13.3) of the three-dimensional process `{(X_t, D_t, J_t)}`: the QBD
with levels `n`, phases `(d, j)` and blocks (13.4)–(13.7). -/
def mg1QBD [DecidableEq ι] (D C : ℕ → ι → ι → ℝ) : ℕ × (ℕ × ι) → ℕ × (ℕ × ι) → ℝ :=
  qbdP (augB D) augA0 (augA1 C) (augA2 C)

/-- The matrix `H` (13.9) at level `n`: `H_{ij} = P[τ < ∞ & (X_τ, D_τ, J_τ) = (n − 1, 0, j) |
(X₀, D₀, J₀) = (n, 0, i)]`, `τ` the first passage time from `ℓ(n)` to `ℓ(n − 1)` in the QBD
(13.3). Meant for `n ≥ 1`. -/
def matH [DecidableEq ι] (D C : ℕ → ι → ι → ℝ) (n : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance (mg1QBD D C) (level (n - 1)) (n, (0, i)) (n - 1, (0, j))

/-- The series `Σ_{k ≥ 0} M_{n+k} X^k` in `ℝ≥0∞`: with `M = C`, `X = H` it is `C̄_n`, with
`M = D` it is `D̄_n` (Theorem 13.1.5, p. 274); with `n = 0` and `M = C` it is the right-hand side
`Σ_{k≥0} C_k X^k` of (13.10). -/
def shiftSeriesE [DecidableEq ι] (M : ℕ → ι → ι → ℝ) (X : ι → ι → ℝ≥0∞) (n : ℕ) :
    ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k : ℕ, matMulE (ennMat (M (n + k))) (matPowE X k) i j

/-- The right-hand side `C₀ + XC₁ + X²C₂ + ⋯ = Σ_{k ≥ 0} X^k C_k` of (13.27), in `ℝ≥0∞`. -/
def leftSeriesE [DecidableEq ι] (C : ℕ → ι → ι → ℝ) (X : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k : ℕ, matMulE (matPowE X k) (ennMat (C k)) i j

end

end MatrixAnalytic.SkipFree


