-- Prove2me | Definitions.Def_AccelPPM_FPR_boundBD
-- name    : AccelPPM_FPR_boundBD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:46:53.310099+00:00
-- url     : https://prove2.me/theorems/4b05a519-27b5-4a1d-91fa-52c0bc27eb07
-- title:
--   The PEP matrices $A_{i,j}(h)$, $B_i(h)$, $C$, dual feasibility for (D), and its optimal value $\mathcal B_D(h)$
-- statement:
--   Fix $N\ge1$ and step coefficients $h=\{h_{i,k}\}$. Let $u_1,\dots,u_{N+1}$ be the canonical basis of $\mathbb R^{N+1}$ and $u\odot v:=\tfrac12(uv^\top+vu^\top)$ the symmetrized outer product. Define the symmetric $(N+1)\times(N+1)$ matrices
--   $$
--   A_{i,j}(h):=(u_i-u_j)\odot(u_i-u_j)-(u_i-u_j)\odot\sum_{l=i-1}^{j-2}\sum_{k=0}^{l}h_{l+1,k+1}u_{k+1},\qquad i<j=1,\dots,N,
--   $$
--   $$
--   B_i(h):=u_iu_i^\top-u_i\odot u_{N+1}+u_i\odot\sum_{l=0}^{i-2}\sum_{k=0}^{l}h_{l+1,k+1}u_{k+1},\qquad i=1,\dots,N,
--   $$
--   $$
--   C:=u_{N+1}u_{N+1}^\top .
--   $$
--   A tuple $(a_2,\dots,a_N,b_N,c)$ is **feasible for the dual problem (D)** if $a_2,\dots,a_N,b_N,c\ge0$ and
--   $$
--   \sum_{i=2}^{N}a_iA_{i-1,i}(h)+b_NB_N(h)+cC-u_Nu_N^\top\ \succeq\ 0 .
--   $$
--   The optimal value of (D) is
--   $$
--   \mathcal B_D(h):=\min\{\,c : (a_2,\dots,a_N,b_N,c)\text{ feasible for (D)}\,\}.
--   $$
--   (D) is the Lagrangian dual of a semidefinite relaxation of the performance estimation problem for the worst-case fixed-point residual of the general proximal point method after $N$ steps; any feasible $c$ is an upper bound on that worst case.
--
--   **Formalization Note** Matrices are `Matrix (Fin (N+1)) (Fin (N+1)) ℝ`; `basisVec N i` is the 1-based basis vector $u_i$ ($1\le i\le N+1$, coordinate `j : Fin (N+1)` standing for index $j+1$). The sums $\sum_{l=i-1}^{j-2}$ and $\sum_{l=0}^{i-2}$ are `Finset.Ico (i-1) (j-1)` and `Finset.range (i-1)`, so the latter is empty for $i=1$. The module declares `basisVec`, `symOuter`, `matA`, `matB`, `matC`, `dualMatrix`, `IsDualFeasible` and `boundBD`; the dual variables are `a : ℕ → ℝ` (only `a 2, …, a N` are read), `b` $=b_N$ and `c`. $\mathcal B_D(h)$ is valued in `EReal`: it is the `sInf` of the feasible values of $c$ cast to `EReal`, so an infeasible $h$ gets the paper's value $+\infty$ (`sInf ∅ = ⊤`). The feasible $c$ are nonnegative, so the value is never $-\infty$; when (D) is feasible (as for Kim's coefficients (25), by Lemma 4.1) it is the infimum of the feasible $c$ (the paper's min).
-- source:
--   Kim, Accelerated proximal point method for maximally monotone operators, arXiv:1905.05149v4, p. 7, definitions of $A_{i,j}(h)$, $B_i(h)$, $C$ and $u\odot v$ after (23), and the dual problem (D)

import Mathlib

namespace AccelPPM.FPR

/-- The 1-based canonical basis of `ℝ^{N+1}`: `basisVec N i = u_i` for `1 ≤ i ≤ N + 1`
(coordinates are indexed by `Fin (N+1)`, coordinate `j` standing for the paper's index `j + 1`).
`basisVec N 0 = 0` and is never used. -/
def basisVec (N i : ℕ) : Fin (N + 1) → ℝ :=
  fun j => if (j : ℕ) + 1 = i then 1 else 0

/-- The symmetrized outer product `u ⊙ v := ½ (u vᵀ + v uᵀ)` (p. 7). -/
noncomputable def symOuter {N : ℕ} (u v : Fin (N + 1) → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (1 / 2 : ℝ) • (Matrix.vecMulVec u v + Matrix.vecMulVec v u)

/-- `A_{i,j}(h) := (u_i − u_j) ⊙ (u_i − u_j) − (u_i − u_j) ⊙ ∑_{l=i−1}^{j−2} ∑_{k=0}^{l} h_{l+1,k+1} u_{k+1}`
(p. 7), for `1 ≤ i < j ≤ N`. The outer sum over `l = i−1, …, j−2` is `Finset.Ico (i-1) (j-1)`. -/
noncomputable def matA (N : ℕ) (h : ℕ → ℕ → ℝ) (i j : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  symOuter (basisVec N i - basisVec N j) (basisVec N i - basisVec N j)
    - symOuter (basisVec N i - basisVec N j)
        (∑ l ∈ Finset.Ico (i - 1) (j - 1), ∑ k ∈ Finset.range (l + 1),
          h (l + 1) (k + 1) • basisVec N (k + 1))

/-- `B_i(h) := u_i u_iᵀ − u_i ⊙ u_{N+1} + u_i ⊙ ∑_{l=0}^{i−2} ∑_{k=0}^{l} h_{l+1,k+1} u_{k+1}`
(p. 7), for `1 ≤ i ≤ N`. The outer sum over `l = 0, …, i−2` is `Finset.range (i-1)`, which is
empty for `i = 1`. -/
noncomputable def matB (N : ℕ) (h : ℕ → ℕ → ℝ) (i : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.vecMulVec (basisVec N i) (basisVec N i)
    - symOuter (basisVec N i) (basisVec N (N + 1))
    + symOuter (basisVec N i)
        (∑ l ∈ Finset.range (i - 1), ∑ k ∈ Finset.range (l + 1),
          h (l + 1) (k + 1) • basisVec N (k + 1))

/-- `C := u_{N+1} u_{N+1}ᵀ` (p. 7). -/
def matC (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.vecMulVec (basisVec N (N + 1)) (basisVec N (N + 1))

/-- The matrix of the constraint of the dual problem (D) (p. 7):
`∑_{i=2}^{N} a_i A_{i−1,i}(h) + b_N B_N(h) + c C − u_N u_Nᵀ`, with `a i = a_i` and `b = b_N`. -/
noncomputable def dualMatrix (N : ℕ) (h : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (b c : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  ∑ i ∈ Finset.Icc 2 N, a i • matA N h (i - 1) i + b • matB N h N + c • matC N
    - Matrix.vecMulVec (basisVec N N) (basisVec N N)

/-- `(a_2, …, a_N, b_N, c)` is a feasible point of the dual problem (D) for the step
coefficients `h` (p. 7): all dual variables are nonnegative and the matrix
`∑_{i=2}^{N} a_i A_{i−1,i}(h) + b_N B_N(h) + c C − u_N u_Nᵀ` is positive semidefinite.
Only the entries `a 2, …, a N` of `a` are read. -/
def IsDualFeasible (N : ℕ) (h : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (b c : ℝ) : Prop :=
  (∀ i ∈ Finset.Icc 2 N, 0 ≤ a i) ∧ 0 ≤ b ∧ 0 ≤ c ∧ (dualMatrix N h a b c).PosSemidef

/-- The optimal value `B_D(h)` of the dual problem (D) (p. 7): the infimum of `c` over the
feasible points `(a_2, …, a_N, b_N, c)` of (D), computed in `EReal` so that an infeasible `h`
gets the paper's value `+∞` (`sInf ∅ = ⊤`). The feasible `c` are nonnegative, so the value is
never `⊥`; when (D) is feasible (e.g. for Kim's coefficients (25), by Lemma 4.1) it is the real
infimum of the feasible `c`. -/
noncomputable def boundBD (N : ℕ) (h : ℕ → ℕ → ℝ) : EReal :=
  sInf ((fun c : ℝ => (c : EReal)) '' {c : ℝ | ∃ (a : ℕ → ℝ) (b : ℝ), IsDualFeasible N h a b c})

end AccelPPM.FPR


