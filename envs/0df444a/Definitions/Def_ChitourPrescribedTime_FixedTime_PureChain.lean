-- Prove2me | Definitions.Def_ChitourPrescribedTime_FixedTime_PureChain
-- name    : ChitourPrescribedTime_FixedTime_PureChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:04:31.850984+00:00
-- url     : https://prove2.me/theorems/c969048a-c49c-4969-b1a9-912bc665756f
-- title:
--   The pure chain of integrators $\dot x = J_n x + u e_n$ (31) and the dilation $D^{\mathbf r}_\lambda$ (5)
-- statement:
--   Let $n\ge1$ and let $(e_i)_{1\le i\le n}$ be the canonical basis of $\mathbb R^n$. The $n$-th **Jordan block** $J_n$ is the matrix with $J_n e_i=e_{i-1}$ for $1\le i\le n$, with $e_0=0$; equivalently $(J_nx)_i=x_{i+1}$ for $i<n$ and $(J_nx)_n=0$. The **$n$-th order pure chain of integrators** (31) is
--   $$\dot x = J_n x + u\, e_n ,$$
--   with scalar control $u$; the definition records its right-hand side $(x,u)\mapsto J_nx+ue_n$.
--
--   With the weights $r_i:=n-i+1$ ($1\le i\le n$), the **dilation** of (5) is
--   $$D^{\mathbf r}_\lambda=\operatorname{diag}(\lambda^{r_i})_{i=1}^n ,\qquad \lambda>0,$$
--   which satisfies $D^{\mathbf r}_\lambda J_n (D^{\mathbf r}_\lambda)^{-1}=\lambda J_n$ and $D^{\mathbf r}_\lambda e_n=\lambda e_n$. This is the dilation used in the time rescaling of Theorem 30; it is not the dilation $D^{\mathbf r(\kappa)}_\lambda$ of Proposition 24.
--
--   **Formalization Note** The paper's 1-based index $i\in\{1,\dots,n\}$ is `i : Fin n` with value `i.val + 1`; hence $r_i=n-i+1$ becomes the natural-number exponent `n - i.val` $\ge1$. The parameter $\lambda$ is named `lam`.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1026, §3, eq. (5); p. 1033, §4.1, eq. (31)

import Mathlib

open Matrix

namespace ChitourPrescribedTime.FixedTime

/-- The `n`-th Jordan block `J_n`: `(J_n)_{ij} = 1` if `j = i + 1` and `0` otherwise, so that
`J_n e_i = e_{i-1}` with `e_0 = 0` and `(J_n x)_i = x_{i+1}` (`x_{n+1} := 0`).
Indices: the paper's `i ∈ {1, …, n}` is `i : Fin n` with value `i.val + 1`. -/
def jordanBlock (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.val = i.val + 1 then 1 else 0

/-- The last canonical basis vector `e_n` of `ℝ^n`. -/
def eN (n : ℕ) : Fin n → ℝ :=
  fun i => if i.val + 1 = n then 1 else 0

/-- The right-hand side of the `n`-th order pure chain of integrators (31),
`ẋ = J_n x + u e_n`, at state `x` and control value `u`. -/
noncomputable def chainField (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (u : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (jordanBlock n *ᵥ (WithLp.ofLp x) + u • eN n)

/-- The dilation of §3, (5): `D^r_λ = diag(λ^{r_i})` with `r_i = n - i + 1` (1-based `i`),
applied to `x`. With 0-based `i : Fin n` the exponent is `n - i.val ≥ 1`. -/
noncomputable def dilR (n : ℕ) (lam : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i : Fin n => lam ^ (n - i.val) * x i)

end ChitourPrescribedTime.FixedTime


