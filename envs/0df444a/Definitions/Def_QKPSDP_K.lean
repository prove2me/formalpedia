-- Prove2me | Definitions.Def_QKPSDP_K
-- name    : QKPSDP_K
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:52.937246+00:00
-- url     : https://prove2.me/theorems/79c10832-5d40-4924-9db3-f4dfc7f07e18
-- title:
--   The feasible region $\mathcal K_{n,r}$ of (SQKELR)
-- statement:
--   For $a \in \mathbb R^n$, $\tau \in \mathbb R$ and $r \ge 1$,
--
--   $$
--   \mathcal K_{n,r} := \bigl\{ R \in \mathbb R^{n\times r} : \|a^\top R\|^2 - \tau\, a^\top R e_1 = 0,\ \operatorname{diag}(RR^\top) = R e_1 \bigr\}.
--   $$
--
--   It is the feasible region of the factorized problem (SQKELR). For $R \in \mathcal K_{n,r}$, the matrix $Y = (e_1\ R^\top)^\top(e_1\ R^\top) = \begin{pmatrix} 1 & (Re_1)^\top \\ Re_1 & RR^\top\end{pmatrix}$ is feasible for (SQKE), with $x = Re_1$ (the first column of $R$) and $X = RR^\top$.
--
--   **Formalization Note** $\|a^\top R\|^2$ is the sum of squares of the entries of the row vector $a^\top R$; $\operatorname{diag}(RR^\top)$ is the vector of diagonal entries.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, (1), p.3

import Mathlib
import Definitions.Def_QKPSDP_e1

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, (1), p.3: the feasible region of (SQKELR),
`K_{n,r} := { R ∈ ℝ^{n×r} : ‖a⊤R‖² − τa⊤Re₁ = 0, diag(RR⊤) = Re₁ }`.

**Formalization Note** `R` is `Matrix (Fin n) (Fin r) ℝ`; `a⊤R` is the row vector `a ᵥ* R`, and
`‖a⊤R‖²` is its sum of squares `(a ᵥ* R) ⬝ᵥ (a ᵥ* R)`; `a⊤Re₁` is `a ⬝ᵥ (R *ᵥ e₁)`;
`diag(RR⊤)` is the vector of diagonal entries `(R * Rᵀ).diag`. -/
def K {n r : ℕ} [NeZero r] (a : Fin n → ℝ) (τ : ℝ) : Set (Matrix (Fin n) (Fin r) ℝ) :=
  {R | (a ᵥ* R) ⬝ᵥ (a ᵥ* R) - τ * (a ⬝ᵥ (R *ᵥ e1 r)) = 0 ∧ (R * Rᵀ).diag = R *ᵥ e1 r}

end QKPSDP


