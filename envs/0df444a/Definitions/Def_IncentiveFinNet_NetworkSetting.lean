-- Prove2me | Definitions.Def_IncentiveFinNet_NetworkSetting
-- name    : IncentiveFinNet_NetworkSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:57.181196+00:00
-- url     : https://prove2.me/theorems/8be0428b-3e8e-4ab6-9577-b9963f21a1b7
-- title:
--   Network setting of agents with mean-variance utilities, the selection matrices $\Psi_i$, and the utility $g_i(W,P)$
-- statement:
--   A **network setting** (Definition 1) describes the beliefs and constraints of $n$ agents $i \in [n]$ (firms, countries or individuals) who sign contracts with each other.
--
--   1. **Beliefs.** Agent $i$ holds a vector $\mu_i \in \mathbb R^n$ of expected returns and a covariance matrix $\Sigma_i \succ 0$. The matrix $M \in \mathbb R^{n\times n}$ has $\mu_i$ as its $i$-th column, so $M_{ji} = \mu_{i;j}$. No sign or symmetry condition is placed on $M$: beliefs need not be correct or zero-sum. Each agent has its own $\Sigma_i$.
--   2. **Risk aversion.** Agent $i$ has a risk-aversion parameter $\gamma_i > 0$.
--   3. **Permitted counterparties.** Agent $i$ may only contract with the agents of a set $J_i \subseteq [n]$, and the relation is symmetric: $k \in J_i$ if and only if $i \in J_k$. Whether $i \in J_i$ (a self-investment is allowed) is not restricted.
--   4. **Selection matrix.** $\Psi_i \in \mathbb R^{|J_i| \times n}$ has $\Psi_{i;jk} = 1$ if $k$ is the $j$-th element of $J_i$ and $0$ otherwise; it is the identity $I_n$ with the rows of the prohibited counterparties of $i$ deleted, and $\Psi_i v$ selects the entries of $v$ indexed by $J_i$.
--
--   For a network $W \in \mathbb R^{n\times n}$ of contract sizes and a matrix $P$ of prices, write $w_i$ for the $i$-th column of $W$ ($w_{i;j} = W_{ji}$) and $Pe_i$ for the $i$-th column of $P$. Agent $i$'s **mean-variance utility** (eq. (1)) is
--   $$
--   g_i(W,P) = w_i^{\top}(\mu_i - Pe_i) - \gamma_i\, w_i^{\top}\Sigma_i w_i .
--   $$
--
--   These are the primitives of the paper's model: every stability notion and every matrix of Theorem 1 is built from them.
--
--   **Formalization Note** Agents are indexed by `Fin n`, and $n = 0$ is allowed. `Sig i` is $\Sigma_i$, and Mathlib's `Matrix.PosDef` includes symmetry, the standing meaning of a covariance matrix $\Sigma_i \succ 0$. $J_i$ is a `Finset`; the paper's order on $J_i$ is immaterial for every quantity it defines, so the rows of $\Psi_i$ are indexed by the elements of $J_i$ themselves (the row of $k \in J_i$ is $e_k^{\top}$).
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, §1 Notation p.7; §2 pp.7–10: eq. (1) p.8, permitted sets J_i and Ψ_i pp.9–10, Definition 1 p.10

import Mathlib

open Matrix

namespace IncentiveFinNet

/-- **Definition 1 (Network Setting)**, Jalan, Chakrabarti, Sarkar, *Incentive-Aware Models of
Financial Networks*, arXiv:2212.06808v3, §2, pp.7–10.

A network setting `(µ_i, γ_i, Σ_i, Ψ_i)_{i ∈ [n]}` of `n` agents: the expected-return matrix `M`
whose column `i` is agent `i`'s belief vector `µ_i` (`M j i = µ_{i;j}`), risk-aversion parameters
`γ_i > 0`, covariance matrices `Σ_i ≻ 0` (one per agent), and the permitted counterparty sets
`J_i ⊆ [n]` (p.9: "if k ∉ J_i (and hence i ∉ J_k)").

**Formalization Note**
* Agents are indexed by `Fin n`; `n = 0` is allowed.
* `Sig i` is `Σ_i`; `Matrix.PosDef` includes symmetry, the standing meaning of a covariance
  matrix `Σ_i ≻ 0`.
* `J i` is a `Finset`; its order (the paper's "ordered set") is immaterial for every quantity
  of the paper. `J_symm` is the symmetry `k ∈ J_i ↔ i ∈ J_k` of p.9. Whether `i ∈ J i`
  (self-loops) is left free. -/
structure NetworkSetting (n : ℕ) where
  /-- Expected returns: column `i` is `µ_i`, i.e. `M j i = µ_{i;j}`. -/
  M : Matrix (Fin n) (Fin n) ℝ
  /-- Risk-aversion parameters `γ_i`. -/
  γ : Fin n → ℝ
  /-- Covariance matrices `Σ_i`. -/
  Sig : Fin n → Matrix (Fin n) (Fin n) ℝ
  /-- Permitted counterparties `J_i`. -/
  J : Fin n → Finset (Fin n)
  γ_pos : ∀ i, 0 < γ i
  Sig_posDef : ∀ i, (Sig i).PosDef
  J_symm : ∀ i k, k ∈ J i ↔ i ∈ J k

namespace NetworkSetting

variable {n : ℕ} (S : NetworkSetting n)

/-- The selection matrix `Ψ_i ∈ ℝ^{|J_i| × n}` (arXiv:2212.06808v3, p.10): `Ψ_{i;jk} = 1` if `k`
is the `j`-th element of `J_i`, and `0` otherwise.

**Formalization Note** The rows are indexed by the subtype `{k // k ∈ J i}` instead of by
positions `1, …, |J_i|`; the row of `k ∈ J_i` is `e_kᵀ`. -/
def Psi (i : Fin n) : Matrix {k // k ∈ S.J i} (Fin n) ℝ :=
  Matrix.of fun a k => if k = a.1 then 1 else 0

/-- Agent `i`'s mean-variance utility, arXiv:2212.06808v3, eq. (1), p.8:
`g_i(W, P) := w_iᵀ(µ_i − P e_i) − γ_i · w_iᵀ Σ_i w_i`, where `w_i` is the `i`-th column of `W`
(`w_{i;j} = W_{ji}`) and `P e_i` is the `i`-th column of `P`. -/
def utility (i : Fin n) (W P : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∑ j, W j i * (S.M j i - P j i)) -
    S.γ i * ((fun j => W j i) ⬝ᵥ (S.Sig i *ᵥ fun j => W j i))

end NetworkSetting

end IncentiveFinNet


