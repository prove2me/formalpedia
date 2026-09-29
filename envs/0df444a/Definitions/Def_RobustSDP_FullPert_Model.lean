-- Prove2me | Definitions.Def_RobustSDP_FullPert_Model
-- name    : RobustSDP_FullPert_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:58:38.117911+00:00
-- url     : https://prove2.me/theorems/b3dd435c-c9a1-4000-acd3-9f192ce308d6
-- title:
--   Linear-fractional perturbation model: affine maps, the LFR (5), the robust feasible set (2) and the LMI (10)
-- statement:
--   This file fixes the objects of the full-perturbation robust semidefinite program of El Ghaoui, Oustry and Lebret.
--
--   Let $m, n, p, q$ be natural numbers and $x \in \mathbb{R}^m$ the decision variable.
--
--   1. **Affine matrix maps.** Given coefficient matrices $A_0, A_1, \dots, A_m$ of a common size, the affine map is
--   $$A(x) = A_0 + \sum_{i=1}^{m} x_i A_i .$$
--   It is used for $F(x) = F_0 + \sum_i x_i F_i$ with $F_i \in \mathbb{R}^{n\times n}$ (Eq. (1)) and for $R(x) = R_0 + \sum_i x_i R_i$ with $R_i \in \mathbb{R}^{q\times n}$ (§2.2).
--
--   2. **Linear-fractional representation (5).** For $L \in \mathbb{R}^{n\times p}$, $D \in \mathbb{R}^{q\times p}$ and a perturbation $\Delta \in \mathbb{R}^{p\times q}$,
--   $$\mathbf{F}(x,\Delta) = F(x) + L\Delta(I - D\Delta)^{-1}R(x) + R(x)^T(I - \Delta^T D^T)^{-1}\Delta^T L^T .$$
--
--   3. **Robust feasible set (2).** For a linear subspace $\mathcal{D} \subseteq \mathbb{R}^{p\times q}$ and a level $\rho$,
--   $$\mathcal{X}_\rho = \bigl\{x \in \mathbb{R}^m \;:\; \text{for every } \Delta \in \mathcal{D},\ \|\Delta\| \le \rho,\ \det(I - D\Delta) \ne 0 \text{ and } \mathbf{F}(x,\Delta) \succeq 0\bigr\},$$
--   where $\|\Delta\|$ is the largest singular value of $\Delta$ and $X \succeq 0$ means that $X$ is symmetric positive semidefinite. The condition $\det(I - D\Delta) \neq 0$ is the paper's "$\mathbf{F}(x,\Delta)$ is well defined".
--
--   4. **The LMI of the SDP (10).** For $\tau \in \mathbb{R}$, the $(n+q)\times(n+q)$ symmetric block matrix
--   $$\begin{bmatrix} F(x) - \tau LL^T & R(x)^T - \tau LD^T \\ R(x) - \tau DL^T & \tau(\rho^{-2}I - DD^T)\end{bmatrix}.$$
--
--   These objects are shared by every statement of the mission: the robust feasible set is the set the robust SDP optimizes over, and the block matrix is the constraint of its SDP reformulation.
--
--   **Formalization Note** The coefficient list is indexed by `Fin (m + 1)`, with `A 0` the constant term and `A (i+1)` the coefficient of the 0-based coordinate `x i`. The LFR and the LMI take the values $F(x)$ and $R(x)$ as matrix arguments. Mathlib's matrix inverse returns $0$ at a singular matrix, so the LFR is meaningful only where $\det(I - D\Delta) \neq 0$; the robust feasible set requires that condition in the same clause as positive semidefiniteness. The norm is Mathlib's $\ell^2$ operator norm (`Matrix.Norms.L2Operator`), which is the largest singular value. $\rho^{-2}$ is written `(ρ ^ 2)⁻¹`.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 33, Notation and Eq. (1); p. 35, Eq. (2) and Eq. (5); p. 36, Eq. (10)

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert

/-- An affine matrix-valued map given by its coefficients (El Ghaoui–Oustry–Lebret 1998, (1),
p. 33, and §2.2, p. 35): `affineMap A x = A₀ + ∑ᵢ xᵢ Aᵢ`, where the coefficient `A (i+1)` is the
paper's `A_{i+1}` multiplying the `i`-th coordinate of `x : Fin m → ℝ` (0-based). Used both for
`F(x) = F₀ + ∑ xᵢ Fᵢ` (`n × n`) and for `R(x) = R₀ + ∑ xᵢ Rᵢ` (`q × n`). -/
def affineMap {m r c : ℕ} (A : Fin (m + 1) → Matrix (Fin r) (Fin c) ℝ) (x : Fin m → ℝ) :
    Matrix (Fin r) (Fin c) ℝ :=
  A 0 + ∑ i : Fin m, x i • A i.succ

/-- The linear-fractional representation (5), p. 35:
`F(x, Δ) = F(x) + L Δ (I − DΔ)⁻¹ R(x) + R(x)ᵀ (I − ΔᵀDᵀ)⁻¹ Δᵀ Lᵀ`, written for given values
`Fx = F(x)` (`n × n`) and `Rx = R(x)` (`q × n`), with `L : n × p`, `D : q × p`, `Δ : p × q`.
Mathlib's `⁻¹` returns `0` on a singular matrix, so this expression is only meaningful where
`det (1 - D * Δ) ≠ 0`; every use states that guard next to it. -/
noncomputable def lfr {n p q : ℕ} (Fx : Matrix (Fin n) (Fin n) ℝ) (Rx : Matrix (Fin q) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ) (Δ : Matrix (Fin p) (Fin q) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Fx + L * Δ * (1 - D * Δ)⁻¹ * Rx + Rxᵀ * (1 - Δᵀ * Dᵀ)⁻¹ * Δᵀ * Lᵀ

/-- The robust feasible set (2), p. 35, for the perturbation model `(F(·), R(·), L, D, 𝒟, ρ)`:
`x` is robustly feasible iff for every `Δ ∈ 𝒟` with spectral norm `‖Δ‖ ≤ ρ`, `F(x, Δ)` is well
defined (`det (I − DΔ) ≠ 0`) and `F(x, Δ) ⪰ 0`. The norm is the largest singular value
(`Matrix.Norms.L2Operator`), and `⪰ 0` is `Matrix.PosSemidef` (symmetric positive semidefinite). -/
def robustFeasibleSet {m n p q : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (D : Matrix (Fin q) (Fin p) ℝ) (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) (ρ : ℝ) :
    Set (Fin m → ℝ) :=
  {x | ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ ρ →
    (1 - D * Δ).det ≠ 0 ∧ (lfr (affineMap Fs x) (affineMap Rs x) L D Δ).PosSemidef}

/-- The `(n + q) × (n + q)` block matrix of the LMI (10), p. 36, in the variables `(x, τ)`,
written for given values `Fx = F(x)`, `Rx = R(x)`:
`[[F(x) − τLLᵀ, R(x)ᵀ − τLDᵀ], [R(x) − τDLᵀ, τ(ρ⁻²I − DDᵀ)]]`
(`Matrix.fromBlocks A B C D` has `B` top-right and `C` bottom-left). -/
noncomputable def sdpLMI {n p q : ℕ} (Fx : Matrix (Fin n) (Fin n) ℝ) (Rx : Matrix (Fin q) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ) (ρ τ : ℝ) :
    Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) ℝ :=
  fromBlocks (Fx - τ • (L * Lᵀ)) (Rxᵀ - τ • (L * Dᵀ)) (Rx - τ • (D * Lᵀ))
    (τ • ((ρ ^ 2)⁻¹ • (1 : Matrix (Fin q) (Fin q) ℝ) - D * Dᵀ))

end RobustSDP.FullPert


