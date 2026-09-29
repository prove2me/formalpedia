-- Prove2me | Definitions.Def_RobustSDP_Uniqueness_Model
-- name    : RobustSDP_Uniqueness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:04:12.436987+00:00
-- url     : https://prove2.me/theorems/d1f54733-a795-4e7d-ab12-eee3c4c386c9
-- title:
--   The robust SDP (15) with full perturbations, D = 0, ρ = 1: data, feasibility, optimality and G(y)
-- statement:
--   This file fixes the semidefinite program studied in §4 of El Ghaoui, Oustry and Lebret (1998), the robust SDP for full perturbations with $D = 0$ and uncertainty level $\rho = 1$.
--
--   Let $m, n, p, q$ be natural numbers. The **data** are matrices $F_0, F_1, \dots, F_m \in \mathbb{R}^{n\times n}$, $R_0, R_1, \dots, R_m \in \mathbb{R}^{q\times n}$ and $L \in \mathbb{R}^{n\times p}$. For $x \in \mathbb{R}^m$ put
--   $$F(x) = F_0 + \sum_{i=1}^m x_i F_i, \qquad R(x) = R_0 + \sum_{i=1}^m x_i R_i ,$$
--   and, for $\lambda \in \mathbb{R}$, the homogenized pencil $\lambda R_0 + \sum_{i=1}^m x_i R_i$.
--
--   1. **The constraint of (15).** For $\tau \in \mathbb{R}$,
--   $$\mathcal{F}(x,\tau) = \begin{bmatrix} F(x) - \tau L L^T & R(x)^T \\ R(x) & \tau I_q \end{bmatrix} \in \mathbb{R}^{(n+q)\times(n+q)} .$$
--   2. **Feasibility.** A point $y = (x, \tau) \in \mathbb{R}^m \times \mathbb{R}$ is feasible for (15) if $\mathcal{F}(x,\tau) \succeq 0$, i.e. $\mathcal{F}(x,\tau)$ is symmetric positive semidefinite.
--   3. **Optimality.** For an objective vector $c \in \mathbb{R}^m$, $y = (x,\tau)$ is optimal for (15), i.e. for
--   $$\text{minimize } c^T x \text{ subject to } \mathcal{F}(x,\tau) \succeq 0,$$
--   if it is feasible and $c^T x \le c^T x'$ for every feasible $(x', \tau')$.
--   4. **The matrix of the nonlinear reformulation (§4.2).** For $y = (x,\tau)$ with $\tau > 0$,
--   $$G(y) = F(x) - \tau L L^T - \frac{1}{\tau} R(x)^T R(x) .$$
--
--   These objects are shared by every statement of the mission: the solution of (15) is the pair $(x, \tau)$, and $G$ is the Schur complement through which the paper analyses it.
--
--   **Formalization Note** The data are bundled in a structure `SDPData m n p q`; the coefficient `Fs i` (resp. `Rs i`) for `i : Fin m` is the paper's $F_{i+1}$ (resp. $R_{i+1}$), multiplying the 0-based coordinate `x i`. Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which includes symmetry, as the paper's notation paragraph does. `G` uses Lean's `τ⁻¹`, which is $0$ at $\tau = 0$; every statement about `G` assumes $\tau > 0$ (or $\tau \ne 0$).
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 33, Eq. (1); p. 38, Eq. (15) and the definition of 𝓕(x, τ); p. 39, §4.2, definition of G(y)

import Mathlib

open Matrix

namespace RobustSDP.Uniqueness

/-- The data of the robust SDP (15) of El Ghaoui–Oustry–Lebret (1998), §4, p. 38, in the case of
full perturbations with `D = 0` and `ρ = 1`: the coefficients of the affine maps
`F(x) = F₀ + ∑ xᵢ Fᵢ` (`n × n`, Eq. (1), p. 33) and `R(x) = R₀ + ∑ xᵢ Rᵢ` (`q × n`, §2.2, p. 35),
and the matrix `L` (`n × p`). The coefficient `Fs i` (resp. `Rs i`), `i : Fin m`, is the paper's
`F_{i+1}` (resp. `R_{i+1}`), multiplying the 0-based coordinate `x i`. -/
structure SDPData (m n p q : ℕ) where
  /-- `F₀` -/
  F0 : Matrix (Fin n) (Fin n) ℝ
  /-- `F₁, …, F_m` -/
  Fs : Fin m → Matrix (Fin n) (Fin n) ℝ
  /-- `L ∈ ℝ^{n×p}` -/
  L : Matrix (Fin n) (Fin p) ℝ
  /-- `R₀` -/
  R0 : Matrix (Fin q) (Fin n) ℝ
  /-- `R₁, …, R_m` -/
  Rs : Fin m → Matrix (Fin q) (Fin n) ℝ

namespace SDPData

variable {m n p q : ℕ} (D : SDPData m n p q)

/-- `F(x) = F₀ + ∑ᵢ xᵢ Fᵢ` (Eq. (1), p. 33). -/
def F (x : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  D.F0 + ∑ i, x i • D.Fs i

/-- `R(x) = R₀ + ∑ᵢ xᵢ Rᵢ` (§2.2, p. 35). -/
def R (x : Fin m → ℝ) : Matrix (Fin q) (Fin n) ℝ :=
  D.R0 + ∑ i, x i • D.Rs i

/-- The homogenized pencil `λ R₀ + ∑ᵢ xᵢ Rᵢ` of hypothesis H3(a) (p. 38). -/
def pencil (lam : ℝ) (x : Fin m → ℝ) : Matrix (Fin q) (Fin n) ℝ :=
  lam • D.R0 + ∑ i, x i • D.Rs i

/-- The constraint matrix of the SDP (15) (p. 38),
`𝓕(x, τ) = [[F(x) − τLLᵀ, R(x)ᵀ], [R(x), τI]]`, an `(n+q) × (n+q)` block matrix. -/
def lmi (x : Fin m → ℝ) (τ : ℝ) : Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) ℝ :=
  fromBlocks (D.F x - τ • (D.L * D.Lᵀ)) (D.R x)ᵀ (D.R x) (τ • (1 : Matrix (Fin q) (Fin q) ℝ))

/-- A point `y = (x, τ)` is feasible for the SDP (15): `𝓕(x, τ) ⪰ 0`. -/
def Feasible (y : (Fin m → ℝ) × ℝ) : Prop :=
  (D.lmi y.1 y.2).PosSemidef

/-- `y = (x, τ)` is optimal for (15) with objective `cᵀx`: it is feasible, and `cᵀx ≤ cᵀx'` for
every feasible `(x', τ')`. -/
def IsOptimal (c : Fin m → ℝ) (y : (Fin m → ℝ) × ℝ) : Prop :=
  D.Feasible y ∧ ∀ y' : (Fin m → ℝ) × ℝ, D.Feasible y' → c ⬝ᵥ y.1 ≤ c ⬝ᵥ y'.1

/-- The matrix `G(y) = F(x) − τLLᵀ − (1/τ) R(x)ᵀR(x)` of §4.2 (p. 39), for `y = (x, τ)`.
Only meaningful for `τ ≠ 0` (Lean's `τ⁻¹` is `0` at `τ = 0`). -/
noncomputable def G (y : (Fin m → ℝ) × ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  D.F y.1 - y.2 • (D.L * D.Lᵀ) - y.2⁻¹ • ((D.R y.1)ᵀ * D.R y.1)

end SDPData

end RobustSDP.Uniqueness


