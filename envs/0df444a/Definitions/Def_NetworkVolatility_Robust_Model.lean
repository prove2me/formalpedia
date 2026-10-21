-- Prove2me | Definitions.Def_NetworkVolatility_Robust_Model
-- name    : NetworkVolatility_Robust_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:16:59.606082+00:00
-- url     : https://prove2.me/theorems/b044a0a4-ec54-43c0-9865-f9b00e49e2f0
-- title:
--   §2.1–§3.1, pp. 6–11 — network pricing game: utility, consumption equilibrium, optimal revenue $R(W,\alpha,b)$, uncertainty set $\mathcal W(W,\epsilon)$, $\lambda_{\max}$
-- statement:
--   This file sets up the two-stage network pricing game of Baron, Hu and Malekian and the robust revenue-volatility quantity of their §3.
--
--   **Agents and network.** There are $n$ agents $V=\{1,\dots,n\}$ on a weighted network $W\in\mathbb R^{n\times n}$, where $W_{ij}$ is the strength of the peer effect between $i$ and $j$. A parameter $\alpha$ scales the network effect, $b\in\mathbb R^n$ collects the agents' primary values, and $c$ is the seller's marginal cost.
--
--   **Standing assumptions** (§2.1, pp. 6–7): $\alpha\ge 0$, $W_{ij}\ge 0$, $W^\top=W$, and $W_{ii}=0$ for all $i$ (a network without self-loops).
--
--   **Second stage: the consumption game** $(W,\alpha,b,p)$. Given prices $p\in\mathbb R^n$ and a consumption profile $x\in\mathbb R^n$, the utility of agent $i$ is
--   $$u_i(x;W,b,p)=-\tfrac12 x_i^2+b_i x_i+\alpha\sum_{j\in V\setminus\{i\}} W_{ij}x_ix_j-p_ix_i .$$
--   A **consumption equilibrium** is a profile $x\ge 0$ such that, for every $i$, $x_i$ maximizes $y\mapsto u_i(y,x_{-i};W,b,p)$ over $y\in\mathbb R_+$.
--
--   **First stage: pricing.** The seller's revenue at prices $p$ and consumption $x$ is $\sum_i (p_i-c)x_i$. The set of achievable revenues collects these values over all $p\in\mathbb R^n$ and all consumption equilibria $x$ at $p$. The **optimal revenue** $R(W,\alpha,b)$ (Definition 1) is the supremum of that set, and a price vector $p$ is **optimal** if some consumption equilibrium at $p$ attains the greatest achievable revenue.
--
--   **Assumptions** (p. 8). Assumption 1: $\alpha\sum_j W_{ij}<1$ for every $i$ (that is, $1/\alpha>\max_i\sum_j W_{ij}$). Assumption 2: $b_i>c$ for every $i$ ($b>c\mathbf 1$).
--
--   **Spectral quantities.** $\lambda_{\max}(M)$ is the largest absolute value of a real eigenvalue of $M$ (p. 6); it is applied only to symmetric matrices, whose eigenvalues are all real. $\rho(A)$ is the spectral radius of a real square matrix, the largest modulus of its complex eigenvalues. $\|\cdot\|$ is the spectral norm (the $\ell_2$ operator norm).
--
--   **Uncertainty set** (Definition 2, p. 10):
--   $$\mathcal W(W,\epsilon)=\{\tilde W:\ \|W-\tilde W\|_2\le\epsilon\|W\|_2,\ \tilde W\ge0,\ \tilde W^\top=\tilde W,\ \tilde W_{ii}=0\ \forall i\}.$$
--
--   **Revenue volatility** (Definition 3, pp. 10–11). The seller sets the ex-ante optimal price $p$ for the forecast network $W$; the consumers then play the consumption game on the realized network $\tilde W$, yielding consumption $\tilde x$ and revenue $R(\tilde W,\alpha,b)=\sum_i(p_i-c)\tilde x_i$. The volatility set is
--   $$\Big\{\frac{|R(W,\alpha,b)-R(\tilde W,\alpha,b)|}{R(W,\alpha,b)}\ :\ \tilde W\in\mathcal W(W,\epsilon),\ b>c\mathbf 1\Big\},$$
--   and $\mathrm{RV}(W,\epsilon)$ is its least upper bound.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Agents are `Fin n`. The revenue of the game is defined from the equilibrium, not by Proposition 2's closed form, so Propositions 1–2 carry content. Two conventions are added to the page: the zero diagonal of $W$ and of every $\tilde W$ (the utility sums over $j\neq i$, so $W_{ii}$ never enters the game while the paper's formulas use $(I-\alpha W)^{-1}$ with the full $W$), and $\mathrm{RV}$ as a least upper bound rather than an attained maximum (the paper's maximizing $b=c\mathbf 1+v_{\max}$ need not satisfy $b>c\mathbf 1$). `lamMax` is `sSup` of $|\mu|$ over the real spectrum ($0$ when $n=0$); `specRadius` uses the complex spectrum of the complexified matrix. The norm is Mathlib's scoped `Matrix.Norms.L2Operator` instance.
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), pp. 6–11, §2.1–§3.1, Assumptions 1–2, Definitions 1–3

import Mathlib

namespace NetworkVolatility.Robust

open Matrix Finset
open scoped Matrix.Norms.L2Operator

/-- p. 7: the utility of agent `i` at the consumption profile `x`,
`u_i(x; W, b, p) = -(1/2) x_i² + b_i x_i + α Σ_{j ∈ V∖{i}} W_ij x_i x_j - p_i x_i`. -/
noncomputable def utility {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b p x : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  -(1 / 2) * x i ^ 2 + b i * x i + α * ∑ j ∈ univ.erase i, W i j * x i * x j - p i * x i

/-- p. 7: `x` is a consumption equilibrium of the game `(W, α, b, p)`: every `x_i ≥ 0`, and `x_i`
maximizes `u_i(·, x_{-i})` over `ℝ₊`. -/
def IsConsumptionEq {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b p x : Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ x i ∧
    ∀ y : ℝ, 0 ≤ y → utility W α b p (Function.update x i y) i ≤ utility W α b p x i

/-- p. 7: the seller's revenue `Σ_i (p_i - c) x_i` at prices `p` and consumption `x`, with marginal
cost `c`. -/
def revenue {n : ℕ} (c : ℝ) (p x : Fin n → ℝ) : ℝ :=
  ∑ i, (p i - c) * x i

/-- The revenues the seller can obtain: `(p - c1)ᵀ x` for a price vector `p ∈ ℝⁿ` and a consumption
equilibrium `x` of the game `(W, α, b, p)`. -/
def revenueSet {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b : Fin n → ℝ) (c : ℝ) : Set ℝ :=
  {r | ∃ p x : Fin n → ℝ, IsConsumptionEq W α b p x ∧ r = revenue c p x}

/-- Definition 1, p. 8: the optimal revenue `R(W, α, b)` of the monopolist, the supremum of
`revenueSet W α b c` (Proposition 2 shows that it is attained). -/
noncomputable def optRevenue {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b : Fin n → ℝ)
    (c : ℝ) : ℝ :=
  sSup (revenueSet W α b c)

/-- p. 7: `p` is an optimal (first-stage) price vector of the seller in the game `(W, α, b)`: some
consumption equilibrium at `p` yields the greatest element of `revenueSet W α b c`. -/
def IsOptimalPrice {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b : Fin n → ℝ) (c : ℝ)
    (p : Fin n → ℝ) : Prop :=
  ∃ x, IsConsumptionEq W α b p x ∧ IsGreatest (revenueSet W α b c) (revenue c p x)

/-- §2.1, pp. 6–7: the standing assumptions on the network: `α ≥ 0`, `W ≥ 0` entrywise, `W`
symmetric, and (added: no self-loops) a zero diagonal. -/
def Standing {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) : Prop :=
  0 ≤ α ∧ (∀ i j, 0 ≤ W i j) ∧ W.IsSymm ∧ ∀ i, W i i = 0

/-- Assumption 1 (Regularity), p. 8: `1/α > max_i Σ_j W_ij`, written `α Σ_j W_ij < 1` for all `i`. -/
def Assumption1 {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) : Prop :=
  ∀ i, α * ∑ j, W i j < 1

/-- Assumption 2 (Positive Consumption with No Network Effect), p. 8: `b > c1`. -/
def Assumption2 {n : ℕ} (b : Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ i, c < b i

/-- p. 6: `λmax(M)`, the largest absolute value of a (real) eigenvalue of `M`. Applied only to
symmetric real matrices, whose eigenvalues are all real. Equal to `0` when `n = 0`. -/
noncomputable def lamMax {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun μ : ℝ => |μ|) '' spectrum ℝ M)

/-- The spectral radius `ρ(A)` of a real square matrix: the largest modulus of a complex eigenvalue
of `A`. Equal to `0` when `n = 0`. -/
noncomputable def specRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun μ : ℂ => ‖μ‖) '' spectrum ℂ (A.map (algebraMap ℝ ℂ)))

/-- Definition 2, p. 10: the uncertainty set `𝒲(W, ε)` of `ε`-perturbed networks,
`{W̃ : ‖W - W̃‖₂ ≤ ε ‖W‖₂, W̃ ≥ 0, W̃ᵀ = W̃}` with the spectral (l2 operator) norm, restricted
(added) to networks `W̃` with a zero diagonal. -/
def uncSet {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {Wt | ‖W - Wt‖ ≤ ε * ‖W‖ ∧ (∀ i j, 0 ≤ Wt i j) ∧ Wt.IsSymm ∧ ∀ i, Wt i i = 0}

/-- Definition 3, pp. 10–11: the relative revenue changes
`|R(W, α, b) - R(W̃, α, b)| / R(W, α, b)` over `W̃ ∈ 𝒲(W, ε)` and `b > c1`, where `R(W̃, α, b)` is
the revenue at the seller's ex-ante optimal price `p` for `W` with the consumers' equilibrium `x`
on the realized network `W̃` (p. 11). `RV(W, ε)` is the least upper bound of this set. -/
def volatilitySet {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α c ε : ℝ) : Set ℝ :=
  {r | ∃ Wt ∈ uncSet W ε, ∃ b : Fin n → ℝ, Assumption2 b c ∧
    ∃ p x : Fin n → ℝ, IsOptimalPrice W α b c p ∧ IsConsumptionEq Wt α b p x ∧
      r = |optRevenue W α b c - revenue c p x| / optRevenue W α b c}

end NetworkVolatility.Robust


