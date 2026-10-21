-- Prove2me | Definitions.Def_WrightPDIPM_SelfDual_Setup
-- name    : WrightPDIPM_SelfDual_Setup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:42.127829+00:00
-- url     : https://prove2.me/theorems/95effacd-109e-4c18-97a0-e49d6d195734
-- title:
--   Self-dual setting: the problem (A.2) and its solutions, the LP pair (9.3) with Ω, B, N, the self-dual LP (9.1) and mLCP (9.2), the simplified HSD mLCP (9.5) and the HSD mLCP (9.8)
-- statement:
--   Vectors are real column vectors, vector inequalities are componentwise, and $e$ is the all-ones vector. This file defines the objects of Chapter 9 and Appendix A of Wright's book.
--
--   1. The **Euclidean norm** $\|v\| = (\sum_i v_i^2)^{1/2}$ and the **gradient** $\nabla f(u)$ of $f : \mathbb R^N \to \mathbb R$, the vector of partial derivatives $\partial f/\partial u_i(u)$.
--   2. The **linearly constrained problem** (A.2): $\min f(u)$ subject to $Cu = d$, $Gu \ge h$, $u \in U$, with $U \subset \mathbb R^N$, matrices $C, G$ and vectors $d, h$. A point $u^*$ is **feasible** if $u^* \in U$, $Cu^* = d$, $Gu^* \ge h$; it is a **local solution** if it is feasible and there is $\rho > 0$ with $f(u) \ge f(u^*)$ for every feasible $u$ with $\|u - u^*\| < \rho$; it is a **global solution** if it is feasible and $f(u) \ge f(u^*)$ for every feasible $u$.
--   3. For $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$ (no rank assumption), the primal-dual pair
--   $$\min c^{\mathsf T}x \ \text{ s.t. } Ax = b,\ x \ge 0, \qquad (9.3a) \qquad\qquad \max b^{\mathsf T}\lambda \ \text{ s.t. } A^{\mathsf T}\lambda + s = c,\ s \ge 0, \qquad (9.3b)$$
--   the solution sets $\Omega_P$ (feasible $x$ with $c^{\mathsf T}x \le c^{\mathsf T}x'$ for every feasible $x'$), $\Omega_D$ (feasible $(\lambda, s)$ with $b^{\mathsf T}\lambda \ge b^{\mathsf T}\lambda'$ for every feasible $(\lambda', s')$), $\Omega = \Omega_P \times \Omega_D$ as triples $(x, \lambda, s)$, and the index sets $\mathcal B = \{j : x^*_j \ne 0 \text{ for some } x^* \in \Omega_P\}$, $\mathcal N = \{j : s^*_j \ne 0 \text{ for some } (\lambda^*, s^*) \in \Omega_D\}$.
--   4. The **self-dual linear program** (9.1), $\min f^{\mathsf T}u + g^{\mathsf T}w$ subject to $M_{11}u + M_{12}w \ge -f$, $-M_{12}^{\mathsf T}u + M_{22}w = -g$, $u \ge 0$, $w$ free (feasibility only is defined), and its **mixed LCP** (9.2): $(u, v, w)$ with
--   $$v = M_{11}u + M_{12}w + f,\quad 0 = -M_{12}^{\mathsf T}u + M_{22}w + g,\quad (u, v) \ge 0,\quad u^{\mathsf T}v = 0;$$
--   a solution is **strictly complementary** if $u + v > 0$.
--   5. The mLCP (9.5) of the **simplified homogeneous self-dual (HSD) form**: $(\tau, x, \lambda, \kappa, s) \in \mathbb R \times \mathbb R^n \times \mathbb R^m \times \mathbb R \times \mathbb R^n$ with
--   $$\begin{bmatrix}\kappa\\ s\\ 0\end{bmatrix} = \begin{bmatrix} 0 & -c^{\mathsf T} & b^{\mathsf T}\\ c & 0 & -A^{\mathsf T}\\ -b & A & 0\end{bmatrix}\begin{bmatrix}\tau\\ x\\ \lambda\end{bmatrix}, \qquad (\tau, x, \kappa, s) \ge 0, \qquad \tau\kappa + x^{\mathsf T}s = 0;$$
--   a solution is **strictly complementary** if $\tau + \kappa > 0$ and $x + s > 0$.
--   6. For an initial point $(x^0, \lambda^0, s^0)$, the quantities $\bar b = b - Ax^0$, $\bar c = c - A^{\mathsf T}\lambda^0 - s^0$, $\bar z = c^{\mathsf T}x^0 + 1 - b^{\mathsf T}\lambda^0$, and the mLCP (9.8) of the **HSD form**: $(\tau, x, \lambda, \theta, \kappa, s)$ with
--   $$\begin{bmatrix}\kappa\\ s\\ 0\\ 0\end{bmatrix} = \begin{bmatrix} 0 & -c^{\mathsf T} & b^{\mathsf T} & \bar z\\ c & 0 & -A^{\mathsf T} & -\bar c\\ -b & A & 0 & \bar b\\ -\bar z & \bar c^{\mathsf T} & -\bar b^{\mathsf T} & 0\end{bmatrix}\begin{bmatrix}\tau\\ x\\ \lambda\\ \theta\end{bmatrix} + \begin{bmatrix}0\\0\\0\\ (x^0)^{\mathsf T}s^0 + 1\end{bmatrix}, \qquad (\tau, x, \kappa, s) \ge 0, \qquad \tau\kappa + x^{\mathsf T}s = 0;$$
--   a solution is **strictly complementary** if $\tau + \kappa > 0$ and $x + s > 0$.
--
--   The simplified HSD and HSD forms recast the LP pair (9.3) as a single monotone complementarity problem that always has a solution; Chapter 9 reads feasibility and infeasibility of (9.3) off its strictly complementary solutions.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` and matrices `Matrix (Fin m) (Fin n) ℝ`. The Euclidean norm is defined explicitly because Mathlib's default norm on `Fin N → ℝ` is the sup norm. The gradient is the vector of Fréchet partial derivatives `fderiv ℝ f u (Pi.single i 1)`; $f$ is a function on all of $\mathbb R^N$ (its values off $U$ play no role in the statements). $\lambda$ and $\theta$ carry no sign constraint. $\Omega_P$ and $\Omega_D$ are defined by optimality against every feasible point (no infimum), so they are empty when the optimum is not attained.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 24 (Ω); p. 27, Eqs. (2.11a)–(2.11b); p. 179, Eqs. (9.1)–(9.2); p. 180, Eqs. (9.3)–(9.5); p. 181; pp. 183–184, Eqs. (9.7)–(9.8); p. 240, Eq. (A.2)

import Mathlib

/-!
# Wright, *Primal-Dual Interior-Point Methods* (SIAM 1997), Chapter 9 and Appendix A: setting

* `norm2`, `gradVec` — the Euclidean norm (Notation, p. xvii) and the gradient vector `∇f(u)`.
* `FeasibleA2`, `IsLocalSolutionA2`, `IsGlobalSolutionA2` — the linearly constrained problem
  (A.2) `min f(u) s.t. Cu = d, Gu ≥ h, u ∈ U` and its local and global solutions (p. 240).
* `PrimalFeasible`, `DualFeasible`, `OmegaP`, `OmegaD`, `Omega`, `indexB`, `indexN` — the
  standard-form pair (9.3a)/(9.3b) (p. 180, = (2.1)/(2.2), p. 22), its solution sets (p. 24) and
  the index sets (2.11a)/(2.11b) (p. 27).
* `SelfDualFeasible`, `IsMLCPSolution`, `IsStrictlyComplementaryMLCP` — the self-dual linear
  program (9.1) and its mixed LCP (9.2) (p. 179); strictly complementary means `u + v > 0`.
* `IsSolution95`, `IsStrictlyComplementary95` — the mLCP (9.5) of the simplified HSD form (9.4)
  (p. 180); strictly complementary means `τ + κ > 0`, `x + s > 0` (p. 181).
* `bbar`, `cbar`, `zbar`, `IsSolution98`, `IsStrictlyComplementary98` — the data of the HSD form
  (9.7) (p. 183) and its mLCP (9.8) (p. 184).

Vectors are `Fin n → ℝ`, matrices `Matrix (Fin m) (Fin n) ℝ`, vector inequalities are
componentwise. No rank assumption on `A`.
-/

namespace WrightPDIPM.SelfDual

open Matrix

/-- The Euclidean norm `‖v‖ = (∑ᵢ vᵢ²)^{1/2}` (Notation, p. xvii). Mathlib's default norm on
`Fin N → ℝ` is the sup norm, hence the explicit definition. -/
noncomputable def norm2 {N : ℕ} (v : Fin N → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The gradient vector `∇f(u) ∈ ℝᴺ`, whose `i`-th entry is the partial derivative
`∂f/∂uᵢ(u) = Df(u)[eᵢ]` (the Fréchet derivative applied to the `i`-th unit vector). -/
noncomputable def gradVec {N : ℕ} (f : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) : Fin N → ℝ :=
  fun i => fderiv ℝ f u (Pi.single i (1 : ℝ))

/-- Feasibility for (A.2) (p. 240): `u ∈ U`, `Cu = d`, `Gu ≥ h`. -/
def FeasibleA2 {N k l : ℕ} (C : Matrix (Fin k) (Fin N) ℝ) (d : Fin k → ℝ)
    (G : Matrix (Fin l) (Fin N) ℝ) (h : Fin l → ℝ) (U : Set (Fin N → ℝ)) :
    Set (Fin N → ℝ) :=
  {u | u ∈ U ∧ C *ᵥ u = d ∧ ∀ i, h i ≤ (G *ᵥ u) i}

/-- A local solution of (A.2) (p. 240): `u*` is feasible and there is `ρ > 0` with
`f(u) ≥ f(u*)` for every feasible `u` with `‖u − u*‖ < ρ`. -/
def IsLocalSolutionA2 {N k l : ℕ} (f : (Fin N → ℝ) → ℝ) (C : Matrix (Fin k) (Fin N) ℝ)
    (d : Fin k → ℝ) (G : Matrix (Fin l) (Fin N) ℝ) (h : Fin l → ℝ) (U : Set (Fin N → ℝ))
    (ustar : Fin N → ℝ) : Prop :=
  ustar ∈ FeasibleA2 C d G h U ∧
    ∃ ρ > 0, ∀ u ∈ FeasibleA2 C d G h U, norm2 (u - ustar) < ρ → f ustar ≤ f u

/-- A global solution of (A.2) (p. 240, "taking ρ = ∞"): `u*` is feasible and
`f(u) ≥ f(u*)` for every feasible `u`. -/
def IsGlobalSolutionA2 {N k l : ℕ} (f : (Fin N → ℝ) → ℝ) (C : Matrix (Fin k) (Fin N) ℝ)
    (d : Fin k → ℝ) (G : Matrix (Fin l) (Fin N) ℝ) (h : Fin l → ℝ) (U : Set (Fin N → ℝ))
    (ustar : Fin N → ℝ) : Prop :=
  ustar ∈ FeasibleA2 C d G h U ∧ ∀ u ∈ FeasibleA2 C d G h U, f ustar ≤ f u

/-- Primal feasibility for (9.3a): `Ax = b`, `x ≥ 0`. -/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 ≤ x j

/-- Dual feasibility for (9.3b): `Aᵀλ + s = c`, `s ≥ 0`. -/
def DualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (lam : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ lam + s = c ∧ ∀ j, 0 ≤ s j

/-- The primal solution set `Ω_P = {x* | x* solves (9.3a)}` (p. 24): feasible points whose
objective `cᵀx*` is no larger than that of any feasible point. -/
def OmegaP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | PrimalFeasible A b x ∧ ∀ x', PrimalFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'}

/-- The dual solution set `Ω_D = {(λ*, s*) | (λ*, s*) solves (9.3b)}` (p. 24): feasible points
whose objective `bᵀλ*` is no smaller than that of any feasible point. -/
def OmegaD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | DualFeasible A c p.1 p.2 ∧
    ∀ lam' s', DualFeasible A c lam' s' → b ⬝ᵥ lam' ≤ b ⬝ᵥ p.1}

/-- The primal-dual solution set `Ω = Ω_P × Ω_D` (p. 24), as triples `(x*, λ*, s*)`. -/
def Omega {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | p.1 ∈ OmegaP A b c ∧ (p.2.1, p.2.2) ∈ OmegaD A b c}

/-- The index set `B` (2.11a) (p. 27): `j` with `x*_j ≠ 0` for some `x* ∈ Ω_P`. -/
def indexB {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ x ∈ OmegaP A b c, x j ≠ 0}

/-- The index set `N` (2.11b) (p. 27): `j` with `s*_j ≠ 0` for some `(λ*, s*) ∈ Ω_D`. -/
def indexN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ p ∈ OmegaD A b c, p.2 j ≠ 0}

/-- Feasibility of the self-dual linear program (9.1) (p. 179):
`M₁₁u + M₁₂w ≥ −f`, `−M₁₂ᵀu + M₂₂w = −g`, `u ≥ 0`, `w` free. -/
def SelfDualFeasible {p q : ℕ} (M11 : Matrix (Fin p) (Fin p) ℝ) (M12 : Matrix (Fin p) (Fin q) ℝ)
    (M22 : Matrix (Fin q) (Fin q) ℝ) (f : Fin p → ℝ) (g : Fin q → ℝ) : Prop :=
  ∃ (u : Fin p → ℝ) (w : Fin q → ℝ),
    (∀ i, -f i ≤ (M11 *ᵥ u + M12 *ᵥ w) i) ∧ -(M12ᵀ *ᵥ u) + M22 *ᵥ w = -g ∧ ∀ i, 0 ≤ u i

/-- A solution `(u, v, w)` of the mixed LCP (9.2) (p. 179):
`v = M₁₁u + M₁₂w + f`, `0 = −M₁₂ᵀu + M₂₂w + g`, `(u, v) ≥ 0`, `uᵀv = 0`. -/
def IsMLCPSolution {p q : ℕ} (M11 : Matrix (Fin p) (Fin p) ℝ) (M12 : Matrix (Fin p) (Fin q) ℝ)
    (M22 : Matrix (Fin q) (Fin q) ℝ) (f : Fin p → ℝ) (g : Fin q → ℝ)
    (u v : Fin p → ℝ) (w : Fin q → ℝ) : Prop :=
  v = M11 *ᵥ u + M12 *ᵥ w + f ∧ (0 : Fin q → ℝ) = -(M12ᵀ *ᵥ u) + M22 *ᵥ w + g ∧
    (∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ v i) ∧ u ⬝ᵥ v = 0

/-- A strictly complementary solution of (9.2) (p. 179): a solution with `u + v > 0`. -/
def IsStrictlyComplementaryMLCP {p q : ℕ} (M11 : Matrix (Fin p) (Fin p) ℝ)
    (M12 : Matrix (Fin p) (Fin q) ℝ) (M22 : Matrix (Fin q) (Fin q) ℝ) (f : Fin p → ℝ)
    (g : Fin q → ℝ) (u v : Fin p → ℝ) (w : Fin q → ℝ) : Prop :=
  IsMLCPSolution M11 M12 M22 f g u v w ∧ ∀ i, 0 < u i + v i

/-- A solution `(τ, x, λ, κ, s)` of the mLCP (9.5) of the simplified HSD form (p. 180):
(9.5a) `κ = −cᵀx + bᵀλ`, `s = cτ − Aᵀλ`, `0 = −bτ + Ax`, and
(9.5b) `(τ, x, κ, s) ≥ 0`, `τκ + xᵀs = 0`. `λ` is free. -/
def IsSolution95 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (κ : ℝ) (s : Fin n → ℝ) : Prop :=
  κ = -(c ⬝ᵥ x) + b ⬝ᵥ lam ∧ s = τ • c - Aᵀ *ᵥ lam ∧ (0 : Fin m → ℝ) = -(τ • b) + A *ᵥ x ∧
    0 ≤ τ ∧ (∀ j, 0 ≤ x j) ∧ 0 ≤ κ ∧ (∀ j, 0 ≤ s j) ∧ τ * κ + x ⬝ᵥ s = 0

/-- A strictly complementary solution of (9.5) (p. 181): a solution with `τ + κ > 0` and
`x + s > 0`. -/
def IsStrictlyComplementary95 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (κ : ℝ) (s : Fin n → ℝ) : Prop :=
  IsSolution95 A b c τ x lam κ s ∧ 0 < τ + κ ∧ ∀ j, 0 < x j + s j

/-- `b̄ = b − Ax⁰` (p. 183). -/
def bbar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x0 : Fin n → ℝ) :
    Fin m → ℝ :=
  b - A *ᵥ x0

/-- `c̄ = c − Aᵀλ⁰ − s⁰` (p. 183). -/
def cbar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (lam0 : Fin m → ℝ)
    (s0 : Fin n → ℝ) : Fin n → ℝ :=
  c - Aᵀ *ᵥ lam0 - s0

/-- `z̄ = cᵀx⁰ + 1 − bᵀλ⁰` (p. 183). -/
def zbar {m n : ℕ} (b : Fin m → ℝ) (c : Fin n → ℝ) (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) : ℝ :=
  c ⬝ᵥ x0 + 1 - b ⬝ᵥ lam0

/-- A solution `(τ, x, λ, θ, κ, s)` of the mLCP (9.8) of the HSD form (9.7) (p. 184), for the
initial point `(x⁰, λ⁰, s⁰)`: (9.8a)
`κ = −cᵀx + bᵀλ + z̄θ`, `s = cτ − Aᵀλ − c̄θ`, `0 = −bτ + Ax + b̄θ`,
`0 = −z̄τ + c̄ᵀx − b̄ᵀλ + ((x⁰)ᵀs⁰ + 1)`, and (9.8b) `(τ, x, κ, s) ≥ 0`, `τκ + xᵀs = 0`.
`λ` and `θ` are free. -/
def IsSolution98 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ) : Prop :=
  κ = -(c ⬝ᵥ x) + b ⬝ᵥ lam + zbar b c x0 lam0 * θ ∧
    s = τ • c - Aᵀ *ᵥ lam - θ • cbar A c lam0 s0 ∧
    (0 : Fin m → ℝ) = -(τ • b) + A *ᵥ x + θ • bbar A b x0 ∧
    (0 : ℝ) = -(zbar b c x0 lam0 * τ) + cbar A c lam0 s0 ⬝ᵥ x - bbar A b x0 ⬝ᵥ lam
      + (x0 ⬝ᵥ s0 + 1) ∧
    0 ≤ τ ∧ (∀ j, 0 ≤ x j) ∧ 0 ≤ κ ∧ (∀ j, 0 ≤ s j) ∧ τ * κ + x ⬝ᵥ s = 0

/-- A strictly complementary solution of (9.8): a solution with `τ + κ > 0` and `x + s > 0`
(the notion of p. 181 for (9.5), used for (9.8) in Theorems 9.5–9.6, p. 185). -/
def IsStrictlyComplementary98 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ) : Prop :=
  IsSolution98 A b c x0 lam0 s0 τ x lam θ κ s ∧ 0 < τ + κ ∧ ∀ j, 0 < x j + s j

end WrightPDIPM.SelfDual


