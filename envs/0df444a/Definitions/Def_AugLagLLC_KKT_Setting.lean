-- Prove2me | Definitions.Def_AugLagLLC_KKT_Setting
-- name    : AugLagLLC_KKT_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:08.139603+00:00
-- url     : https://prove2.me/theorems/d4f50619-95b0-442a-afe5-378e3f919dea
-- title:
--   (2.1), (2.2), Algorithm 3.1, pp. 3–5 — the problem, the PHR augmented Lagrangian and runs of Algorithm 3.1
-- statement:
--   This file sets up the problem and the algorithm of Andreani, Birgin, Martínez and Schuverdt.
--
--   **Problem (2.1).** Let $f:\mathbb R^n\to\mathbb R$, $h_1:\mathbb R^n\to\mathbb R^{m_1}$, $g_1:\mathbb R^n\to\mathbb R^{p_1}$, $h_2:\mathbb R^n\to\mathbb R^{m_2}$, $g_2:\mathbb R^n\to\mathbb R^{p_2}$ and consider
--   $$\text{minimize } f(x)\quad\text{subject to}\quad h_1(x)=0,\ g_1(x)\le 0,\ h_2(x)=0,\ g_2(x)\le 0 .$$
--   The standing assumption is that all these functions have continuous first derivatives. Write $\Omega_1=\{x : h_1(x)=0,\ g_1(x)\le 0\}$ (upper-level constraints) and $\Omega_2=\{x : h_2(x)=0,\ g_2(x)\le 0\}$ (lower-level constraints), and $[v]_i$ for the $i$-th component of a vector $v$.
--
--   **Augmented Lagrangian (2.2).** For $\rho>0$, $\lambda\in\mathbb R^{m_1}$, $\mu\in\mathbb R^{p_1}_+$,
--   $$L(x,\lambda,\mu,\rho)=f(x)+\frac{\rho}{2}\sum_{i=1}^{m_1}\Big([h_1(x)]_i+\frac{\lambda_i}{\rho}\Big)^2+\frac{\rho}{2}\sum_{i=1}^{p_1}\Big(\Big[[g_1(x)]_i+\frac{\mu_i}{\rho}\Big]_+\Big)^2 .$$
--
--   **Algorithm 3.1.** The parameters are $\tau\in[0,1)$, $\gamma>1$, $\rho_1>0$, bounds $\bar\lambda_{\min}\le\bar\lambda_{\max}$ in $\mathbb R^{m_1}$ and $\bar\mu_{\max}\ge 0$ in $\mathbb R^{p_1}$, and tolerances $\varepsilon_k\ge 0$ with $\varepsilon_k\to 0$. A run consists of an initial point $x_0$ and, for the outer iterations $k=1,2,\dots$, iterates $x_k$, penalty parameters $\rho_k$, safeguarded multipliers $\bar\lambda_k\in[\bar\lambda_{\min},\bar\lambda_{\max}]$, $\bar\mu_k\in[0,\bar\mu_{\max}]$ and lower-level multipliers $v_k\in\mathbb R^{m_2}$, $u_k\in\mathbb R^{p_2}$, such that:
--
--   1. $\rho_1$ is the given parameter, and $\bar\lambda_1$, $\bar\mu_1$ lie in their boxes;
--   2. (Step 2) for every $k\ge 1$ there are $\varepsilon_{k,1},\varepsilon_{k,2},\varepsilon_{k,3}\in[0,\varepsilon_k]$ with
--   $$\Big\|\nabla L(x_k,\bar\lambda_k,\bar\mu_k,\rho_k)+\sum_{i=1}^{m_2}[v_k]_i\nabla[h_2(x_k)]_i+\sum_{i=1}^{p_2}[u_k]_i\nabla[g_2(x_k)]_i\Big\|\le\varepsilon_{k,1},$$
--   $[u_k]_i\ge 0$ and $[g_2(x_k)]_i\le\varepsilon_{k,2}$ for all $i$, $[g_2(x_k)]_i<-\varepsilon_{k,2}\Rightarrow[u_k]_i=0$, and $\|h_2(x_k)\|\le\varepsilon_{k,3}$ ((3.1)–(3.4));
--   3. (Step 3) the next safeguarded multipliers $\bar\lambda_{k+1}$, $\bar\mu_{k+1}$ lie in their boxes (3.6);
--   4. (Step 4) $\rho_{k+1}=\rho_k$ if $\max\{\|h_1(x_k)\|_\infty,\|\sigma_k\|_\infty\}\le\tau\max\{\|h_1(x_{k-1})\|_\infty,\|\sigma_{k-1}\|_\infty\}$, and $\rho_{k+1}=\gamma\rho_k$ otherwise.
--
--   The first-order multiplier estimates and the complementarity measure are
--   $$[\lambda_{k+1}]_i=[\bar\lambda_k]_i+\rho_k[h_1(x_k)]_i,\qquad [\mu_{k+1}]_i=\max\{0,[\bar\mu_k]_i+\rho_k[g_1(x_k)]_i\},$$
--   $$[\sigma_k]_i=\max\Big\{[g_1(x_k)]_i,-\frac{[\bar\mu_k]_i}{\rho_k}\Big\}\ (k\ge 1),\qquad [\sigma_0]_i=\max\{0,[g_1(x_0)]_i\}.$$
--
--   A run never stops at Step 2: this is the standing assumption of §4 of the paper, built into the definition.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; the vector-valued constraints are given by their components, indexed by `Fin m` (0-based in Lean, $1,\dots,m$ in the paper). "Continuous first derivatives on a sufficiently large and open domain" is read as `ContDiff ℝ 1` on all of $\mathbb R^n$ (`IsC1`). The norm in (3.1) is the Euclidean norm; $\|h_2(x_k)\|$ in (3.4) and the norms of Step 4 are the sup norm on `Fin m → ℝ`. The paper's $\|\cdot\|$ is an arbitrary norm, and only $\varepsilon_k\to 0$ matters, so the choice changes nothing. $\nabla L$ is the true gradient of the defined function (2.2). Sequences are indexed by `ℕ`; index $0$ holds $x_0$ and $\sigma_0$, and the values $\rho_0$, $\bar\lambda_0$, $\bar\mu_0$, $v_0$, $u_0$, $\varepsilon_0$ are unused. The three tolerances $\varepsilon_{k,1},\varepsilon_{k,2},\varepsilon_{k,3}$ are kept separate, as on the page. Step 3 only requires the safeguarded multipliers to stay in their boxes; the projections the paper calls "usual" are not imposed.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, p. 3, (2.1), (2.2); pp. 4–5, Algorithm 3.1, (3.1)–(3.7); p. 5, standing assumption of §4

import Mathlib
import Definitions.Def_AugLagLLC_KKT_ConstraintQualifications

namespace AugLagLLC.KKT

open Filter Topology

/-- Problem (2.1): minimize `f x` subject to `h1 x = 0`, `g1 x ≤ 0` (the upper-level constraints,
defining `Ω₁`) and `h2 x = 0`, `g2 x ≤ 0` (the lower-level constraints, defining `Ω₂`), on
`ℝⁿ = EuclideanSpace ℝ (Fin n)`. Each vector-valued constraint is given by its components:
`[h₁(x)]ᵢ` is `h1 i x` with `i : Fin m1` (the paper's `i = 1, …, m₁`). -/
structure Problem (n m1 p1 m2 p2 : ℕ) where
  f  : EuclideanSpace ℝ (Fin n) → ℝ
  h1 : Fin m1 → EuclideanSpace ℝ (Fin n) → ℝ
  g1 : Fin p1 → EuclideanSpace ℝ (Fin n) → ℝ
  h2 : Fin m2 → EuclideanSpace ℝ (Fin n) → ℝ
  g2 : Fin p2 → EuclideanSpace ℝ (Fin n) → ℝ

namespace Problem

variable {n m1 p1 m2 p2 : ℕ}

/-- Standing assumption of §2 (p. 3): all functions of (2.1) have continuous first derivatives,
read as `C¹` on all of `ℝⁿ`. -/
def IsC1 (P : Problem n m1 p1 m2 p2) : Prop :=
  ContDiff ℝ 1 P.f ∧ (∀ i, ContDiff ℝ 1 (P.h1 i)) ∧ (∀ i, ContDiff ℝ 1 (P.g1 i)) ∧
    (∀ i, ContDiff ℝ 1 (P.h2 i)) ∧ ∀ i, ContDiff ℝ 1 (P.g2 i)

/-- `Ω₁ = {x | h₁(x) = 0, g₁(x) ≤ 0}`. -/
def Omega1 (P : Problem n m1 p1 m2 p2) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, P.h1 i x = 0) ∧ ∀ i, P.g1 i x ≤ 0}

/-- `Ω₂ = {x | h₂(x) = 0, g₂(x) ≤ 0}`. -/
def Omega2 (P : Problem n m1 p1 m2 p2) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, P.h2 i x = 0) ∧ ∀ i, P.g2 i x ≤ 0}

/-- The PHR augmented Lagrangian (2.2) with respect to `Ω₁`:
`L(x, λ, μ, ρ) = f(x) + ρ/2 ∑ᵢ ([h₁(x)]ᵢ + λᵢ/ρ)² + ρ/2 ∑ᵢ (([g₁(x)]ᵢ + μᵢ/ρ)₊)²`.
Meaningful for `ρ > 0` (the paper's domain). -/
noncomputable def augLag (P : Problem n m1 p1 m2 p2) (x : EuclideanSpace ℝ (Fin n))
    (lam : Fin m1 → ℝ) (mu : Fin p1 → ℝ) (ρ : ℝ) : ℝ :=
  P.f x + ρ / 2 * ∑ i, (P.h1 i x + lam i / ρ) ^ 2
    + ρ / 2 * ∑ i, (max (P.g1 i x + mu i / ρ) 0) ^ 2

/-- The first-order multiplier estimate (3.5): `[λₖ₊₁]ᵢ = [λ̄ₖ]ᵢ + ρₖ [h₁(xₖ)]ᵢ`. -/
def lamNext (P : Problem n m1 p1 m2 p2) (x : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ)
    (lamBar : ℕ → Fin m1 → ℝ) (k : ℕ) : Fin m1 → ℝ :=
  fun i => lamBar k i + ρ k * P.h1 i (x k)

/-- The first-order multiplier estimate (3.7): `[μₖ₊₁]ᵢ = max{0, [μ̄ₖ]ᵢ + ρₖ [g₁(xₖ)]ᵢ}`. -/
noncomputable def muNext (P : Problem n m1 p1 m2 p2) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (ρ : ℕ → ℝ) (muBar : ℕ → Fin p1 → ℝ) (k : ℕ) : Fin p1 → ℝ :=
  fun i => max 0 (muBar k i + ρ k * P.g1 i (x k))

/-- The infeasibility/complementarity measure: `[σ₀]ᵢ = max{0, [g₁(x₀)]ᵢ}` (Step 1) and
`[σₖ]ᵢ = max{[g₁(xₖ)]ᵢ, −[μ̄ₖ]ᵢ/ρₖ}` for `k ≥ 1` ((3.7)). -/
noncomputable def sigma (P : Problem n m1 p1 m2 p2) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (ρ : ℕ → ℝ) (muBar : ℕ → Fin p1 → ℝ) (k : ℕ) : Fin p1 → ℝ :=
  fun i => if k = 0 then max 0 (P.g1 i (x 0)) else max (P.g1 i (x k)) (-(muBar k i) / ρ k)

/-- The parameters of Algorithm 3.1 (p. 4): `τ ∈ [0, 1)`, `γ > 1`, `ρ₁ > 0`,
`λ̄_min ≤ λ̄_max` componentwise, `μ̄_max ≥ 0`, and tolerances `εₖ ≥ 0` with `εₖ → 0`. -/
def IsParams (τ γ ρ1 : ℝ) (lamMin lamMax : Fin m1 → ℝ) (muMax : Fin p1 → ℝ) (ε : ℕ → ℝ) :
    Prop :=
  0 ≤ τ ∧ τ < 1 ∧ 1 < γ ∧ 0 < ρ1 ∧ (∀ i, lamMin i ≤ lamMax i) ∧ (∀ i, 0 ≤ muMax i) ∧
    (∀ k, 0 ≤ ε k) ∧ Tendsto ε atTop (𝓝 0)

/-- A run of Algorithm 3.1 (pp. 4–5) that never stops at Step 2 (the standing assumption of §4).
`x 0` is the initial point `x₀`; the outer iterations are `k = 1, 2, …`. The values `ρ 0`,
`lamBar 0`, `muBar 0`, `v 0`, `u 0` and `ε 0` are unused.
* Initialization: `ρ₁ = ρ1`, `λ̄₁ ∈ [λ̄_min, λ̄_max]`, `μ̄₁ ∈ [0, μ̄_max]`.
* Step 2, for every `k ≥ 1`: there are `ε_{k,1}, ε_{k,2}, ε_{k,3} ∈ [0, εₖ]` with (3.1) (Euclidean
  norm of the gradient of the true augmented Lagrangian plus the lower-level terms), (3.2), (3.3)
  and (3.4) (sup norm of `h₂(xₖ)`).
* Step 3 (3.6): `λ̄ₖ₊₁ ∈ [λ̄_min, λ̄_max]`, `μ̄ₖ₊₁ ∈ [0, μ̄_max]`.
* Step 4: `ρₖ₊₁ = ρₖ` if `max{‖h₁(xₖ)‖∞, ‖σₖ‖∞} ≤ τ max{‖h₁(xₖ₋₁)‖∞, ‖σₖ₋₁‖∞}`, else `γ ρₖ`. -/
def IsRun (P : Problem n m1 p1 m2 p2) (τ γ ρ1 : ℝ) (lamMin lamMax : Fin m1 → ℝ)
    (muMax : Fin p1 → ℝ) (ε : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ)
    (lamBar : ℕ → Fin m1 → ℝ) (muBar : ℕ → Fin p1 → ℝ) (v : ℕ → Fin m2 → ℝ)
    (u : ℕ → Fin p2 → ℝ) : Prop :=
  ρ 1 = ρ1 ∧ (∀ i, lamMin i ≤ lamBar 1 i ∧ lamBar 1 i ≤ lamMax i) ∧
    (∀ i, 0 ≤ muBar 1 i ∧ muBar 1 i ≤ muMax i) ∧
    ∀ k, 1 ≤ k →
      (∃ ε1 ε2 ε3 : ℝ, 0 ≤ ε1 ∧ ε1 ≤ ε k ∧ 0 ≤ ε2 ∧ ε2 ≤ ε k ∧ 0 ≤ ε3 ∧ ε3 ≤ ε k ∧
        ‖gradient (fun y => P.augLag y (lamBar k) (muBar k) (ρ k)) (x k)
            + ∑ i, v k i • gradient (P.h2 i) (x k)
            + ∑ i, u k i • gradient (P.g2 i) (x k)‖ ≤ ε1 ∧
        (∀ i, 0 ≤ u k i ∧ P.g2 i (x k) ≤ ε2) ∧
        (∀ i, P.g2 i (x k) < -ε2 → u k i = 0) ∧
        ‖(fun i => P.h2 i (x k) : Fin m2 → ℝ)‖ ≤ ε3) ∧
      (∀ i, lamMin i ≤ lamBar (k + 1) i ∧ lamBar (k + 1) i ≤ lamMax i) ∧
      (∀ i, 0 ≤ muBar (k + 1) i ∧ muBar (k + 1) i ≤ muMax i) ∧
      ρ (k + 1) =
        if max ‖(fun i => P.h1 i (x k) : Fin m1 → ℝ)‖ ‖P.sigma x ρ muBar k‖ ≤
            τ * max ‖(fun i => P.h1 i (x (k - 1)) : Fin m1 → ℝ)‖ ‖P.sigma x ρ muBar (k - 1)‖
        then ρ k else γ * ρ k

end Problem

end AugLagLLC.KKT


