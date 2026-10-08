-- Prove2me | Definitions.Def_AugLagLLC_Penalty_Setting
-- name    : AugLagLLC_Penalty_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:23.25396+00:00
-- url     : https://prove2.me/theorems/5e877c17-7295-4bf1-821c-03a1f68d065a
-- title:
--   (2.1), (2.2), Algorithm 3.1, Definitions of §5.1–§5.2, pp. 3–5, 11, 13 — the problem, the PHR augmented Lagrangian and runs of Algorithm 3.1 with projected safeguards
-- statement:
--   This file fixes the objects of §2, §3 and §5 of Andreani, Birgin, Martínez and Schuverdt.
--
--   **Problem (2.1).** Let $f:\mathbb R^n\to\mathbb R$, $h_1:\mathbb R^n\to\mathbb R^{m_1}$, $g_1:\mathbb R^n\to\mathbb R^{p_1}$, $h_2:\mathbb R^n\to\mathbb R^{m_2}$, $g_2:\mathbb R^n\to\mathbb R^{p_2}$ and consider
--   $$\text{Minimize } f(x) \text{ subject to } h_1(x)=0,\ g_1(x)\le 0,\ h_2(x)=0,\ g_2(x)\le 0 .$$
--   The constraints $h_1, g_1$ are the *upper-level* constraints and $h_2, g_2$ the *lower-level* ones; $\Omega_1=\{x : h_1(x)=0,\ g_1(x)\le 0\}$ and $\Omega_2=\{x : h_2(x)=0,\ g_2(x)\le 0\}$. The standing assumption is that all these functions are continuously differentiable. Problem (5.1) of §5.1 is the case $p_1=p_2=0$. The file also records *twice continuously differentiable near $x_*$* (Assumptions 4 and 10).
--
--   **The augmented Lagrangian (2.2).** For $\rho>0$, $\lambda\in\mathbb R^{m_1}$, $\mu\in\mathbb R^{p_1}_+$,
--   $$L(x,\lambda,\mu,\rho)=f(x)+\frac{\rho}{2}\sum_{i=1}^{m_1}\Big([h_1(x)]_i+\frac{\lambda_i}{\rho}\Big)^2+\frac{\rho}{2}\sum_{i=1}^{p_1}\Big([g_1(x)]_i+\frac{\mu_i}{\rho}\Big)_+^2 .$$
--
--   **Algorithm 3.1.** The parameters are $\tau\in[0,1)$, $\gamma>1$, $\rho_1>0$, bounds $\bar\lambda_{\min}\le\bar\lambda_{\max}$ in $\mathbb R^{m_1}$ and $\bar\mu_{\max}\ge 0$ in $\mathbb R^{p_1}$, and tolerances $\varepsilon_k\ge 0$ with $\varepsilon_k\to 0$. From an arbitrary $x_0$, with $[\sigma_0]_i=\max\{0,[g_1(x_0)]_i\}$, $\bar\lambda_1\in[\bar\lambda_{\min},\bar\lambda_{\max}]$, $\bar\mu_1\in[0,\bar\mu_{\max}]$, each outer iteration $k=1,2,\dots$:
--
--   1. (Step 2) finds $x_k$, $v_k\in\mathbb R^{m_2}$, $u_k\in\mathbb R^{p_2}$ and $0\le\varepsilon_{k,1},\varepsilon_{k,2},\varepsilon_{k,3}\le\varepsilon_k$ with
--   $$\Big\|\nabla L(x_k,\bar\lambda_k,\bar\mu_k,\rho_k)+\sum_i [v_k]_i\nabla[h_2(x_k)]_i+\sum_i [u_k]_i\nabla[g_2(x_k)]_i\Big\|\le\varepsilon_{k,1}, \tag{3.1}$$
--   $[u_k]_i\ge 0$ and $[g_2(x_k)]_i\le\varepsilon_{k,2}$ (3.2), $[g_2(x_k)]_i<-\varepsilon_{k,2}\Rightarrow[u_k]_i=0$ (3.3), and $\|h_2(x_k)\|\le\varepsilon_{k,3}$ (3.4);
--   2. (Step 3) sets $[\lambda_{k+1}]_i=[\bar\lambda_k]_i+\rho_k[h_1(x_k)]_i$ (3.5), $[\mu_{k+1}]_i=\max\{0,[\bar\mu_k]_i+\rho_k[g_1(x_k)]_i\}$ and $[\sigma_k]_i=\max\{[g_1(x_k)]_i,-[\bar\mu_k]_i/\rho_k\}$ (3.7), and chooses $\bar\lambda_{k+1}\in[\bar\lambda_{\min},\bar\lambda_{\max}]$, $\bar\mu_{k+1}\in[0,\bar\mu_{\max}]$;
--   3. (Step 4) keeps $\rho_{k+1}=\rho_k$ if $\max\{\|h_1(x_k)\|_\infty,\|\sigma_k\|_\infty\}\le\tau\max\{\|h_1(x_{k-1})\|_\infty,\|\sigma_{k-1}\|_\infty\}$ and sets $\rho_{k+1}=\gamma\rho_k$ otherwise.
--
--   A *run* is a sequence produced this way in which Step 2 never fails. A *projected run* is a run that also uses the safeguard of the Definitions of §5.1 and §5.2: $[\bar\lambda_{k+1}]_i$ is the projection of $[\lambda_{k+1}]_i$ on $[[\bar\lambda_{\min}]_i,[\bar\lambda_{\max}]_i]$ and $[\bar\mu_{k+1}]_j$ is the projection of $[\mu_{k+1}]_j$ on $[0,[\bar\mu_{\max}]_j]$.
--
--   Every theorem of the mission is about projected runs of Algorithm 3.1.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; each vector-valued constraint map is a family of components indexed by `Fin m`. Continuous differentiability "on a sufficiently large and open domain" is read as $C^1$ on all of $\mathbb R^n$ (`IsC1`); "continuous second derivatives in a neighborhood of $x_*$" is `ContDiffAt ℝ 2` at $x_*$ (`IsC2At`), which for a finite order is $C^2$ on a neighbourhood. The paper's norm is arbitrary: (3.1) uses the Euclidean norm, and (3.4), Step 4 and every $\|\cdot\|_\infty$ use the sup norm of `Fin m → ℝ` (`h1vec`, `h2vec`). The run is a predicate on sequences indexed by $\mathbb N$, with `x 0` the initial point; the values $\rho_0,\bar\lambda_0,\bar\mu_0,v_0,u_0,\varepsilon_0$ are unused. The three tolerances $\varepsilon_{k,1},\varepsilon_{k,2},\varepsilon_{k,3}$ are kept separate. The gradient in (3.1) is the true gradient of the defined function $L$. The projection is written $\max\{a,\min\{b,t\}\}$; the safeguard Definition is applied for every outer iteration $k\ge1$.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, pp. 3–5, (2.1), (2.2), Algorithm 3.1 with (3.1)–(3.7); p. 11, Definition of §5.1 and Assumption 4; p. 13, Definition of §5.2 and Assumption 10

import Mathlib

open Filter
open scoped Topology

namespace AugLagLLC.Penalty

/-- Problem (2.1), p. 3: minimize `f x` subject to `h₁(x) = 0`, `g₁(x) ≤ 0` (the upper-level
constraints, defining `Ω₁`) and `h₂(x) = 0`, `g₂(x) ≤ 0` (the lower-level constraints, defining
`Ω₂`), on `ℝⁿ = EuclideanSpace ℝ (Fin n)`. Each vector-valued constraint map is stored as the
family of its components: `[h₁(x)]ᵢ` is `h1 i x` with `i : Fin m1` (the paper's `i = 1, …, m₁`).
Problem (5.1) of §5.1 is the case `p1 = p2 = 0`. -/
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

/-- Assumptions 4 and 10 (pp. 11, 13): all functions of the problem have continuous second
derivatives in a neighbourhood of `x` (`ContDiffAt ℝ 2`, which for a finite order means `C²` on a
neighbourhood of `x`). -/
def IsC2At (P : Problem n m1 p1 m2 p2) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ContDiffAt ℝ 2 P.f x ∧ (∀ i, ContDiffAt ℝ 2 (P.h1 i) x) ∧ (∀ i, ContDiffAt ℝ 2 (P.g1 i) x) ∧
    (∀ i, ContDiffAt ℝ 2 (P.h2 i) x) ∧ ∀ i, ContDiffAt ℝ 2 (P.g2 i) x

/-- `Ω₁ = {x | h₁(x) = 0, g₁(x) ≤ 0}`. -/
def Omega1 (P : Problem n m1 p1 m2 p2) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, P.h1 i x = 0) ∧ ∀ i, P.g1 i x ≤ 0}

/-- `Ω₂ = {x | h₂(x) = 0, g₂(x) ≤ 0}`. -/
def Omega2 (P : Problem n m1 p1 m2 p2) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, P.h2 i x = 0) ∧ ∀ i, P.g2 i x ≤ 0}

/-- The vector `h₁(x) ∈ ℝ^{m₁}`; its norm is the sup norm `‖h₁(x)‖∞`. -/
def h1vec (P : Problem n m1 p1 m2 p2) (x : EuclideanSpace ℝ (Fin n)) : Fin m1 → ℝ :=
  fun i => P.h1 i x

/-- The vector `h₂(x) ∈ ℝ^{m₂}`; its norm is the sup norm. -/
def h2vec (P : Problem n m1 p1 m2 p2) (x : EuclideanSpace ℝ (Fin n)) : Fin m2 → ℝ :=
  fun i => P.h2 i x

/-- The PHR augmented Lagrangian (2.2) with respect to `Ω₁`:
`L(x, λ, μ, ρ) = f(x) + ρ/2 ∑ᵢ ([h₁(x)]ᵢ + λᵢ/ρ)² + ρ/2 ∑ᵢ (([g₁(x)]ᵢ + μᵢ/ρ)₊)²`.
Meaningful for `ρ > 0` (the paper's domain). -/
noncomputable def augLag (P : Problem n m1 p1 m2 p2) (x : EuclideanSpace ℝ (Fin n))
    (lam : Fin m1 → ℝ) (mu : Fin p1 → ℝ) (ρ : ℝ) : ℝ :=
  P.f x + ρ / 2 * ∑ i, (P.h1 i x + lam i / ρ) ^ 2
    + ρ / 2 * ∑ i, (max (P.g1 i x + mu i / ρ) 0) ^ 2

/-- The first-order multiplier estimate (3.5): `[λₖ₊₁]ᵢ = [λ̄ₖ]ᵢ + ρₖ [h₁(xₖ)]ᵢ`.
`lamNext … k` is `λₖ₊₁`. -/
def lamNext (P : Problem n m1 p1 m2 p2) (x : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ)
    (lamBar : ℕ → Fin m1 → ℝ) (k : ℕ) : Fin m1 → ℝ :=
  fun i => lamBar k i + ρ k * P.h1 i (x k)

/-- The first-order multiplier estimate (3.7): `[μₖ₊₁]ᵢ = max{0, [μ̄ₖ]ᵢ + ρₖ [g₁(xₖ)]ᵢ}`.
`muNext … k` is `μₖ₊₁`. -/
noncomputable def muNext (P : Problem n m1 p1 m2 p2) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (ρ : ℕ → ℝ) (muBar : ℕ → Fin p1 → ℝ) (k : ℕ) : Fin p1 → ℝ :=
  fun i => max 0 (muBar k i + ρ k * P.g1 i (x k))

/-- `σₖ`: Step 1 sets `[σ₀]ᵢ = max{0, [g₁(x₀)]ᵢ}`; for `k ≥ 1`, (3.7) sets
`[σₖ]ᵢ = max{[g₁(xₖ)]ᵢ, −[μ̄ₖ]ᵢ/ρₖ}`. -/
noncomputable def sigma (P : Problem n m1 p1 m2 p2) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (ρ : ℕ → ℝ) (muBar : ℕ → Fin p1 → ℝ) (k : ℕ) : Fin p1 → ℝ :=
  fun i => if k = 0 then max 0 (P.g1 i (x 0)) else max (P.g1 i (x k)) (-(muBar k i) / ρ k)

/-- The parameters of Algorithm 3.1 (p. 4): `τ ∈ [0, 1)`, `γ > 1`, `ρ₁ > 0`,
`λ̄_min ≤ λ̄_max` componentwise, `μ̄_max ≥ 0`, and tolerances `εₖ ≥ 0` with `εₖ → 0`. -/
def IsParams (τ γ ρ1 : ℝ) (lamMin lamMax : Fin m1 → ℝ) (muMax : Fin p1 → ℝ) (ε : ℕ → ℝ) :
    Prop :=
  0 ≤ τ ∧ τ < 1 ∧ 1 < γ ∧ 0 < ρ1 ∧ (∀ i, lamMin i ≤ lamMax i) ∧ (∀ i, 0 ≤ muMax i) ∧
    (∀ k, 0 ≤ ε k) ∧ Tendsto ε atTop (𝓝 0)

/-- A run of Algorithm 3.1 (pp. 4–5) that never stops at Step 2.
`x 0` is the arbitrary initial point `x₀`; the outer iterations are `k = 1, 2, …`. The values
`ρ 0`, `lamBar 0`, `muBar 0`, `v 0`, `u 0` and `ε 0` are unused.
* Initialization: `ρ₁ = ρ1`, `λ̄₁ ∈ [λ̄_min, λ̄_max]`, `μ̄₁ ∈ [0, μ̄_max]`.
* Step 2, for every `k ≥ 1`: there are `ε_{k,1}, ε_{k,2}, ε_{k,3} ∈ [0, εₖ]` with (3.1) (Euclidean
  norm of the gradient of the true augmented Lagrangian plus the lower-level terms), (3.2), (3.3)
  and (3.4) (sup norm of `h₂(xₖ)`).
* Step 3 (3.6): `λ̄ₖ₊₁ ∈ [λ̄_min, λ̄_max]`, `μ̄ₖ₊₁ ∈ [0, μ̄_max]`.
* Step 4: `ρₖ₊₁ = ρₖ` if `max{‖h₁(xₖ)‖∞, ‖σₖ‖∞} ≤ τ max{‖h₁(xₖ₋₁)‖∞, ‖σₖ₋₁‖∞}`, else `γ ρₖ`
  (at `k = 1` the comparison is with `x₀` and `σ₀`). -/
def IsRun (P : Problem n m1 p1 m2 p2) (τ γ ρ1 : ℝ) (lamMin lamMax : Fin m1 → ℝ)
    (muMax : Fin p1 → ℝ) (ε : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ)
    (lamBar : ℕ → Fin m1 → ℝ) (muBar : ℕ → Fin p1 → ℝ) (v : ℕ → Fin m2 → ℝ)
    (u : ℕ → Fin p2 → ℝ) : Prop :=
  ρ 1 = ρ1 ∧ (∀ i, lamMin i ≤ lamBar 1 i ∧ lamBar 1 i ≤ lamMax i) ∧
    (∀ i, 0 ≤ muBar 1 i ∧ muBar 1 i ≤ muMax i) ∧
    ∀ k, 1 ≤ k →
      (∃ ε1 ε2 ε3 : ℝ, 0 ≤ ε1 ∧ ε1 ≤ ε k ∧ 0 ≤ ε2 ∧ ε2 ≤ ε k ∧ 0 ≤ ε3 ∧ ε3 ≤ ε k ∧
        -- (3.1)
        ‖gradient (fun y => P.augLag y (lamBar k) (muBar k) (ρ k)) (x k)
            + ∑ i, v k i • gradient (P.h2 i) (x k)
            + ∑ i, u k i • gradient (P.g2 i) (x k)‖ ≤ ε1 ∧
        -- (3.2)
        (∀ i, 0 ≤ u k i ∧ P.g2 i (x k) ≤ ε2) ∧
        -- (3.3)
        (∀ i, P.g2 i (x k) < -ε2 → u k i = 0) ∧
        -- (3.4)
        ‖P.h2vec (x k)‖ ≤ ε3) ∧
      -- (3.6) and the box for `μ̄ₖ₊₁`
      (∀ i, lamMin i ≤ lamBar (k + 1) i ∧ lamBar (k + 1) i ≤ lamMax i) ∧
      (∀ i, 0 ≤ muBar (k + 1) i ∧ muBar (k + 1) i ≤ muMax i) ∧
      -- Step 4
      ρ (k + 1) =
        if max ‖P.h1vec (x k)‖ ‖P.sigma x ρ muBar k‖ ≤
            τ * max ‖P.h1vec (x (k - 1))‖ ‖P.sigma x ρ muBar (k - 1)‖
        then ρ k else γ * ρ k

/-- A run of Algorithm 3.1 with the safeguarded multipliers of the Definitions of §5.1 (p. 11)
and §5.2 (p. 13): for every outer iteration `k ≥ 1`, `[λ̄ₖ₊₁]ᵢ` is the projection of `[λₖ₊₁]ᵢ`
on `[[λ̄_min]ᵢ, [λ̄_max]ᵢ]` and `[μ̄ₖ₊₁]ⱼ` is the projection of `[μₖ₊₁]ⱼ` on `[0, [μ̄_max]ⱼ]`. -/
def IsProjRun (P : Problem n m1 p1 m2 p2) (τ γ ρ1 : ℝ) (lamMin lamMax : Fin m1 → ℝ)
    (muMax : Fin p1 → ℝ) (ε : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ)
    (lamBar : ℕ → Fin m1 → ℝ) (muBar : ℕ → Fin p1 → ℝ) (v : ℕ → Fin m2 → ℝ)
    (u : ℕ → Fin p2 → ℝ) : Prop :=
  P.IsRun τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u ∧
    ∀ k, 1 ≤ k →
      (∀ i, lamBar (k + 1) i = max (lamMin i) (min (lamMax i) (P.lamNext x ρ lamBar k i))) ∧
      ∀ j, muBar (k + 1) j = max 0 (min (muMax j) (P.muNext x ρ muBar k j))

end Problem

end AugLagLLC.Penalty


