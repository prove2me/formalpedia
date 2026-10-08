-- Prove2me | Definitions.Def_AugLagLLC_Feas_Setting
-- name    : AugLagLLC_Feas_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:21.285261+00:00
-- url     : https://prove2.me/theorems/c84599a4-4244-4282-95a0-ee6d6120df42
-- title:
--   (2.1), (2.2), Algorithm 3.1, (4.1), CPLD, pp. 2–6 — the problem, the PHR augmented Lagrangian, runs of Algorithm 3.1, KKT points and CPLD
-- statement:
--   This file fixes the objects of §2–§4 of Andreani, Birgin, Martínez and Schuverdt.
--
--   **Problem (2.1).** Let $f:\mathbb R^n\to\mathbb R$, $h_1:\mathbb R^n\to\mathbb R^{m_1}$, $g_1:\mathbb R^n\to\mathbb R^{p_1}$, $h_2:\mathbb R^n\to\mathbb R^{m_2}$, $g_2:\mathbb R^n\to\mathbb R^{p_2}$ and consider
--   $$\text{Minimize } f(x) \text{ subject to } h_1(x)=0,\ g_1(x)\le 0,\ h_2(x)=0,\ g_2(x)\le 0 .$$
--   The constraints $h_1, g_1$ are the *upper-level* constraints and $h_2, g_2$ the *lower-level* ones; $\Omega_1=\{x : h_1(x)=0,\ g_1(x)\le 0\}$ and $\Omega_2=\{x : h_2(x)=0,\ g_2(x)\le 0\}$. The standing assumption is that all these functions are continuously differentiable.
--
--   **The augmented Lagrangian (2.2).** For $\rho>0$, $\lambda\in\mathbb R^{m_1}$, $\mu\in\mathbb R^{p_1}_+$,
--   $$L(x,\lambda,\mu,\rho)=f(x)+\frac{\rho}{2}\sum_{i=1}^{m_1}\Big([h_1(x)]_i+\frac{\lambda_i}{\rho}\Big)^2+\frac{\rho}{2}\sum_{i=1}^{p_1}\Big([g_1(x)]_i+\frac{\mu_i}{\rho}\Big)_+^2 .$$
--   The *upper-level infeasibility*, objective of problem (4.1), is $\tfrac12\big[\sum_i [h_1(x)]_i^2+\sum_i \max\{0,[g_1(x)]_i\}^2\big]$.
--
--   **Algorithm 3.1.** The parameters are $\tau\in[0,1)$, $\gamma>1$, $\rho_1>0$, bounds $\bar\lambda_{\min}\le\bar\lambda_{\max}$ in $\mathbb R^{m_1}$ and $\bar\mu_{\max}\ge 0$ in $\mathbb R^{p_1}$, and tolerances $\varepsilon_k\ge 0$ with $\varepsilon_k\to 0$. From an arbitrary $x_0$, with $[\sigma_0]_i=\max\{0,[g_1(x_0)]_i\}$, $\bar\lambda_1\in[\bar\lambda_{\min},\bar\lambda_{\max}]$, $\bar\mu_1\in[0,\bar\mu_{\max}]$, each outer iteration $k=1,2,\dots$:
--
--   1. (Step 2) finds $x_k$, $v_k\in\mathbb R^{m_2}$, $u_k\in\mathbb R^{p_2}$ and $0\le\varepsilon_{k,1},\varepsilon_{k,2},\varepsilon_{k,3}\le\varepsilon_k$ with
--   $$\Big\|\nabla L(x_k,\bar\lambda_k,\bar\mu_k,\rho_k)+\sum_i [v_k]_i\nabla[h_2(x_k)]_i+\sum_i [u_k]_i\nabla[g_2(x_k)]_i\Big\|\le\varepsilon_{k,1}, \tag{3.1}$$
--   $[u_k]_i\ge 0$ and $[g_2(x_k)]_i\le\varepsilon_{k,2}$ (3.2), $[g_2(x_k)]_i<-\varepsilon_{k,2}\Rightarrow[u_k]_i=0$ (3.3), and $\|h_2(x_k)\|\le\varepsilon_{k,3}$ (3.4);
--   2. (Step 3) chooses $\bar\lambda_{k+1}\in[\bar\lambda_{\min},\bar\lambda_{\max}]$, $\bar\mu_{k+1}\in[0,\bar\mu_{\max}]$, and sets $[\lambda_{k+1}]_i=[\bar\lambda_k]_i+\rho_k[h_1(x_k)]_i$, $[\mu_{k+1}]_i=\max\{0,[\bar\mu_k]_i+\rho_k[g_1(x_k)]_i\}$, $[\sigma_k]_i=\max\{[g_1(x_k)]_i,-[\bar\mu_k]_i/\rho_k\}$;
--   3. (Step 4) keeps $\rho_{k+1}=\rho_k$ if $\max\{\|h_1(x_k)\|_\infty,\|\sigma_k\|_\infty\}\le\tau\max\{\|h_1(x_{k-1})\|_\infty,\|\sigma_{k-1}\|_\infty\}$ and sets $\rho_{k+1}=\gamma\rho_k$ otherwise.
--
--   A *run* is a sequence produced this way in which Step 2 never fails, the standing assumption of §4.
--
--   **KKT points and CPLD.** For an objective $F$, equality constraints $H_i$ and inequality constraints $G_j$, a point $x$ is a *KKT point* if it is feasible and there are multipliers $a_i$ and $b_j\ge0$, with $b_j=0$ whenever $G_j(x)<0$, such that $\nabla F(x)+\sum_i a_i\nabla H_i(x)+\sum_j b_j\nabla G_j(x)=0$. The point $x$ satisfies the *constant positive linear dependence* condition (CPLD, Qi and Wei) if, whenever a nontrivial null combination $\sum_{i\in I}a_i\nabla H_i(x)+\sum_{j\in J}b_j\nabla G_j(x)=0$ of equality gradients and active inequality gradients exists with $b_j\ge 0$, the gradients $\{\nabla H_i(z)\}_{i\in I}\cup\{\nabla G_j(z)\}_{j\in J}$ are linearly dependent for every $z$ in a neighbourhood of $x$.
--
--   These objects carry every statement of the mission: Theorem 4.1 is about runs, their limit points, KKT points of (4.1) and CPLD with respect to $\Omega_2$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; each vector-valued constraint map is a family of components indexed by `Fin m`. Continuous differentiability "on a sufficiently large and open domain" is read as $C^1$ on all of $\mathbb R^n$ (`IsC1`). The paper's norm is arbitrary: (3.1) uses the Euclidean norm, and (3.4) and Step 4 use the sup norm of `Fin m → ℝ`; the results are invariant because only $\varepsilon_k\to0$ enters. The run is a predicate on sequences indexed by $\mathbb N$, with `x 0` the initial point; the values $\rho_0,\bar\lambda_0,\bar\mu_0,v_0,u_0,\varepsilon_0$ are unused. The three tolerances $\varepsilon_{k,1},\varepsilon_{k,2},\varepsilon_{k,3}$ are kept separate. KKT and CPLD are stated for arbitrary finite index types; CPLD quantifies over all index subsets $I$, $J$ (with $J$ active), which is equivalent to the prose's "the gradients involved in that combination", and carries no feasibility clause. Linear independence is that of the family indexed by $I\oplus J$, so repeated gradients count as dependent.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, pp. 2–6, the definition of CPLD (pp. 2–3), (2.1), (2.2), Algorithm 3.1 with (3.1)–(3.7), and problem (4.1)

import Mathlib

open Filter
open scoped Topology

namespace AugLagLLC.Feas

/-- Problem (2.1), p. 3: minimize `f x` subject to `h₁(x) = 0`, `g₁(x) ≤ 0` (upper level) and
`h₂(x) = 0`, `g₂(x) ≤ 0` (lower level). Each vector-valued constraint map is stored as the family of
its components; the paper's index `i ∈ {1, …, m₁}` is `i : Fin m1`. -/
structure Problem (n m1 p1 m2 p2 : ℕ) where
  f  : EuclideanSpace ℝ (Fin n) → ℝ
  h1 : Fin m1 → EuclideanSpace ℝ (Fin n) → ℝ
  g1 : Fin p1 → EuclideanSpace ℝ (Fin n) → ℝ
  h2 : Fin m2 → EuclideanSpace ℝ (Fin n) → ℝ
  g2 : Fin p2 → EuclideanSpace ℝ (Fin n) → ℝ

namespace Problem

variable {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2)

/-- Standing assumption of §2 (p. 3): every function of the problem has continuous first
derivatives (read as `C¹` on all of `ℝⁿ`). -/
def IsC1 : Prop :=
  ContDiff ℝ 1 P.f ∧ (∀ i, ContDiff ℝ 1 (P.h1 i)) ∧ (∀ i, ContDiff ℝ 1 (P.g1 i)) ∧
    (∀ i, ContDiff ℝ 1 (P.h2 i)) ∧ (∀ i, ContDiff ℝ 1 (P.g2 i))

/-- `Ω₁ = {x | h₁(x) = 0, g₁(x) ≤ 0}` (p. 3). -/
def Omega1 : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, P.h1 i x = 0) ∧ ∀ i, P.g1 i x ≤ 0}

/-- `Ω₂ = {x | h₂(x) = 0, g₂(x) ≤ 0}` (p. 3). -/
def Omega2 : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, P.h2 i x = 0) ∧ ∀ i, P.g2 i x ≤ 0}

end Problem

variable {n m1 p1 m2 p2 : ℕ}

/-- The PHR augmented Lagrangian (2.2) with respect to `Ω₁`:
`L(x, λ, μ, ρ) = f(x) + ρ/2 Σᵢ ([h₁(x)]ᵢ + λᵢ/ρ)² + ρ/2 Σᵢ ([g₁(x)]ᵢ + μᵢ/ρ)₊²`.
The paper defines it for `ρ > 0`; the run below only evaluates it there. -/
noncomputable def augLag (P : Problem n m1 p1 m2 p2) (x : EuclideanSpace ℝ (Fin n))
    (lam : Fin m1 → ℝ) (mu : Fin p1 → ℝ) (ρ : ℝ) : ℝ :=
  P.f x + ρ / 2 * ∑ i, (P.h1 i x + lam i / ρ) ^ 2
    + ρ / 2 * ∑ i, (max (P.g1 i x + mu i / ρ) 0) ^ 2

/-- The upper-level infeasibility measure, the objective of problem (4.1):
`½ [Σᵢ [h₁(x)]ᵢ² + Σᵢ max{0, [g₁(x)]ᵢ}²]`. -/
noncomputable def infeas (P : Problem n m1 p1 m2 p2) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 / 2 * (∑ i, (P.h1 i x) ^ 2 + ∑ i, (max 0 (P.g1 i x)) ^ 2)

/-- The vector `h₁(x) ∈ ℝ^{m₁}`; its norm `‖·‖` on `Fin m1 → ℝ` is the sup norm `‖·‖∞`. -/
def h1vec (P : Problem n m1 p1 m2 p2) (x : EuclideanSpace ℝ (Fin n)) : Fin m1 → ℝ :=
  fun i => P.h1 i x

/-- The vector `h₂(x) ∈ ℝ^{m₂}`; its norm on `Fin m2 → ℝ` is the sup norm. -/
def h2vec (P : Problem n m1 p1 m2 p2) (x : EuclideanSpace ℝ (Fin n)) : Fin m2 → ℝ :=
  fun i => P.h2 i x

/-- (3.5): `[λₖ₊₁]ᵢ = [λ̄ₖ]ᵢ + ρₖ [h₁(xₖ)]ᵢ`. -/
def lamNext (P : Problem n m1 p1 m2 p2) (x : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ)
    (lamBar : ℕ → Fin m1 → ℝ) (k : ℕ) : Fin m1 → ℝ :=
  fun i => lamBar k i + ρ k * P.h1 i (x k)

/-- (3.7): `[μₖ₊₁]ᵢ = max{0, [μ̄ₖ]ᵢ + ρₖ [g₁(xₖ)]ᵢ}`. -/
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
def ValidParams (τ γ ρ1 : ℝ) (lamMin lamMax : Fin m1 → ℝ) (muMax : Fin p1 → ℝ)
    (ε : ℕ → ℝ) : Prop :=
  0 ≤ τ ∧ τ < 1 ∧ 1 < γ ∧ 0 < ρ1 ∧ (∀ i, lamMin i ≤ lamMax i) ∧ (∀ i, 0 ≤ muMax i) ∧
    (∀ k, 0 ≤ ε k) ∧ Tendsto ε atTop (𝓝 0)

/-- Step 2 of Algorithm 3.1 at outer iteration `k`: `x k` satisfies (3.1)–(3.4) with the
multipliers `v k`, `u k` and some tolerances `0 ≤ ε_{k,1}, ε_{k,2}, ε_{k,3} ≤ εₖ`. In (3.1) the
norm is the Euclidean norm of `ℝⁿ`; in (3.4) it is the sup norm of `ℝ^{m₂}`. -/
def Step2 (P : Problem n m1 p1 m2 p2) (ε : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (ρ : ℕ → ℝ) (lamBar : ℕ → Fin m1 → ℝ) (muBar : ℕ → Fin p1 → ℝ) (v : ℕ → Fin m2 → ℝ)
    (u : ℕ → Fin p2 → ℝ) (k : ℕ) : Prop :=
  ∃ ε1 ε2 ε3 : ℝ, 0 ≤ ε1 ∧ ε1 ≤ ε k ∧ 0 ≤ ε2 ∧ ε2 ≤ ε k ∧ 0 ≤ ε3 ∧ ε3 ≤ ε k ∧
    -- (3.1)
    ‖gradient (fun y => augLag P y (lamBar k) (muBar k) (ρ k)) (x k)
        + ∑ i, v k i • gradient (P.h2 i) (x k) + ∑ i, u k i • gradient (P.g2 i) (x k)‖ ≤ ε1 ∧
    -- (3.2)
    (∀ i, 0 ≤ u k i ∧ P.g2 i (x k) ≤ ε2) ∧
    -- (3.3)
    (∀ i, P.g2 i (x k) < -ε2 → u k i = 0) ∧
    -- (3.4)
    ‖h2vec P (x k)‖ ≤ ε3

/-- A run of Algorithm 3.1 (pp. 4–5) that never stops at Step 2 (the standing assumption of §4).
`x 0` is the arbitrary initial point `x₀`; the outer iterations are `k = 1, 2, …`. The values
`ρ 0`, `lamBar 0`, `muBar 0`, `v 0`, `u 0` (and `ε 0`) are unused.
* initialisation: `ρ₁`, `λ̄₁ ∈ [λ̄_min, λ̄_max]`, `μ̄₁ ∈ [0, μ̄_max]`;
* for every `k ≥ 1`: Step 2 holds, the safeguarded estimates `λ̄ₖ₊₁`, `μ̄ₖ₊₁` lie in their boxes
  ((3.6) and the line after (3.7)), and Step 4 updates `ρ`:
  `ρₖ₊₁ = ρₖ` if `max{‖h₁(xₖ)‖∞, ‖σₖ‖∞} ≤ τ max{‖h₁(xₖ₋₁)‖∞, ‖σₖ₋₁‖∞}`, else `ρₖ₊₁ = γρₖ`. -/
def IsRun (P : Problem n m1 p1 m2 p2) (τ γ ρ1 : ℝ) (lamMin lamMax : Fin m1 → ℝ)
    (muMax : Fin p1 → ℝ) (ε : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ)
    (lamBar : ℕ → Fin m1 → ℝ) (muBar : ℕ → Fin p1 → ℝ) (v : ℕ → Fin m2 → ℝ)
    (u : ℕ → Fin p2 → ℝ) : Prop :=
  ρ 1 = ρ1 ∧
  (∀ i, lamMin i ≤ lamBar 1 i ∧ lamBar 1 i ≤ lamMax i) ∧
  (∀ i, 0 ≤ muBar 1 i ∧ muBar 1 i ≤ muMax i) ∧
  ∀ k, 1 ≤ k →
    Step2 P ε x ρ lamBar muBar v u k ∧
    (∀ i, lamMin i ≤ lamBar (k + 1) i ∧ lamBar (k + 1) i ≤ lamMax i) ∧
    (∀ i, 0 ≤ muBar (k + 1) i ∧ muBar (k + 1) i ≤ muMax i) ∧
    ρ (k + 1) =
      if max ‖h1vec P (x k)‖ ‖sigma P x ρ muBar k‖
          ≤ τ * max ‖h1vec P (x (k - 1))‖ ‖sigma P x ρ muBar (k - 1)‖
      then ρ k else γ * ρ k

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `x` is a KKT point of `minimize F subject to H(x) = 0, G(x) ≤ 0`: it is feasible and there
are multipliers `a`, `b ≥ 0` with `b j = 0` for inactive `j` and
`∇F(x) + Σᵢ aᵢ ∇Hᵢ(x) + Σⱼ bⱼ ∇Gⱼ(x) = 0`. -/
def IsKKT (F : E → ℝ) (H : ι → E → ℝ) (G : κ → E → ℝ) (x : E) : Prop :=
  (∀ i, H i x = 0) ∧ (∀ j, G j x ≤ 0) ∧
    ∃ (a : ι → ℝ) (b : κ → ℝ), (∀ j, 0 ≤ b j) ∧ (∀ j, G j x < 0 → b j = 0) ∧
      gradient F x + ∑ i, a i • gradient (H i) x + ∑ j, b j • gradient (G j) x = 0

/-- The constant positive linear dependence condition (CPLD) of Qi and Wei at `x`
(pp. 2–3): whenever a nontrivial null linear combination of the gradients of the equality
constraints indexed by `I` and of active inequality constraints indexed by `J`, with
nonnegative coefficients on `J`, exists at `x`, the gradients indexed by `I ⊕ J` are linearly
dependent at every `z` in a neighbourhood of `x`. No feasibility clause is included. -/
def CPLDAt (H : ι → E → ℝ) (G : κ → E → ℝ) (x : E) : Prop :=
  ∀ (I : Finset ι) (J : Finset κ), (∀ j ∈ J, G j x = 0) →
    ∀ (a : ι → ℝ) (b : κ → ℝ), (∀ j ∈ J, 0 ≤ b j) →
      ((∃ i ∈ I, a i ≠ 0) ∨ (∃ j ∈ J, b j ≠ 0)) →
      ∑ i ∈ I, a i • gradient (H i) x + ∑ j ∈ J, b j • gradient (G j) x = 0 →
      ∀ᶠ z in 𝓝 x, ¬ LinearIndependent ℝ
        (Sum.elim (fun i : I => gradient (H i) z) (fun j : J => gradient (G j) z))

end Generic

end AugLagLLC.Feas


