-- Prove2me | Definitions.Def_WrightPDIPM_Infeasible_IPF
-- name    : WrightPDIPM_Infeasible_IPF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:20.941968+00:00
-- url     : https://prove2.me/theorems/fc7152f5-f2e7-4470-b601-67cb95fee65b
-- title:
--   Algorithm IPF: residuals, the neighborhood N_−∞(γ, β), the step equations (6.4), the iterates, ν_k, the scaled steps, and Q-/R-linear convergence
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, with no assumption on the rank of $A$, and consider the primal linear program $\min c^{\mathsf T}x$ s.t. $Ax = b$, $x \ge 0$ and its dual $\max b^{\mathsf T}\lambda$ s.t. $A^{\mathsf T}\lambda + s = c$, $s \ge 0$. Vector inequalities are componentwise; $e = (1,\dots,1)^{\mathsf T}$, $X = \operatorname{diag}(x)$, $S = \operatorname{diag}(s)$. This file defines the objects of Chapter 6 of Wright's book.
--
--   1. The **residuals** $r_b = Ax - b$ and $r_c = A^{\mathsf T}\lambda + s - c$, and the Euclidean norm $\|(r_b, r_c)\|$ of the stacked vector in $\mathbb{R}^{m+n}$; the **duality measure** $\mu = x^{\mathsf T}s/n$; the Euclidean norm $\|v\|$ and the 1-norm $\|(x,s)\|_1 = \sum_i |x_i| + \sum_i |s_i|$.
--   2. The **solution set** $\Omega$: triples $(x,\lambda,s)$ with $A^{\mathsf T}\lambda + s = c$, $Ax = b$, $x_is_i = 0$ for all $i$, $(x,s) \ge 0$; the **strictly feasible set** $\mathcal F^\circ$ ($Ax = b$, $A^{\mathsf T}\lambda + s = c$, $(x,s) > 0$); the index sets $\mathcal B = \{j : x^*_j \ne 0$ for some $(x^*,\lambda^*,s^*) \in \Omega\}$ and $\mathcal N = \{j : s^*_j \ne 0$ for some $(x^*,\lambda^*,s^*) \in \Omega\}$.
--   3. For a starting point $(x^0,\lambda^0,s^0)$ with residuals $(r_b^0, r_c^0)$ and $\mu_0 = (x^0)^{\mathsf T}s^0/n$, and parameters $\gamma, \beta$, the **neighborhood**
--
--   $$\mathcal N_{-\infty}(\gamma,\beta) = \Big\{(x,\lambda,s) : \|(r_b,r_c)\| \le \big[\|(r_b^0,r_c^0)\|/\mu_0\big]\beta\mu,\ (x,s) > 0,\ x_is_i \ge \gamma\mu,\ i = 1,\dots,n\Big\}.$$
--
--   4. The **step equations** at $(x,\lambda,s)$ with centering parameter $\sigma$: $A^{\mathsf T}\Delta\lambda + \Delta s = -r_c$, $A\Delta x = -r_b$, $S\Delta x + X\Delta s = -XSe + \sigma\mu e$.
--   5. The **iterates of Algorithm IPF** with parameters $\gamma, \beta, \sigma_{\min}, \sigma_{\max}$: sequences $(x^k,\lambda^k,s^k)$, $\sigma_k$, $\alpha_k$, $(\Delta x^k, \Delta\lambda^k, \Delta s^k)$ such that $(x^0, s^0) > 0$; for every $k$, $\sigma_k \in [\sigma_{\min}, \sigma_{\max}]$, the direction solves the step equations at the $k$-th iterate with $\sigma_k$, $\alpha_k$ is the largest $\alpha \in [0,1]$ with $(x^k,\lambda^k,s^k) + \alpha(\Delta x^k,\Delta\lambda^k,\Delta s^k) \in \mathcal N_{-\infty}(\gamma,\beta)$ and $\mu_k(\alpha) \le (1 - 0.01\alpha)\mu_k$, where $\mu_k(\alpha) = (x^k + \alpha\Delta x^k)^{\mathsf T}(s^k + \alpha\Delta s^k)/n$, and the next iterate is $(x^k,\lambda^k,s^k) + \alpha_k(\Delta x^k,\Delta\lambda^k,\Delta s^k)$. The neighborhood is anchored at the run's own starting point.
--   6. $\nu_k = \prod_{j=0}^{k-1}(1-\alpha_j)$, $\nu_0 = 1$, and the scaled steps $D^{-1}\Delta x$, $D\Delta s$ with $D = X^{1/2}S^{-1/2}$, whose $i$-th entries are $(s_i/x_i)^{1/2}\Delta x_i$ and $(x_i/s_i)^{1/2}\Delta s_i$.
--   7. **Q-linear convergence to zero** of a real sequence $\{\beta_k\}$: all $\beta_k > 0$, $\beta_k \to 0$, and there is $\rho \in (0,1)$ with $\beta_{k+1}/\beta_k \le \rho$ for all $k$ sufficiently large. **R-linear convergence to zero**: there is a sequence $\{\hat\beta_k\}$ converging Q-linearly to zero with $0 \le \beta_k \le \hat\beta_k$ for all $k$.
--
--   These are the objects on which the convergence theory of the infeasible-interior-point path-following method rests.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, matrices `Matrix (Fin m) (Fin n) ℝ`, triples are `x, λ, s` in that order, with $\lambda$ written `lam`. Mathlib's default norm on `Fin n → ℝ` is the sup norm, so the Euclidean norms are defined explicitly with `Real.sqrt`. "The largest $\alpha$" is the hypothesis `IsGreatest` on the admissible set rather than a constructed maximum (a greatest element need not exist in degenerate cases, since $(x,s) > 0$ is an open condition). The parameter ranges $\gamma \in (0,1)$, $\beta \ge 1$, $0 < \sigma_{\min} < \sigma_{\max} \le 0.5$ are stated by each theorem, not by the iterate predicate. $\Omega$ is defined through the optimality conditions (2.4), which the book uses as its definition of $\Omega$ on p. 24.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 109, Eqs. (6.1)–(6.3); p. 110, Algorithm IPF, Eqs. (6.4)–(6.7); p. 115, Eq. (6.24); pp. 23–24, (2.4) and Ω; p. 5, (1.7b); p. 27, (2.11); Appendix A, pp. 252–253 (Q-/R-linear convergence)

import Mathlib

/-!
# Wright, *Primal-Dual Interior-Point Methods* (SIAM 1997), Chapter 6: Algorithm IPF

The standard-form pair (2.1) `min cᵀx s.t. Ax = b, x ≥ 0` and (2.2) `max bᵀλ s.t. Aᵀλ + s = c,
s ≥ 0` (p. 22), with `A ∈ ℝ^{m×n}` arbitrary (no rank assumption). Vectors are `Fin n → ℝ`,
primal-dual points are triples `(x, λ, s)`, vector inequalities are componentwise.

* `norm2`, `norm1xs` — the Euclidean norm, and the 1-norm `‖(x, s)‖₁` of a stacked pair.
* `rb`, `rc`, `resNorm` — the residuals (6.1) (p. 109) and the Euclidean norm `‖(r_b, r_c)‖`.
* `mu` — the duality measure `μ = xᵀs/n` (1.11) (p. 7).
* `Omega`, `Fo`, `indexB`, `indexN` — the solution set `Ω` of (2.4) (p. 24), the strictly
  feasible set `F°` (1.7b) (p. 5), and the index sets `B`, `N` (2.11) (p. 27).
* `NegInfNbhd` — the neighborhood `N_{-∞}(γ, β)` (6.2) (p. 109), anchored at a starting point.
* `IsIPFStep` — the step equations (6.4) (p. 110).
* `IsIPFIterates` — the iterates of Algorithm IPF (p. 110), step length (6.5)–(6.6).
* `nu` — `ν_k = ∏_{j=0}^{k-1} (1 − α_j)` (6.7) (p. 110).
* `scaledDx`, `scaledDs` — `(Dᵏ)⁻¹Δxᵏ` and `DᵏΔsᵏ`, `Dᵏ = (Xᵏ)^{1/2}(Sᵏ)^{-1/2}` (6.24) (p. 115).
* `QLinearToZero`, `RLinearToZero` — Q- and R-linear convergence to zero (App. A, pp. 252–253).
-/

namespace WrightPDIPM.Infeasible

open Matrix Filter

/-- The Euclidean norm `‖v‖ = ‖v‖₂ = (∑ᵢ vᵢ²)^{1/2}` (Notation, p. xvii). Mathlib's default norm
on `Fin n → ℝ` is the sup norm, hence the explicit definition. -/
noncomputable def norm2 {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The 1-norm of the stacked vector `(x, s) ∈ ℝ²ⁿ`: `‖(x, s)‖₁ = ∑ᵢ |xᵢ| + ∑ᵢ |sᵢ|`. -/
def norm1xs {n : ℕ} (x s : Fin n → ℝ) : ℝ :=
  ∑ i, |x i| + ∑ i, |s i|

/-- The primal residual `r_b = Ax − b` (6.1) (p. 109). -/
def rb {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Fin m → ℝ :=
  A *ᵥ x - b

/-- The dual residual `r_c = Aᵀλ + s − c` (6.1) (p. 109). -/
def rc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (lam : Fin m → ℝ)
    (s : Fin n → ℝ) : Fin n → ℝ :=
  Aᵀ *ᵥ lam + s - c

/-- The Euclidean norm of the stacked residual `(r_b, r_c) ∈ ℝ^{m+n}` at `(x, λ, s)`:
`‖(r_b, r_c)‖ = (∑ᵢ (r_b)ᵢ² + ∑ⱼ (r_c)ⱼ²)^{1/2}`. -/
noncomputable def resNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, rb A b x i ^ 2 + ∑ j, rc A c lam s j ^ 2)

/-- The duality measure `μ = xᵀs/n` (1.11) (p. 7). -/
noncomputable def mu {n : ℕ} (x s : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ s) / (n : ℝ)

/-- The primal-dual solution set `Ω = Ω_P × Ω_D` (p. 24), i.e. the triples satisfying the
optimality conditions (2.4) (p. 23): `Aᵀλ + s = c`, `Ax = b`, `xᵢsᵢ = 0` for all `i`,
`(x, s) ≥ 0`. -/
def Omega {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | Aᵀ *ᵥ p.2.1 + p.2.2 = c ∧ A *ᵥ p.1 = b ∧ (∀ i, p.1 i * p.2.2 i = 0) ∧
    (∀ i, 0 ≤ p.1 i) ∧ (∀ i, 0 ≤ p.2.2 i)}

/-- The strictly feasible set `F°` (1.7b) (p. 5): triples `(x, λ, s)` with `Ax = b`,
`Aᵀλ + s = c`, `x > 0`, `s > 0`. -/
def Fo {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | A *ᵥ p.1 = b ∧ Aᵀ *ᵥ p.2.1 + p.2.2 = c ∧ (∀ i, 0 < p.1 i) ∧ (∀ i, 0 < p.2.2 i)}

/-- The index set `B` (2.11a) (p. 27): indices `j` with `x*_j ≠ 0` for some solution. -/
def indexB {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ p ∈ Omega A b c, p.1 j ≠ 0}

/-- The index set `N` (2.11b) (p. 27): indices `j` with `s*_j ≠ 0` for some solution. -/
def indexN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ p ∈ Omega A b c, p.2.2 j ≠ 0}

/-- The neighborhood `N_{-∞}(γ, β)` (6.2) (p. 109), for the starting point `(x⁰, λ⁰, s⁰)`:
the triples `(x, λ, s)` with
`‖(r_b, r_c)‖ ≤ [‖(r_b⁰, r_c⁰)‖/μ₀] β μ`, `(x, s) > 0`, and `xᵢsᵢ ≥ γμ` for `i = 1, …, n`,
where `μ = xᵀs/n`, `μ₀ = (x⁰)ᵀs⁰/n` and `(r_b⁰, r_c⁰)` are the residuals at the start. -/
def NegInfNbhd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β : ℝ) (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | resNorm A b c p.1 p.2.1 p.2.2 ≤
        (resNorm A b c x0 lam0 s0 / mu x0 s0) * β * mu p.1 p.2.2 ∧
      (∀ i, 0 < p.1 i) ∧ (∀ i, 0 < p.2.2 i) ∧
      ∀ i, γ * mu p.1 p.2.2 ≤ p.1 i * p.2.2 i}

/-- The step equations (6.4) (p. 110) at `(x, λ, s)` with centering parameter `σ`:
`AᵀΔλ + Δs = −r_c`, `AΔx = −r_b`, and `SΔx + XΔs = −XSe + σμe`, i.e.
`sᵢΔxᵢ + xᵢΔsᵢ = −xᵢsᵢ + σμ` for every `i`, with `μ = xᵀs/n`. The direction is defined by
these linear equations, not by a closed-form solution. -/
def IsIPFStep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (σ : ℝ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ dlam + ds = -rc A c lam s ∧ A *ᵥ dx = -rb A b x ∧
    ∀ i, s i * dx i + x i * ds i = -(x i * s i) + σ * mu x s

/-- The iterates of Algorithm IPF (p. 110) with parameters `γ, β, σ_min, σ_max`: the start has
`(x⁰, s⁰) > 0`; at every `k`, `σ_k ∈ [σ_min, σ_max]`, `(Δxᵏ, Δλᵏ, Δsᵏ)` solves (6.4), `α_k` is the
largest `α ∈ [0, 1]` such that `(xᵏ(α), λᵏ(α), sᵏ(α)) ∈ N_{-∞}(γ, β)` (6.5) and
`μ_k(α) ≤ (1 − .01α)μ_k` (6.6), and `(x^{k+1}, λ^{k+1}, s^{k+1}) = (xᵏ(α_k), λᵏ(α_k), sᵏ(α_k))`,
where `(xᵏ(α), λᵏ(α), sᵏ(α)) = (xᵏ, λᵏ, sᵏ) + α(Δxᵏ, Δλᵏ, Δsᵏ)` and `μ_k(α) = xᵏ(α)ᵀsᵏ(α)/n`.
The neighborhood is the one anchored at this run's own start `(x⁰, λ⁰, s⁰)`. The parameter
ranges `γ ∈ (0, 1)`, `β ≥ 1`, `0 < σ_min < σ_max ≤ 0.5` are not part of this predicate;
theorems state them. -/
structure IsIPFIterates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (γ β σmin σmax : ℝ)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ)
    (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ) : Prop where
  start_pos : (∀ i, 0 < x 0 i) ∧ (∀ i, 0 < s 0 i)
  sigma_mem : ∀ k, σ k ∈ Set.Icc σmin σmax
  step : ∀ k, IsIPFStep A b c (x k) (lam k) (s k) (σ k) (dx k) (dlam k) (ds k)
  alpha_greatest : ∀ k, IsGreatest
    {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧
      (x k + a • dx k, lam k + a • dlam k, s k + a • ds k) ∈
        NegInfNbhd A b c γ β (x 0) (lam 0) (s 0) ∧
      mu (x k + a • dx k) (s k + a • ds k) ≤ (1 - 0.01 * a) * mu (x k) (s k)} (α k)
  update_x : ∀ k, x (k + 1) = x k + α k • dx k
  update_lam : ∀ k, lam (k + 1) = lam k + α k • dlam k
  update_s : ∀ k, s (k + 1) = s k + α k • ds k

/-- `ν_k = ∏_{j=0}^{k-1} (1 − α_j)`, `ν₀ = 1` (6.7) (p. 110). -/
def nu (α : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (1 - α j)

/-- The scaled primal step `D⁻¹Δx`, with `D = X^{1/2}S^{-1/2}` (6.24) (p. 115):
its `i`-th entry is `(sᵢ/xᵢ)^{1/2} Δxᵢ` (meant for `x, s > 0`). -/
noncomputable def scaledDx {n : ℕ} (x s dx : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt (s i / x i) * dx i

/-- The scaled dual step `DΔs`, with `D = X^{1/2}S^{-1/2}` (6.24) (p. 115):
its `i`-th entry is `(xᵢ/sᵢ)^{1/2} Δsᵢ` (meant for `x, s > 0`). -/
noncomputable def scaledDs {n : ℕ} (x s ds : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt (x i / s i) * ds i

/-- Q-linear convergence to zero (Appendix A, p. 252): `{β_k}` is a sequence of positive scalars
with `β_k → 0`, and there is `ρ ∈ (0, 1)` with `β_{k+1}/β_k ≤ ρ` for all `k` sufficiently large. -/
def QLinearToZero (β : ℕ → ℝ) : Prop :=
  (∀ k, 0 < β k) ∧ Tendsto β atTop (nhds 0) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ᶠ k in atTop, β (k + 1) / β k ≤ ρ

/-- R-linear convergence to zero (Appendix A, p. 253): `{β_k}` is dominated by a Q-linearly
convergent sequence, i.e. there is `{β̂_k}` converging Q-linearly to zero with
`0 ≤ β_k ≤ β̂_k` for all `k`. -/
def RLinearToZero (β : ℕ → ℝ) : Prop :=
  ∃ βhat : ℕ → ℝ, QLinearToZero βhat ∧ ∀ k, 0 ≤ β k ∧ β k ≤ βhat k

end WrightPDIPM.Infeasible


