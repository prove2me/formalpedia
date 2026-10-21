-- Prove2me | Definitions.Def_WrightPDIPM_PathFollowing_Setup
-- name    : WrightPDIPM_PathFollowing_Setup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:20.456981+00:00
-- url     : https://prove2.me/theorems/d42e22cf-27f2-4b91-9db9-85225da89bc2
-- title:
--   Path-following setting: F°, the duality measure μ, the step equations (1.12), the neighborhoods N₂(θ) and N₋∞(γ), the bound ᾱ (5.19) and Algorithm LPF
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, with no assumption on the rank of $A$, and consider the standard-form linear program $\min c^{\mathsf T}x$ s.t. $Ax = b$, $x \ge 0$ and its dual $\max b^{\mathsf T}\lambda$ s.t. $A^{\mathsf T}\lambda + s = c$, $s \ge 0$. Vector inequalities are componentwise, $e = (1,\dots,1)^{\mathsf T}$, and for vectors $x, s$ we write $X = \operatorname{diag}(x)$, $S = \operatorname{diag}(s)$, so that $XSe$ is the vector with entries $x_i s_i$. This file defines:
--
--   1. the **Euclidean norm** $\|v\|_2 = (\sum_i v_i^2)^{1/2}$;
--   2. the **strictly feasible set** $\mathcal F^\circ = \{(x,\lambda,s) : Ax = b,\ A^{\mathsf T}\lambda + s = c,\ x > 0,\ s > 0\}$;
--   3. the **duality measure** $\mu = x^{\mathsf T}s/n$;
--   4. the **2-norm neighborhood** $\mathcal N_2(\theta) = \{(x,\lambda,s) \in \mathcal F^\circ : \|XSe - \mu e\|_2 \le \theta\mu\}$ and the **one-sided $\infty$-norm neighborhood** $\mathcal N_{-\infty}(\gamma) = \{(x,\lambda,s) \in \mathcal F^\circ : x_i s_i \ge \gamma\mu \text{ for all } i\}$;
--   5. the **step equations** at $(x,\lambda,s)$ with centering parameter $\sigma$: a direction $(\Delta x, \Delta\lambda, \Delta s)$ satisfies
--   $$\begin{bmatrix} 0 & A^{\mathsf T} & I \\ A & 0 & 0 \\ S & 0 & X\end{bmatrix}\begin{bmatrix}\Delta x\\ \Delta\lambda\\ \Delta s\end{bmatrix} = \begin{bmatrix} 0 \\ 0 \\ -XSe + \sigma\mu e\end{bmatrix};$$
--   6. the predictor step bound $\bar\alpha = \min\bigl(\tfrac12, (\mu/(8\|\Delta X\Delta S e\|))^{1/2}\bigr)$, read as $\tfrac12$ when $\Delta X \Delta S e = 0$;
--   7. the iterates of **Algorithm LPF** with parameters $\gamma, \sigma_{\min}, \sigma_{\max}$: $(x^0,\lambda^0,s^0) \in \mathcal N_{-\infty}(\gamma)$; at each $k$, $\sigma_k \in [\sigma_{\min}, \sigma_{\max}]$, $(\Delta x^k, \Delta\lambda^k, \Delta s^k)$ solves the step equations at the $k$-th iterate with $\sigma_k$, $\alpha_k$ is the largest $\alpha \in [0,1]$ with $(x^k,\lambda^k,s^k) + \alpha(\Delta x^k,\Delta\lambda^k,\Delta s^k) \in \mathcal N_{-\infty}(\gamma)$, and $(x^{k+1},\lambda^{k+1},s^{k+1}) = (x^k,\lambda^k,s^k) + \alpha_k(\Delta x^k,\Delta\lambda^k,\Delta s^k)$.
--
--   These are the objects of Chapter 5 of Wright's book: every path-following method there takes its direction from the step equations and keeps its iterates in one of the two neighborhoods.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, matrices `Matrix (Fin m) (Fin n) ℝ`, points are triples `(x, lam, s)`. The norm is defined explicitly because Mathlib's default norm on `Fin n → ℝ` is the sup norm. The direction is given by its linear equations, not by a closed-form solution, so no nonsingularity is presupposed; $\lambda$ does not enter the equations. In $\bar\alpha$ the case $\Delta X\Delta S e = 0$ is split off explicitly, since real division by zero would give $\bar\alpha = 0$. In Algorithm LPF the "largest $\alpha$" is a hypothesis (`IsGreatest`) on the chosen $\alpha_k$, not a construction; the parameter ranges $\gamma \in (0,1)$, $0 < \sigma_{\min} < \sigma_{\max} < 1$ are stated by the theorems that use the predicate.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 5, Eq. (1.7b); p. 7, Eq. (1.11); p. 8, Eq. (1.12); p. 9, Eqs. (1.15)–(1.16); p. 87, Eq. (5.5); p. 94, Eq. (5.19); pp. 96–97, Algorithm LPF, Eq. (5.21)

import Mathlib

/-!
# Wright, *Primal-Dual Interior-Point Methods* (SIAM 1997), Chapter 5: path-following setting

The standard-form pair (2.1) `min cᵀx s.t. Ax = b, x ≥ 0` and (2.2) `max bᵀλ s.t. Aᵀλ + s = c,
s ≥ 0` (p. 22), with `A ∈ ℝ^{m×n}` arbitrary (no rank assumption). Vectors are `Fin n → ℝ`,
primal-dual points are triples `(x, λ, s)`, vector inequalities are componentwise.

* `norm2` — the Euclidean norm `‖·‖ = ‖·‖₂` (Notation, p. xvii).
* `Fo` — the strictly feasible set `F°` (1.7b) (p. 5).
* `mu` — the duality measure `μ = xᵀs/n` (1.11) (p. 7).
* `N2`, `NegInf` — the neighborhoods `N₂(θ)` (1.15) and `N_{-∞}(γ)` (1.16) (p. 9).
* `IsStep` — the step equations (1.12) (p. 8) with centering parameter `σ`.
* `alphaBar` — the predictor step bound `ᾱ` (5.19) (p. 94).
* `IsLPFIterates` — the iterates of Algorithm LPF (pp. 96–97), step length (5.21).
-/

namespace WrightPDIPM.PathFollowing

open Matrix

/-- The Euclidean norm `‖v‖₂ = (∑ᵢ vᵢ²)^{1/2}` (Notation, p. xvii). Mathlib's default norm on
`Fin n → ℝ` is the sup norm, hence the explicit definition. -/
noncomputable def norm2 {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The strictly feasible set `F°` (1.7b) (p. 5): triples `(x, λ, s)` with `Ax = b`,
`Aᵀλ + s = c`, `x > 0`, `s > 0`. -/
def Fo {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | A *ᵥ p.1 = b ∧ Aᵀ *ᵥ p.2.1 + p.2.2 = c ∧ (∀ i, 0 < p.1 i) ∧ (∀ i, 0 < p.2.2 i)}

/-- The duality measure `μ = xᵀs/n` (1.11) (p. 7). -/
noncomputable def mu {n : ℕ} (x s : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ s) / (n : ℝ)

/-- The 2-norm neighborhood (1.15) (p. 9):
`N₂(θ) = {(x, λ, s) ∈ F° | ‖XSe − μe‖₂ ≤ θμ}`, where `XSe − μe` is the vector with entries
`xᵢsᵢ − μ`. -/
def N2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (θ : ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ Fo A b c ∧ norm2 (fun i => p.1 i * p.2.2 i - mu p.1 p.2.2) ≤ θ * mu p.1 p.2.2}

/-- The one-sided ∞-norm neighborhood (1.16) (p. 9):
`N_{-∞}(γ) = {(x, λ, s) ∈ F° | xᵢsᵢ ≥ γμ for all i = 1, …, n}`. -/
def NegInf {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (γ : ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ Fo A b c ∧ ∀ i, γ * mu p.1 p.2.2 ≤ p.1 i * p.2.2 i}

/-- The step equations (1.12) (p. 8) at the point `(x, λ, s)` with centering parameter `σ`:
`AᵀΔλ + Δs = 0`, `AΔx = 0`, and `SΔx + XΔs = −XSe + σμe`, i.e.
`sᵢΔxᵢ + xᵢΔsᵢ = −xᵢsᵢ + σμ` for every `i`, with `μ = xᵀs/n`. The direction is defined by these
linear equations (not by a closed-form solution); `λ` does not enter them. -/
def IsStep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (σ : ℝ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ dlam + ds = 0 ∧ A *ᵥ dx = 0 ∧
    ∀ i, s i * dx i + x i * ds i = -(x i * s i) + σ * mu x s

/-- The predictor step bound (5.19) (p. 94):
`ᾱ = min(1/2, (μ/(8‖ΔXΔSe‖))^{1/2})`, where `ΔXΔSe` is the vector with entries `ΔxᵢΔsᵢ`.
When `ΔXΔSe = 0` the ratio is read as `+∞`, so `ᾱ = 1/2` (real division by zero would
instead give `ᾱ = 0`). -/
noncomputable def alphaBar {n : ℕ} (x s dx ds : Fin n → ℝ) : ℝ :=
  if norm2 (fun i => dx i * ds i) = 0 then 1 / 2
  else min (1 / 2) (Real.sqrt (mu x s / (8 * norm2 (fun i => dx i * ds i))))

/-- The iterates of Algorithm LPF (pp. 96–97) with parameters `γ, σ_min, σ_max`: the start
`(x⁰, λ⁰, s⁰) ∈ N_{-∞}(γ)`; at every `k`, `σ_k ∈ [σ_min, σ_max]`, `(Δxᵏ, Δλᵏ, Δsᵏ)` solves
(1.13) (= (1.12) at the `k`-th iterate with `σ_k`), `α_k` is the largest `α ∈ [0, 1]` with
`(xᵏ(α), λᵏ(α), sᵏ(α)) ∈ N_{-∞}(γ)` (5.21), and `(x^{k+1}, λ^{k+1}, s^{k+1}) =
(xᵏ(α_k), λᵏ(α_k), sᵏ(α_k))`, where `(xᵏ(α), λᵏ(α), sᵏ(α)) = (xᵏ, λᵏ, sᵏ) + α(Δxᵏ, Δλᵏ, Δsᵏ)`
(5.5a). The parameter ranges `γ ∈ (0, 1)`, `0 < σ_min < σ_max < 1` are not part of this
predicate; theorems state them. -/
structure IsLPFIterates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (γ σmin σmax : ℝ)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ)
    (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ) : Prop where
  start : (x 0, lam 0, s 0) ∈ NegInf A b c γ
  sigma_mem : ∀ k, σ k ∈ Set.Icc σmin σmax
  step : ∀ k, IsStep A (x k) (s k) (σ k) (dx k) (dlam k) (ds k)
  alpha_greatest : ∀ k, IsGreatest
    {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧
      (x k + a • dx k, lam k + a • dlam k, s k + a • ds k) ∈ NegInf A b c γ} (α k)
  update_x : ∀ k, x (k + 1) = x k + α k • dx k
  update_lam : ∀ k, lam (k + 1) = lam k + α k • dlam k
  update_s : ∀ k, s (k + 1) = s k + α k • ds k

end WrightPDIPM.PathFollowing


