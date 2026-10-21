-- Prove2me | Definitions.Def_WrightPDIPM_Potential_Setting
-- name    : WrightPDIPM_Potential_Setting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:27.412365+00:00
-- url     : https://prove2.me/theorems/0979becf-645e-49d8-b8e1-75b4614784d7
-- title:
--   The standard-form LP, the potential Φ_ρ, Algorithm PR's direction and step, and the quadratic estimate q(α)
-- statement:
--   Fix integers $m, n \ge 0$, a matrix $A \in \mathbb R^{m\times n}$ (no rank assumption), $b \in \mathbb R^m$ and $c \in \mathbb R^n$, the data of the standard-form linear program $\min c^Tx$ s.t. $Ax = b$, $x \ge 0$ and its dual $\max b^T\lambda$ s.t. $A^T\lambda + s = c$, $s \ge 0$. Vector inequalities are componentwise, $e = (1,\dots,1)^T$, $X = \operatorname{diag}(x)$, $S = \operatorname{diag}(s)$, $\|\cdot\|$ is the Euclidean norm and $\|\cdot\|_\infty$ the max-norm. The file defines the objects of Chapter 4 of Wright's book.
--
--   1. The **strictly feasible set** (1.7b): $\mathcal F^\circ = \{(x,\lambda,s) : Ax = b,\ A^T\lambda + s = c,\ x > 0,\ s > 0\}$, and the **duality measure** $\mu = x^Ts/n$ (1.11).
--   2. The **Tanabe–Todd–Ye potential** (4.2): for a parameter $\rho$,
--   $$\Phi_\rho(x,s) = \rho\log x^Ts - \sum_{i=1}^n \log x_is_i ;$$
--   $\Phi_n$ is the same function with $\rho = n$.
--   3. The **largest feasible step** (4.5): $\alpha_{\max} = \sup\{\alpha \in [0,1] : (x,s) + \alpha(\Delta x,\Delta s) \ge 0\}$.
--   4. A **feasible direction** (4.12): $A\Delta x = 0$, $A^T\Delta\lambda + \Delta s = 0$. The **direction of Algorithm PR** satisfies (4.12) and the step equation (4.19)
--   $$S\Delta x + X\Delta s = -XSe + \frac{n}{\rho}\mu e,$$
--   which is the Newton system (1.13) with centering parameter $\sigma = n/\rho$.
--   5. The **coefficients of the quadratic estimate** (4.17) and the estimate itself (4.18), for $\tau \in (0,1)$:
--   $$g_1 = \rho\frac{s^T\Delta x + x^T\Delta s}{x^Ts} - e^T(X^{-1}\Delta x + S^{-1}\Delta s),\quad g_2 = \frac{1}{1-\tau}\big(\|X^{-1}\Delta x\|^2 + \|S^{-1}\Delta s\|^2\big),\quad q(\alpha) = \Phi_\rho(x,s) + \alpha g_1 + \tfrac12\alpha^2 g_2.$$
--   6. The **scaled quantities** (4.20): $v = [(x_is_i)^{1/2}]_{i=1}^n$, $v_{\min} = \min_i v_i$, $r = -v + \frac{n}{\rho}\mu V^{-1}e$ with $V = \operatorname{diag}(v)$, and the **step** $\bar\alpha = v_{\min}/(2\|r\|)$ (4.31).
--   7. **One iteration of Algorithm PR** (p. 67): from $(x,\lambda,s)$, take a direction $(\Delta x,\Delta\lambda,\Delta s)$ of item 4 and a step length $\alpha_k \in (0,\alpha_{\max})$ that minimizes $\alpha \mapsto \Phi_\rho(x+\alpha\Delta x, s+\alpha\Delta s)$ over $(0,\alpha_{\max})$ (4.6); the new point is $(x,\lambda,s) + \alpha_k(\Delta x,\Delta\lambda,\Delta s)$.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, matrices `Matrix (Fin m) (Fin n) ℝ`. `Phi` is the formula (4.2) on all of $\mathbb R^n\times\mathbb R^n$ (Lean's `Real.log` is $0$ at $0$ and $\log|t|$ for negative $t$); every theorem evaluates it only at points with $x, s > 0$, the domain (4.3). `normInf` is $\max_i |v_i|$ ($0$ when $n = 0$) and `vmin` is $\min_i v_i$, used only with $n \ge 1$. `alphaMax` is the real supremum of a set that contains $0$ and is bounded by $1$ whenever $x, s \ge 0$. A PR iteration takes the minimizing step length as data (`IsMinOn`) instead of constructing an arg min, which need not exist on the open interval.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 5 (1.7b), p. 7 (1.11), p. 8 (1.13), pp. 66–67 ((4.2), (4.3), (4.5), (4.6), Algorithm PR), pp. 71–72 ((4.12), (4.17)–(4.20)), p. 76 (4.31)

import Mathlib

/-!
# Wright, *Primal-Dual Interior-Point Methods* (SIAM 1997), Chapter 4: potential reduction

The standard-form pair (2.1) `min cᵀx s.t. Ax = b, x ≥ 0` and (2.2) `max bᵀλ s.t. Aᵀλ + s = c,
s ≥ 0` (p. 22), with `A ∈ ℝ^{m×n}` arbitrary (no rank assumption). Vectors are `Fin n → ℝ`;
vector inequalities are componentwise; `e = (1, …, 1)ᵀ`, `X = diag(x)`, `S = diag(s)`.

* `Fo` — the strictly feasible set `F°` (1.7b) (p. 5).
* `mu` — the duality measure `μ = xᵀs/n` (1.11).
* `norm2`, `normInf` — the Euclidean norm `‖·‖` and the max-norm `‖·‖_∞` (Notation, p. xvii).
* `Phi` — the Tanabe–Todd–Ye potential `Φ_ρ(x, s) = ρ log xᵀs − ∑ᵢ log xᵢsᵢ` (4.2) (p. 66);
  `Φ_n` is `Phi n`.
* `alphaMax` — `α_max = sup{α ∈ [0, 1] | (x, s) + α(Δx, Δs) ≥ 0}` (4.5) (p. 67).
* `IsFeasibleDirection` — `AΔx = 0`, `AᵀΔλ + Δs = 0` (4.12) (p. 71).
* `IsPRDirection` — (4.12) together with the step equation of Algorithm PR,
  `SΔx + XΔs = −XSe + (n/ρ)μe` (4.19) (p. 72), i.e. (1.13) with `σ = n/ρ`.
* `g1`, `g2`, `q` — the coefficients (4.17a), (4.17b) and the quadratic estimate (4.18) (p. 72).
* `vvec`, `vmin`, `rvec` — `v = Ve = [(xᵢsᵢ)^{1/2}]`, `v_min = minᵢ vᵢ`,
  `r = −v + (n/ρ)μV⁻¹e` (4.20) (p. 72).
* `alphaBar` — the step `ᾱ = v_min/(2‖r‖)` (4.31) (p. 76).
* `IsPRStep` — one iteration of Algorithm PR (p. 67): the direction of (1.13) with
  `σ_k = n/ρ`, and a step length `α_k` minimizing `Φ_ρ` along it over `(0, α_max)` (4.6).
-/

namespace WrightPDIPM.Potential

open Matrix

/-- The strictly feasible set `F°` (1.7b), p. 5: triples `(x, λ, s)` with `Ax = b`,
`Aᵀλ + s = c`, `x > 0`, `s > 0`. -/
def Fo {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | A *ᵥ p.1 = b ∧ Aᵀ *ᵥ p.2.1 + p.2.2 = c ∧ (∀ i, 0 < p.1 i) ∧ ∀ i, 0 < p.2.2 i}

/-- The duality measure `μ = xᵀs/n` (1.11), p. 7. -/
noncomputable def mu {n : ℕ} (x s : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ s) / n

/-- The Euclidean norm `‖v‖ = (∑ᵢ vᵢ²)^{1/2}`. -/
noncomputable def norm2 {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The max-norm `‖v‖_∞ = maxᵢ |vᵢ|` (equal to `0` when `n = 0`). -/
noncomputable def normInf {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ⨆ i, |v i|

/-- The Tanabe–Todd–Ye primal-dual potential (4.2), p. 66:
`Φ_ρ(x, s) = ρ log xᵀs − ∑ᵢ log xᵢsᵢ`. It is evaluated only on its domain (4.3), pairs
`(x, s)` with `(x, λ, s) ∈ F°` for some `λ`, where every logarithm has a positive argument.
`Φ_n` (4.4a) is `Phi n`. -/
noncomputable def Phi {n : ℕ} (ρ : ℝ) (x s : Fin n → ℝ) : ℝ :=
  ρ * Real.log (x ⬝ᵥ s) - ∑ i, Real.log (x i * s i)

/-- The largest feasible step (4.5), p. 67:
`α_max = sup{α ∈ [0, 1] | (x, s) + α(Δx, Δs) ≥ 0}`. For `x, s ≥ 0` the set contains `0` and is
bounded by `1`, so the supremum is a maximum. -/
noncomputable def alphaMax {n : ℕ} (x s dx ds : Fin n → ℝ) : ℝ :=
  sSup {α : ℝ | 0 ≤ α ∧ α ≤ 1 ∧ ∀ i, 0 ≤ x i + α * dx i ∧ 0 ≤ s i + α * ds i}

/-- A direction that keeps the equality constraints (1.4a), (1.4b): (4.12), p. 71,
`AΔx = 0`, `AᵀΔλ + Δs = 0`. -/
def IsFeasibleDirection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (dx : Fin n → ℝ)
    (dlam : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  A *ᵥ dx = 0 ∧ Aᵀ *ᵥ dlam + ds = 0

/-- The search direction of Algorithm PR at a strictly feasible point: (4.12) together with
(4.19), p. 72, `SΔx + XΔs = −XSe + (n/ρ)μe`. This is the system (1.13) (p. 8) with centering
parameter `σ = n/ρ`. -/
def IsPRDirection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ρ : ℝ) (x s : Fin n → ℝ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  IsFeasibleDirection A dx dlam ds ∧
    ∀ i, s i * dx i + x i * ds i = -(x i * s i) + ((n : ℝ) / ρ) * mu x s

/-- The linear coefficient (4.17a), p. 72:
`g₁ = ρ (sᵀΔx + xᵀΔs)/(xᵀs) − eᵀ(X⁻¹Δx + S⁻¹Δs)`. -/
noncomputable def g1 {n : ℕ} (ρ : ℝ) (x s dx ds : Fin n → ℝ) : ℝ :=
  ρ * ((s ⬝ᵥ dx + x ⬝ᵥ ds) / (x ⬝ᵥ s)) - ∑ i, (dx i / x i + ds i / s i)

/-- The quadratic coefficient (4.17b), p. 72:
`g₂ = (1/(1 − τ)) (‖X⁻¹Δx‖² + ‖S⁻¹Δs‖²)`. -/
noncomputable def g2 {n : ℕ} (τ : ℝ) (x s dx ds : Fin n → ℝ) : ℝ :=
  (1 / (1 - τ)) * (norm2 (fun i => dx i / x i) ^ 2 + norm2 (fun i => ds i / s i) ^ 2)

/-- The quadratic estimate (4.18), p. 72: `q(α) = Φ_ρ(x, s) + αg₁ + ½α²g₂`. -/
noncomputable def q {n : ℕ} (ρ τ : ℝ) (x s dx ds : Fin n → ℝ) (α : ℝ) : ℝ :=
  Phi ρ x s + α * g1 ρ x s dx ds + (1 / 2) * α ^ 2 * g2 τ x s dx ds

/-- `v = Ve = [(xᵢsᵢ)^{1/2}]`, `V = (XS)^{1/2}` (4.20), p. 72. -/
noncomputable def vvec {n : ℕ} (x s : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt (x i * s i)

/-- `v_min = min_{i=1,…,n} vᵢ` (4.20), p. 72 (used with `n ≥ 1`). -/
noncomputable def vmin {n : ℕ} (x s : Fin n → ℝ) : ℝ :=
  ⨅ i, vvec x s i

/-- `r = −v + (n/ρ)μV⁻¹e` (4.20), p. 72. -/
noncomputable def rvec {n : ℕ} (ρ : ℝ) (x s : Fin n → ℝ) : Fin n → ℝ :=
  fun i => -vvec x s i + ((n : ℝ) / ρ) * mu x s / vvec x s i

/-- The step length `ᾱ = v_min/(2‖r‖)` (4.31), p. 76. -/
noncomputable def alphaBar {n : ℕ} (ρ : ℝ) (x s : Fin n → ℝ) : ℝ :=
  vmin x s / (2 * norm2 (rvec ρ x s))

/-- One iteration of Algorithm PR (p. 67) from `(x, λ, s)` to `(x', λ', s')`: a direction
`(Δx, Δλ, Δs)` solving (1.13) with `σ = n/ρ` (that is, (4.12) and (4.19)), and a step length
`α ∈ (0, α_max)` that minimizes `α ↦ Φ_ρ(x + αΔx, s + αΔs)` over `(0, α_max)` (4.6), with
`(x', λ', s') = (x, λ, s) + α(Δx, Δλ, Δs)`. -/
def IsPRStep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ρ : ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ)
    (x' : Fin n → ℝ) (lam' : Fin m → ℝ) (s' : Fin n → ℝ) : Prop :=
  ∃ (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ),
    IsPRDirection A ρ x s dx dlam ds ∧
    ∃ α ∈ Set.Ioo 0 (alphaMax x s dx ds),
      IsMinOn (fun a : ℝ => Phi ρ (x + a • dx) (s + a • ds)) (Set.Ioo 0 (alphaMax x s dx ds)) α ∧
      x' = x + α • dx ∧ lam' = lam + α • dlam ∧ s' = s + α • ds

end WrightPDIPM.Potential


