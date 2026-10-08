-- Prove2me | Definitions.Def_NonlinCG_FRBound_Setting
-- name    : NonlinCG_FRBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:24:24.892009+00:00
-- url     : https://prove2.me/theorems/7eeef244-5f67-496f-bd6f-a7509f73d46e
-- title:
--   The conjugate gradient iteration (1.2)–(1.3), $\beta^{FR}$, $\beta^{PR}$, Assumptions 2.1, the Wolfe, ideal and strong Wolfe line searches and the Zoutendijk condition
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, and let $f : E \to \mathbb R$ be differentiable with gradient $g(x) = \nabla f(x)$ for that inner product. This file fixes the objects of Gilbert and Nocedal's analysis of nonlinear conjugate gradient methods for $\min f(x)$ (1.1).
--
--   1. **The iteration (1.2)–(1.3).** Given a starting point $x_1$, scalars $\beta_k$ and steplengths $\alpha_k > 0$, write $g_k = g(x_k)$ and
--   $$d_k = \begin{cases} -g_k & k = 1,\\ -g_k + \beta_k d_{k-1} & k \ge 2,\end{cases}\qquad x_{k+1} = x_k + \alpha_k d_k \quad (k \ge 1).$$
--   2. **The Fletcher–Reeves and Polak–Ribière scalars** (1.4)–(1.5):
--   $$\beta_k^{FR} = \frac{\|g_k\|^2}{\|g_{k-1}\|^2},\qquad \beta_k^{PR} = \frac{\langle g_k, g_k - g_{k-1}\rangle}{\|g_{k-1}\|^2},$$
--   and the hybrid choice (3.7): $\beta_k = -\beta_k^{FR}$ if $\beta_k^{PR} < -\beta_k^{FR}$, $\beta_k = \beta_k^{PR}$ if $|\beta_k^{PR}| \le \beta_k^{FR}$, $\beta_k = \beta_k^{FR}$ if $\beta_k^{PR} > \beta_k^{FR}$.
--   3. **Assumptions 2.1.** The level set $\mathcal L = \{x : f(x) \le f(x_1)\}$ is bounded, and on some open neighbourhood $\mathcal N$ of $\mathcal L$ the function $f$ is continuously differentiable with $\|g(x) - g(\tilde x)\| \le L\|x - \tilde x\|$ for all $x, \tilde x \in \mathcal N$, for some $L > 0$.
--   4. **Line searches** for a step $\alpha$ along $d$ from $x$, with parameters $0 < \sigma_1 < \sigma_2 < 1$: the Wolfe conditions (2.4)–(2.5)
--   $$f(x + \alpha d) \le f(x) + \sigma_1 \alpha \langle g(x), d\rangle,\qquad \langle g(x + \alpha d), d\rangle \ge \sigma_2 \langle g(x), d\rangle;$$
--   the strong Wolfe conditions (2.16)–(2.17), in which the second condition becomes $|\langle g(x + \alpha d), d\rangle| \le -\sigma_2\langle g(x), d\rangle$; and the ideal line search (2.6): $\alpha > 0$ and $f(x + \alpha d) \le f(x + \hat\alpha d)$, where $\hat\alpha$ is the smallest positive stationary point of $\xi(t) = f(x + t d)$.
--   5. **The angle** $\cos\theta_k = -\langle g_k, d_k\rangle / (\|g_k\|\,\|d_k\|)$ (2.1), the **Zoutendijk condition** $\sum_{k\ge 1}\cos^2\theta_k\,\|g_k\|^2 < \infty$ (2.7), and the conclusion $\liminf_{k\to\infty}\|g_k\| = 0$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The space is a finite-dimensional real inner product space, since the paper uses "the scalar product used to compute the gradient" (p. 2) rather than a fixed Euclidean one; `gradient f` is the gradient for that product. Sequences are indexed by $\mathbb N$ and used from index $1$ as in the paper; index $0$ is never constrained. Positive steplengths are part of the run, as on p. 4 ("accepting a positive steplength"). The ratios $\beta^{FR}$, $\beta^{PR}$ and $\cos\theta_k$ are Lean divisions, equal to $0$ when the denominator vanishes. The Zoutendijk summand is written $\langle g_k, d_k\rangle^2/\|d_k\|^2$, which equals $\cos^2\theta_k\|g_k\|^2$ whenever $g_k \ne 0 \ne d_k$. The hybrid (3.7) is written $\max(-\beta^{FR}_k, \min(\beta^{PR}_k, \beta^{FR}_k))$, which is the three-case formula because $\beta^{FR}_k \ge 0$. "Smallest positive stationary point" is encoded as $\xi'(\hat\alpha) = 0$ and no $t \in (0,\hat\alpha)$ with $\xi'(t) = 0$. The liminf is stated as: for every $\varepsilon > 0$ and every $K$ there is $k \ge K$ with $\|g_k\| < \varepsilon$, which is $\liminf \|g_k\| = 0$ for a nonnegative sequence.
-- source:
--   Gilbert & Nocedal, Global convergence properties of conjugate gradient methods for optimization, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, pp. 2–8: (1.1)–(1.5), (2.1), Assumptions 2.1 and (2.2) (p. 3), (2.4)–(2.7) (p. 4), (2.16)–(2.17) (p. 5), (3.7) (p. 8)

import Mathlib

namespace NonlinCG.FRBound

/-!
Gilbert & Nocedal, *Global convergence properties of conjugate gradient methods for
optimization*, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, §1–§3,
pp. 2–8: the problem (1.1), the conjugate gradient iteration (1.2)–(1.3), the formulas
(1.4)–(1.5), the angle (2.1), Assumptions 2.1, the Wolfe conditions (2.4)–(2.5), the ideal
line search (2.6), the Zoutendijk condition (2.7), the strong Wolfe conditions (2.16)–(2.17)
and the hybrid choice (3.7).

Conventions: `E` is a finite-dimensional real inner product space (the "scalar product used to
compute the gradient", p. 2), and `gradient f` is the gradient for that product. Sequences are
indexed from `1` as in the paper; index `0` is never used.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The level set `𝓛 := {x : f(x) ≤ f(x₁)}` (Assumptions 2.1 (i), p. 3). -/
def levelSet (f : E → ℝ) (x₁ : E) : Set E := {x | f x ≤ f x₁}

/-- Assumptions 2.1 (p. 3): the level set `𝓛` is bounded, and on some open neighbourhood `𝒩`
of `𝓛` the function `f` is continuously differentiable with a gradient that is Lipschitz
continuous with a constant `L > 0`, `‖g(x) − g(x̃)‖ ≤ L‖x − x̃‖` for `x, x̃ ∈ 𝒩` (2.2). -/
def Assumptions21 (f : E → ℝ) (x₁ : E) : Prop :=
  Bornology.IsBounded (levelSet f x₁) ∧
  ∃ N : Set E, IsOpen N ∧ levelSet f x₁ ⊆ N ∧ ContDiffOn ℝ 1 f N ∧
    ∃ L : NNReal, 0 < L ∧ LipschitzOnWith L (gradient f) N

/-- `g_k := g(x_k) = ∇f(x_k)`. -/
noncomputable def g (f : E → ℝ) (x : ℕ → E) (k : ℕ) : E := gradient f (x k)

/-- The iteration (1.2)–(1.3) with positive steplengths (p. 2, p. 4), 1-based:
`d₁ = −g₁`, `d_k = −g_k + β_k d_{k−1}` for `k ≥ 2`, and `α_k > 0`,
`x_{k+1} = x_k + α_k d_k` for `k ≥ 1`. Index `0` of every sequence is unused. -/
def IsCGRun (f : E → ℝ) (β α : ℕ → ℝ) (x d : ℕ → E) : Prop :=
  d 1 = -g f x 1 ∧
  (∀ k ≥ 2, d k = -g f x k + β k • d (k - 1)) ∧
  ∀ k ≥ 1, 0 < α k ∧ x (k + 1) = x k + α k • d k

/-- The Fletcher–Reeves scalar (1.4): `β_k^{FR} = ‖g_k‖² / ‖g_{k−1}‖²`. -/
noncomputable def betaFR (f : E → ℝ) (x : ℕ → E) (k : ℕ) : ℝ :=
  ‖g f x k‖ ^ 2 / ‖g f x (k - 1)‖ ^ 2

/-- The Polak–Ribière scalar (1.5): `β_k^{PR} = ⟨g_k, g_k − g_{k−1}⟩ / ‖g_{k−1}‖²`. -/
noncomputable def betaPR (f : E → ℝ) (x : ℕ → E) (k : ℕ) : ℝ :=
  inner ℝ (g f x k) (g f x k - g f x (k - 1)) / ‖g f x (k - 1)‖ ^ 2

/-- The hybrid choice (3.7): `β_k = −β_k^{FR}` if `β_k^{PR} < −β_k^{FR}`, `β_k = β_k^{PR}` if
`|β_k^{PR}| ≤ β_k^{FR}`, `β_k = β_k^{FR}` if `β_k^{PR} > β_k^{FR}`; since `β_k^{FR} ≥ 0` this is
`max(−β_k^{FR}, min(β_k^{PR}, β_k^{FR}))`. -/
noncomputable def betaHybrid (f : E → ℝ) (x : ℕ → E) (k : ℕ) : ℝ :=
  max (-betaFR f x k) (min (betaPR f x k) (betaFR f x k))

/-- The Wolfe conditions (2.4)–(2.5) for the step `α` along `d` from `x`:
`f(x + αd) ≤ f(x) + σ₁α⟨g(x), d⟩` and `⟨g(x + αd), d⟩ ≥ σ₂⟨g(x), d⟩`. -/
def WolfeStep (f : E → ℝ) (σ₁ σ₂ : ℝ) (x d : E) (α : ℝ) : Prop :=
  f (x + α • d) ≤ f x + σ₁ * α * inner ℝ (gradient f x) d ∧
  σ₂ * inner ℝ (gradient f x) d ≤ inner ℝ (gradient f (x + α • d)) d

/-- The strong Wolfe conditions (2.16)–(2.17):
`f(x + αd) ≤ f(x) + σ₁α⟨g(x), d⟩` and `|⟨g(x + αd), d⟩| ≤ −σ₂⟨g(x), d⟩`. -/
def StrongWolfeStep (f : E → ℝ) (σ₁ σ₂ : ℝ) (x d : E) (α : ℝ) : Prop :=
  f (x + α • d) ≤ f x + σ₁ * α * inner ℝ (gradient f x) d ∧
  |inner ℝ (gradient f (x + α • d)) d| ≤ -σ₂ * inner ℝ (gradient f x) d

/-- The ideal line search (2.6): `α > 0` and `f(x + αd) ≤ f(x + α̂d)`, where `α̂` is the smallest
positive stationary point of `ξ(t) := f(x + t d)`, i.e. `ξ'(α̂) = 0` and `ξ'(t) ≠ 0` for every
`t ∈ (0, α̂)`. -/
def IdealStep (f : E → ℝ) (x d : E) (α : ℝ) : Prop :=
  0 < α ∧ ∃ αhat : ℝ, 0 < αhat ∧ HasDerivAt (fun t : ℝ => f (x + t • d)) 0 αhat ∧
    (∀ t ∈ Set.Ioo 0 αhat, ¬ HasDerivAt (fun t : ℝ => f (x + t • d)) 0 t) ∧
    f (x + α • d) ≤ f (x + αhat • d)

/-- `cos θ_k := −⟨g_k, d_k⟩ / (‖g_k‖ ‖d_k‖)` (2.1). -/
noncomputable def cosTheta (f : E → ℝ) (x d : ℕ → E) (k : ℕ) : ℝ :=
  -inner ℝ (g f x k) (d k) / (‖g f x k‖ * ‖d k‖)

/-- The Zoutendijk condition (2.7), `Σ_{k≥1} cos²θ_k ‖g_k‖² < ∞`, with the summand written as
`⟨g_k, d_k⟩² / ‖d_k‖²` (equal to `cos²θ_k ‖g_k‖²` whenever `g_k ≠ 0` and `d_k ≠ 0`). -/
def ZoutendijkCondition (f : E → ℝ) (x d : ℕ → E) : Prop :=
  Summable (fun k : ℕ => inner ℝ (g f x (k + 1)) (d (k + 1)) ^ 2 / ‖d (k + 1)‖ ^ 2)

/-- `liminf_{k→∞} ‖g_k‖ = 0`: for every `ε > 0` and every `K`, some `k ≥ K` has `‖g_k‖ < ε`. -/
def LiminfGradZero (f : E → ℝ) (x : ℕ → E) : Prop :=
  ∀ ε > 0, ∀ K : ℕ, ∃ k ≥ K, ‖g f x k‖ < ε

end NonlinCG.FRBound


