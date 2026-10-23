-- Prove2me | Definitions.Def_GreedyAdvEq_Existence_Setting
-- name    : GreedyAdvEq_Existence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:32.763461+00:00
-- url     : https://prove2.me/theorems/a35749cd-dd22-4f36-b93a-997d49f2efba
-- title:
--   §2, pp. 6–9 — b-bounded f with L-Lipschitz Hessian, approximate local maxima (2), greedy paths (Definition 2.1), the greedy max (4), Definitions 2.3 and 2.5
-- statement:
--   This file fixes the objects of Mangoubi and Vishnoi's min-max framework on $\mathbb R^d\times\mathbb R^d$, where the min-player controls $x$ and the max-player controls $y$.
--
--   **Standing model** (p. 6). A function $f:\mathbb R^d\times\mathbb R^d\to\mathbb R$ satisfies the model with constants $b, L$ if it is $C^2$, it is $b$-bounded, $|f(x,y)|\le b$, and its Hessian is $L$-Lipschitz:
--   $$\|\nabla^2 f(x,y)-\nabla^2 f(\tilde x,\tilde y)\|_{\mathrm{op}}\le L\sqrt{\|x-\tilde x\|^2+\|y-\tilde y\|^2}.$$
--
--   **Approximate local maximum** ((2), p. 6). A point $y$ is an $(\varepsilon,\sqrt{L\varepsilon})$-approximate local maximum of $f(x,\cdot)$ if
--   $$\|\nabla_y f(x,y)\|\le\varepsilon\quad\text{and}\quad\lambda_{\max}\big(\nabla_y^2 f(x,y)\big)\le\sqrt{L\varepsilon}.$$
--
--   **Greedy paths** (Definition 2.1, p. 7). Let $\tau\ge0$ and let $\varphi:[0,\tau]\to\mathbb R^d$ be continuous and differentiable at all but finitely many points. Then $\varphi$ is an $\varepsilon$-greedy path for $f(x,\cdot)$ if at every point $t$ where $\varphi$ is differentiable, $\|\dot\varphi_t\|=1$ (unit speed), $\frac{d}{dt}f(x,\varphi_t)\ge-\varepsilon$, and
--   $$\frac{d}{dt}f(x,\varphi_t)>\varepsilon\qquad\text{or}\qquad \dot\varphi_t^{\top}\,\nabla_y^2 f(x,\varphi_t)\,\dot\varphi_t>\sqrt{L\varepsilon}. \tag{3}$$
--
--   **Greedy max** ((4), p. 7). $S_{\varepsilon,x,y}$ is the set of endpoints $\varphi_\tau$ of $\varepsilon$-greedy paths for $f(x,\cdot)$ with $\varphi_0=y$, and
--   $$g_\varepsilon(x,y)=\sup\{f(x,z): z\in S_{\varepsilon,x,y}\}.$$
--
--   **Approximate local minimum of a discontinuous function** (Definition 2.3, p. 8). For a uniformly bounded $\psi:\mathbb R^d\to\mathbb R$, a point $x^\star$ is an $(\varepsilon,\sigma)$-approximate local minimum of $\psi$ if, with
--   $$\mathcal S(x)=\mathbb E_{\zeta\sim N(0,I_d)}\big[\min\big(\psi(x+\sigma\zeta),\psi(x^\star)\big)\big],$$
--   $\mathcal S$ is twice differentiable at $x^\star$ and $\|\nabla\mathcal S(x^\star)\|\le\varepsilon$, $\lambda_{\min}(\nabla^2\mathcal S(x^\star))\ge-\sqrt\varepsilon$ (5).
--
--   **Greedy adversarial equilibrium** (Definition 2.5, p. 9). $(x^\star,y^\star)$ is an $(\varepsilon,\sigma)$-greedy adversarial equilibrium of $f$ if $y^\star$ is an $(\varepsilon,\sqrt{L\varepsilon})$-approximate local maximum of $f(x^\star,\cdot)$ (6) and $x^\star$ is an $(\varepsilon,\sigma)$-approximate local minimum of $g_\varepsilon(\cdot,y^\star)$ in the sense of Definition 2.3 (7). The same $\varepsilon$ is used in $g_\varepsilon$, in (6) and in (7).
--
--   These objects are shared by every statement of the mission; the goal (Theorem 3.1) asserts that greedy adversarial equilibria exist.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; the joint function lives on `WithLp 2 (ℝᵈ × ℝᵈ)`, whose norm is $\sqrt{\|x\|^2+\|y\|^2}$ (Lean's plain product carries the sup norm), and the Hessian norm is the operator norm of the second Fréchet derivative (the page's displayed formula $\sup_v v^\top Av/\|v\|^2$ is $\lambda_{\max}$, a slip). Eigenvalue bounds are quadratic-form bounds, $\lambda_{\max}(H)\le c\iff\forall v,\ v^\top Hv\le c\|v\|^2$, which is the eigenvalue statement for the symmetric Hessians of $C^2$ functions. In (3), $\frac{d}{dt}f(x,\varphi_t)$ is $\langle\nabla_y f(x,\varphi_t),\dot\varphi_t\rangle$ and the second derivative is read as $\dot\varphi_t^\top\nabla_y^2 f\,\dot\varphi_t$, the second derivative of $f(x,\cdot)$ in the direction of travel; this is how the proofs of Propositions 7.4 and 7.6 use it (the literal $\frac{d^2}{dt^2}$ adds a curvature term $\langle\nabla_y f,\ddot\varphi_t\rangle$ that makes Proposition 7.6 false). "Points where $\varphi$ is differentiable" are interior points $t\in(0,\tau)$, with finitely many interior exceptions; the constant path ($\tau=0$) is greedy, so $y\in S_{\varepsilon,x,y}$ and the supremum in (4) is over a nonempty set bounded by $b$. In Definition 2.3 the Gaussian integrand is required to be integrable, and the first and second derivatives of $\mathcal S$ are asserted to exist (as Fréchet derivatives near and at $x^\star$) before they are bounded, so that neither Lean's zero value for non-integrable integrals nor its zero value for derivatives of non-differentiable functions can satisfy (5). Gaussian smoothing is the published definition `RandomGradFree.Shared.smoothing`.
-- source:
--   Mangoubi, Vishnoi, Greedy Adversarial Equilibrium, arXiv:2006.12363v4, pp. 6–9, (2)–(7), Definitions 2.1, 2.3, 2.5

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

namespace GreedyAdvEq.Existence

open MeasureTheory ProbabilityTheory Filter Topology

/-- `ℝᵈ`, the strategy space of each player (Euclidean norm). -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The joint function `(x, y) ↦ f(x, y)` on `ℝᵈ × ℝᵈ` with the ℓ2 norm `√(‖x‖² + ‖y‖²)`
(`WithLp 2`, not Lean's default sup norm on products). -/
noncomputable def joint {d : ℕ} (f : E d → E d → ℝ) : WithLp 2 (E d × E d) → ℝ :=
  fun p => f (WithLp.ofLp p).1 (WithLp.ofLp p).2

/-- Standing model of §2, p. 6: `f` is `C²` on `ℝᵈ × ℝᵈ`, `b`-bounded (`|f(x,y)| ≤ b`), and has an
`L`-Lipschitz Hessian, `‖∇²f(x,y) − ∇²f(x̃,ỹ)‖_op ≤ L √(‖x − x̃‖² + ‖y − ỹ‖²)`. -/
def IsModel {d : ℕ} (f : E d → E d → ℝ) (b L : ℝ) : Prop :=
  ContDiff ℝ 2 (joint f) ∧
  (∀ x y, |f x y| ≤ b) ∧
  ∀ p q : WithLp 2 (E d × E d),
    ‖fderiv ℝ (fderiv ℝ (joint f)) p - fderiv ℝ (fderiv ℝ (joint f)) q‖ ≤ L * ‖p - q‖

/-- `∇_y f(x, y)`. -/
noncomputable def gradY {d : ℕ} (f : E d → E d → ℝ) (x y : E d) : E d :=
  gradient (f x) y

/-- `∇²_y f(x, y)` as a bilinear form: `hessY f x y v w = vᵀ ∇²_y f(x, y) w`. -/
noncomputable def hessY {d : ℕ} (f : E d → E d → ℝ) (x y : E d) : E d →L[ℝ] E d →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (f x)) y

/-- (2), p. 6, for the maximization in `y`: `y` is an `(ε, √(Lε))`-approximate local maximum of
`f(x, ·)`, i.e. `‖∇_y f(x,y)‖ ≤ ε` and `λ_max(∇²_y f(x,y)) ≤ √(Lε)` — this is (6). -/
def IsApproxLocalMax {d : ℕ} (f : E d → E d → ℝ) (L ε : ℝ) (x y : E d) : Prop :=
  ‖gradY f x y‖ ≤ ε ∧ ∀ v : E d, hessY f x y v v ≤ Real.sqrt (L * ε) * ‖v‖ ^ 2

/-- Definition 2.1, p. 7: `ϕ : [0, τ] → ℝᵈ` is an `ε`-greedy path for `f(x, ·)`. It is continuous
on `[0, τ]`, differentiable at all but finitely many interior points, and at every interior point
`t` where it is differentiable: unit speed `‖ϕ'(t)‖ = 1`, `d/dt f(x, ϕ_t) = ⟨∇_y f(x, ϕ_t), ϕ'(t)⟩ ≥ −ε`,
and (3): `d/dt f(x, ϕ_t) > ε` or `ϕ'(t)ᵀ ∇²_y f(x, ϕ_t) ϕ'(t) > √(Lε)` (the second derivative of
`f(x, ·)` along the direction of travel). -/
def IsGreedyPath {d : ℕ} (f : E d → E d → ℝ) (L ε : ℝ) (x : E d) (τ : ℝ) (ϕ : ℝ → E d) : Prop :=
  0 ≤ τ ∧
  ContinuousOn ϕ (Set.Icc 0 τ) ∧
  {t | t ∈ Set.Ioo 0 τ ∧ ¬ DifferentiableAt ℝ ϕ t}.Finite ∧
  ∀ t ∈ Set.Ioo 0 τ, DifferentiableAt ℝ ϕ t →
    ‖deriv ϕ t‖ = 1 ∧
    -ε ≤ inner ℝ (gradY f x (ϕ t)) (deriv ϕ t) ∧
    (ε < inner ℝ (gradY f x (ϕ t)) (deriv ϕ t) ∨
      Real.sqrt (L * ε) < hessY f x (ϕ t) (deriv ϕ t) (deriv ϕ t))

/-- `S_{ε,x,y}`, p. 7: the endpoints of `ε`-greedy paths for `f(x, ·)` starting at `y`. -/
def greedyReach {d : ℕ} (f : E d → E d → ℝ) (L ε : ℝ) (x y : E d) : Set (E d) :=
  {z | ∃ τ : ℝ, ∃ ϕ : ℝ → E d, IsGreedyPath f L ε x τ ϕ ∧ ϕ 0 = y ∧ ϕ τ = z}

/-- The greedy max (4), p. 7: `g_ε(x, y) = sup {f(x, z) : z ∈ S_{ε,x,y}}`. -/
noncomputable def greedyMax {d : ℕ} (f : E d → E d → ℝ) (L ε : ℝ) (x y : E d) : ℝ :=
  sSup (f x '' greedyReach f L ε x y)

/-- Definition 2.3, p. 8: `xs` is an `(ε, σ)`-approximate local minimum of the uniformly bounded
function `ψ`. With `S(x) = E_{ζ∼N(0,I_d)}[min(ψ(x + σζ), ψ(xs))]`, `S` is differentiable near `xs`
with derivative `S'`, `S'` is differentiable at `xs` with derivative `S''`, and (5):
`‖∇S(xs)‖ ≤ ε` and `λ_min(∇²S(xs)) ≥ −√ε`. The integrand is required to be Gaussian-integrable. -/
def IsApproxLocalMinDisc {d : ℕ} (ψ : E d → ℝ) (ε σ : ℝ) (xs : E d) : Prop :=
  (∃ B : ℝ, ∀ x, |ψ x| ≤ B) ∧
  (∀ x : E d, Integrable (fun ζ : E d => min (ψ (x + σ • ζ)) (ψ xs)) (stdGaussian (E d))) ∧
  ∃ (S' : E d → (E d →L[ℝ] ℝ)) (S'' : E d →L[ℝ] E d →L[ℝ] ℝ),
    (∀ᶠ x in 𝓝 xs,
      HasFDerivAt (RandomGradFree.Shared.smoothing (fun z => min (ψ z) (ψ xs)) σ) (S' x) x) ∧
    HasFDerivAt S' S'' xs ∧
    ‖S' xs‖ ≤ ε ∧
    ∀ v : E d, -Real.sqrt ε * ‖v‖ ^ 2 ≤ S'' v v

/-- Definition 2.5, p. 9: `(xs, ys)` is an `(ε, σ)`-greedy adversarial equilibrium of `f` (with
`L`-Lipschitz Hessian): (6) `ys` is an `(ε, √(Lε))`-approximate local maximum of `f(xs, ·)`, and (7)
`xs` is an `(ε, σ)`-approximate local minimum of `g_ε(·, ys)` in the sense of Definition 2.3. -/
def IsGAE {d : ℕ} (f : E d → E d → ℝ) (L ε σ : ℝ) (xs ys : E d) : Prop :=
  IsApproxLocalMax f L ε xs ys ∧
  IsApproxLocalMinDisc (fun x => greedyMax f L ε x ys) ε σ xs

end GreedyAdvEq.Existence


