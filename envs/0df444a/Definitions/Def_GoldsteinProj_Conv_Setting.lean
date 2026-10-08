-- Prove2me | Definitions.Def_GoldsteinProj_Conv_Setting
-- name    : GoldsteinProj_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:07:32.21658+00:00
-- url     : https://prove2.me/theorems/2bb71f57-e840-4895-ae69-a9886c6101e8
-- title:
--   p. 709 — the projection P onto C, the level set S, f″(x, h, h), stationary points, the run x_{k+1} = P(x_k − ρ_k∇f(x_k)), weak cluster points
-- statement:
--   The objects of Goldstein's note on gradient projection in Hilbert space. Throughout, $H$ is a real inner product space with inner product $[x, y]$ (the definitions themselves do not need completeness; the theorems assume $H$ is a Hilbert space). Let $C \subseteq H$ and $f : H \to \mathbb R$.
--
--   1. **Projection.** A map $P : H \to H$ is *the projection onto $C$* if for every $x \in H$ the point $P(x)$ lies in $C$ and is a closest point of $C$ to $x$:
--   $$P(x) \in C, \qquad \|x - P(x)\| \le \|x - y\| \quad \text{for all } y \in C.$$
--   On a nonempty closed convex subset of a Hilbert space this determines $P$ uniquely.
--   2. **Level set.** For $x_0 \in H$, $S = \{x \in C : f(x) \le f(x_0)\}$.
--   3. **Second directional derivative.** Writing $f'(y, h)$ for the Fréchet derivative of $f$ at $y$ applied to $h$,
--   $$f''(x, h, h) = \frac{d}{dt}\Big|_{t=0} f'(x + t h, h),$$
--   the Gâteaux derivative at $x$ in the direction $h$ of $y \mapsto f'(y, h)$ (a directional second derivative, not a Fréchet Hessian).
--   4. **The hypothesis on $\hat S$.** For an open set $\hat S$ and $\rho_0$: for every $x \in \hat S$, $f$ is Fréchet differentiable at $x$, and for every $h \in H$ the map $t \mapsto f'(x + t h, h)$ is differentiable at $t = 0$ and
--   $$|f''(x, h, h)| \le \frac{\|h\|^2}{\rho_0}.$$
--   5. **Stationary point.** A point $z$ is *stationary* if $z \in C$ and $P(z - \rho \nabla f(z)) = z$ for every $\rho > 0$, where $\nabla f(z)$ is the gradient (the Riesz representative of $f'(z, \cdot)$).
--   6. **The run.** Sequences $(\rho_k)$, $(x_k)$ form a run of the method from $x_0$ with parameters $\sigma, \rho_0$ if
--   $$x_0 \text{ is the start}, \qquad \sigma \le \rho_k \le 2\rho_0 - \sigma, \qquad x_{k+1} = P\big(x_k - \rho_k \nabla f(x_k)\big) \quad (k \ge 0).$$
--   7. **Hypothesis of part (iii).** For $\mu \in \mathbb R$: $S$ is convex, $\mu \ge 0$, and $f''(x, h, h) \ge \mu \|h\|^2$ for all $x \in S$, $h \in H$.
--   8. **Weak cluster point.** $z$ is a weak cluster point of $(x_k)$ if it is a cluster point of the sequence in the weak topology of $H$.
--
--   These are the objects in terms of which the THEOREM, its five parts and the claims of its proof are stated.
--
--   **Formalization Note** The projection is a predicate on a map rather than a chosen function, so no junk value is involved. The existence clauses of item 4 come before the bound, because Lean's `fderiv` and `deriv` return $0$ at points of non-differentiability. The weak topology is Mathlib's `WeakSpace ℝ H`, reached through `toWeakSpace`. The run is anchored at $x_0$ (`x 0 = x0`): the paper never names the start, but $S$ is the level set of $x_0$.
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 709, the paragraph before the THEOREM and the THEOREM's hypotheses; (iii) and (iv) for ConvexityHyp and weak cluster points

import Mathlib

namespace GoldsteinProj.Conv

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `P` is the (metric) projection onto `C`: it maps every point of `H` to a closest point of `C`
(Goldstein 1964, p. 709: "assigns to a given point in `H` its closest point in `C`"). -/
def IsProjection (C : Set H) (P : H → H) : Prop :=
  ∀ x, P x ∈ C ∧ ∀ y ∈ C, ‖x - P x‖ ≤ ‖x - y‖

/-- The level set `S = {x ∈ C : f x ≤ f x₀}` (p. 709). -/
def levelSet (f : H → ℝ) (C : Set H) (x0 : H) : Set H :=
  {x | x ∈ C ∧ f x ≤ f x0}

/-- The directional second derivative `f″(x, h, h)` in the sense of Gâteaux: the derivative at
`t = 0` of `t ↦ f′(x + t h, h)`, where `f′(y, h) = fderiv ℝ f y h` is the Fréchet derivative of `f`
at `y` applied to `h`. It is not a Fréchet Hessian. -/
noncomputable def d2 (f : H → ℝ) (x h : H) : ℝ :=
  deriv (fun t : ℝ => fderiv ℝ f (x + t • h) h) 0

/-- The hypothesis of the THEOREM on the open set `Ŝ` (p. 709): for each `x ∈ Ŝ` and `h ∈ H`,
`f′(x, h)` exists in the sense of Fréchet, `f″(x, h, h)` exists in the sense of Gâteaux, and
`|f″(x, h, h)| ≤ ‖h‖² / ρ₀`. -/
def SecondDerivBound (f : H → ℝ) (Shat : Set H) (ρ0 : ℝ) : Prop :=
  ∀ x ∈ Shat, DifferentiableAt ℝ f x ∧
    ∀ h : H, DifferentiableAt ℝ (fun t : ℝ => fderiv ℝ f (x + t • h) h) 0 ∧
      |d2 f x h| ≤ ‖h‖ ^ 2 / ρ0

/-- A stationary point (p. 709): a point `z ∈ C` with `P(z - ρ ∇f(z)) = z` for every `ρ > 0`. -/
def IsStationary [CompleteSpace H] (f : H → ℝ) (C : Set H) (P : H → H) (z : H) : Prop :=
  z ∈ C ∧ ∀ ρ : ℝ, 0 < ρ → P (z - ρ • gradient f z) = z

/-- A run of the gradient projection method of the THEOREM (p. 709): `x 0 = x₀`, step sizes
`σ ≤ ρ_k ≤ 2ρ₀ - σ`, and `x_{k+1} = P(x_k - ρ_k ∇f(x_k))`. -/
def IsGoldsteinRun [CompleteSpace H] (f : H → ℝ) (P : H → H) (x0 : H) (σ ρ0 : ℝ) (ρ : ℕ → ℝ)
    (x : ℕ → H) : Prop :=
  x 0 = x0 ∧ (∀ k, σ ≤ ρ k ∧ ρ k ≤ 2 * ρ0 - σ) ∧
    ∀ k, x (k + 1) = P (x k - ρ k • gradient f (x k))

/-- The hypothesis of part (iii) (p. 709): `S` is convex, `μ ≥ 0`, and `f″(x, h, h) ≥ μ ‖h‖²` for
each `x ∈ S` and `h ∈ H`. -/
def ConvexityHyp (f : H → ℝ) (C : Set H) (x0 : H) (μ : ℝ) : Prop :=
  Convex ℝ (levelSet f C x0) ∧ 0 ≤ μ ∧
    ∀ x ∈ levelSet f C x0, ∀ h : H, μ * ‖h‖ ^ 2 ≤ d2 f x h

/-- `z` is a weak cluster point of the sequence `x`: a cluster point of `x` in the weak topology of
`H` (the topology `WeakSpace ℝ H`), as in part (iv). -/
def IsWeakClusterPt (x : ℕ → H) (z : H) : Prop :=
  MapClusterPt (toWeakSpace ℝ H z) atTop (fun k => toWeakSpace ℝ H (x k))

end GoldsteinProj.Conv


