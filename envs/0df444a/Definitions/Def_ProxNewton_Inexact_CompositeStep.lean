-- Prove2me | Definitions.Def_ProxNewton_Inexact_CompositeStep
-- name    : ProxNewton_Inexact_CompositeStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:35:53.638603+00:00
-- url     : https://prove2.me/theorems/e0d98d73-67ef-48d5-a894-6bd043f54b92
-- title:
--   Proximal mapping (2.1), composite gradient step (2.3), $G_{f/M}$ and the second-order model $\hat g_k$
-- statement:
--   Throughout, the space is $\mathbb R^n$ with the Euclidean inner product $\langle x,y\rangle = x^Ty$ and norm $\|\cdot\|$. The composite objective is $f = g + h$ with a smooth part $g:\mathbb R^n\to\mathbb R$ and a nonsmooth part $h$ that may take the value $+\infty$; $h$ is described by its effective domain $D = \operatorname{dom} h$ and its (finite) values on $D$.
--
--   1. **Proper closed convex nonsmooth part.** $(D,h)$ is *proper, closed and convex* when $D$ is nonempty and convex, $h$ is convex on $D$, and the extended-valued function equal to $h$ on $D$ and to $+\infty$ off $D$ is lower semicontinuous.
--   2. **Proximal mapping** (Eq. (2.1)). For $v\in\mathbb R^n$,
--   $$\operatorname{prox}_h(v) := \operatorname*{arg\,min}_{y\in\mathbb R^n}\; h(y) + \tfrac12\|y - v\|^2 ,$$
--   where the minimization runs over $y \in D$ since $h = +\infty$ off $D$.
--   3. **Composite gradient step** (Eq. (2.3)). For a step length $t$,
--   $$G_{t f}(x) := \frac1t\Big(x - \operatorname{prox}_{t h}\big(x - t\nabla g(x)\big)\Big),$$
--   and $G_f := G_{1 f}$. The step depends on the split of $f$ into $g$ and $h$, not on $f$ alone.
--   4. **The step on $f/M$.** For $M > 0$, $G_{f/M}$ is the composite gradient step with unit step length on the composite function $f/M = g/M + h/M$:
--   $$G_{f/M}(x) = x - \operatorname{prox}_{h/M}\big(x - \tfrac1M\nabla g(x)\big).$$
--   5. **Hessian and model.** $\nabla^2 g(x)$ is the derivative of the gradient map at $x$. The second-order model of $g$ at $x_k$ with the exact Hessian is
--   $$\hat g_k(y) := g(x_k) + \nabla g(x_k)^T(y - x_k) + \tfrac12 (y - x_k)^T\nabla^2 g(x_k)(y - x_k),$$
--   and $\hat f_k := \hat g_k + h$, so $G_{\hat f_k/M}$ is item 4 with $g$ replaced by $\hat g_k$.
--
--   These objects are the vocabulary of the adaptive stopping condition (2.24) and of the local convergence analysis of §3.4.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. The proximal mapping is made total with `Classical.epsilon` on the set of minimizers of $h(y) + \frac12\|y-v\|^2$ over $D$; for a proper closed convex $(D,h)$ this set is a singleton for every $v$, so the chosen point is the paper's $\operatorname{prox}_h(v)$, and no theorem of the mission uses the junk value. The composite step is `compGradStep g D h t x`, $G_{f/M}$ is `scaledStep g D h M`, the Hessian is `fderiv ℝ (gradient g) x`, and the model is `quadModel g xk`.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 3, Eq. (2.1) and Eq. (2.3); p. 4, §2.1 property 3 (Gf = G_1 f); p. 5 (model ĝ_k); p. 9, Eq. (2.24) (G_{f/M})

import Mathlib

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace

variable {n : ℕ}

open Classical in
/-- The nonsmooth part, given by its effective domain `D` and its values `h` on `D`, is a proper
closed convex function: `D` is nonempty and convex, `h` is convex on `D`, and the extended-valued
function equal to `h` on `D` and to `+∞` off `D` is lower semicontinuous. -/
def IsProperClosedConvex (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  D.Nonempty ∧ Convex ℝ D ∧ ConvexOn ℝ D h ∧
    LowerSemicontinuous (fun x => if x ∈ D then (h x : EReal) else ⊤)

/-- `y` is a minimizer of `h(y) + ½‖y - v‖²` over the effective domain `D` of `h`
(Lee–Sun–Saunders, Eq. (2.1)). -/
def IsProxPoint (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (v y : EuclideanSpace ℝ (Fin n)) : Prop :=
  y ∈ D ∧ ∀ z ∈ D, h y + ‖y - v‖ ^ 2 / 2 ≤ h z + ‖z - v‖ ^ 2 / 2

/-- The proximal mapping `prox_h(v) = argmin_y h(y) + ½‖y - v‖²` (Eq. (2.1)), with `h = +∞`
off `D`. For a proper closed convex `h` the minimizer exists and is unique for every `v`, so the
choice is the paper's `prox_h(v)`; otherwise it is an unspecified point. -/
noncomputable def prox (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Classical.epsilon (IsProxPoint D h v)

/-- The composite gradient step (Eq. (2.3)) with step length `t` on the composite function
`g + h` (smooth part `g`, nonsmooth part `h` with domain `D`):
`G_t(x) = (1/t)(x - prox_{t h}(x - t ∇g(x)))`. The paper's `Gf` is the case `t = 1`. -/
noncomputable def compGradStep (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  t⁻¹ • (x - prox D (fun y => t * h y) (x - t • gradient g x))

/-- `G_{f/M}`: the composite gradient step with unit step length on the composite function
`f/M = g/M + h/M`, i.e. `x - prox_{h/M}(x - ∇g(x)/M)`. -/
noncomputable def scaledStep (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  compGradStep (fun y => g y / M) D (fun y => h y / M) 1

/-- The Hessian `∇²g(x)`, the derivative of the gradient map, as a linear operator. -/
noncomputable def hessian (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (gradient g) x

/-- The second-order model of `g` at `x_k` with the exact Hessian `H_k = ∇²g(x_k)` (p. 5):
`ĝ_k(y) = g(x_k) + ∇g(x_k)ᵀ(y - x_k) + ½ (y - x_k)ᵀ ∇²g(x_k) (y - x_k)`. -/
noncomputable def quadModel (g : EuclideanSpace ℝ (Fin n) → ℝ) (xk : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => g xk + ⟪gradient g xk, y - xk⟫ + (1 / 2) * ⟪y - xk, hessian g xk (y - xk)⟫

end ProxNewton.Inexact


