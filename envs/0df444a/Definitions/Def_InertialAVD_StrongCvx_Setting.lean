-- Prove2me | Definitions.Def_InertialAVD_StrongCvx_Setting
-- name    : InertialAVD_StrongCvx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:38.517792+00:00
-- url     : https://prove2.me/theorems/3a0004db-ee5e-4437-bf07-e9ed92e82ea6
-- title:
--   Standing assumption, system (1), strong convexity, the anchored energies E_{λ,ξ} and E^p_λ, and the parameters p, λ, t₁ of Theorem 3.4
-- statement:
--   Let $\mathcal H$ be a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, and let $\Phi:\mathcal H\to\mathbb R$ be a continuously differentiable function with gradient $\nabla\Phi$. Fix $\alpha>0$ and an initial time $t_0>0$.
--
--   **Solutions of (1).** A *solution* of the inertial system with asymptotic vanishing damping
--   $$\ddot x(t)+\frac{\alpha}{t}\dot x(t)+\nabla\Phi(x(t))=0\qquad (t\ge t_0)\tag{1}$$
--   is a pair of maps $x,v:\mathbb R\to\mathcal H$ such that, at every $t\ge t_0$, $x$ has (one-sided, within $[t_0,+\infty[$) derivative $v(t)$, and $v$ has derivative $-\frac{\alpha}{t}v(t)-\nabla\Phi(x(t))$. Thus $v=\dot x$ and $\ddot x$ satisfies (1) on $[t_0,+\infty[$.
--
--   **Strong convexity.** $\Phi$ is *strongly convex with constant $\mu$* if $\mu>0$ and
--   $$\Phi(y)\ \ge\ \Phi(x)+\langle\nabla\Phi(x),y-x\rangle+\frac{\mu}{2}\|x-y\|^2\qquad\text{for all }x,y\in\mathcal H.$$
--
--   **Anchored energies.** For a point $x^*$ (in every theorem, a minimizer of $\Phi$, so that $\min\Phi=\Phi(x^*)$) and real parameters $\lambda,\xi,p$, define for $t\ge t_0$
--   $$\mathcal E_{\lambda,\xi}(t)=t^2\big(\Phi(x(t))-\min\Phi\big)+\tfrac12\|\lambda(x(t)-x^*)+t\dot x(t)\|^2+\tfrac{\xi}{2}\|x(t)-x^*\|^2,$$
--   $$\mathcal E^p_\lambda(t)=t^p\,\mathcal E_{\lambda,0}(t)=t^p\Big(t^2\big(\Phi(x(t))-\min\Phi\big)+\tfrac12\|\lambda(x(t)-x^*)+t\dot x(t)\|^2\Big).$$
--
--   **Parameters of Theorem 3.4.** For $\alpha>3$ and $\mu>0$, the proof of Theorem 3.4 fixes
--   $$p=\tfrac23(\alpha-3),\qquad \lambda=\tfrac23\alpha,\qquad t_1=\max\Big\{t_0,\sqrt{\tfrac{p\lambda}{\mu}}\Big\}.$$
--
--   These objects are shared by every statement of the mission: the energy $\mathcal E^p_\lambda$ is the Lyapunov function whose growth control yields the rate $\mathcal O(t^{-2\alpha/3})$ for strongly convex $\Phi$.
--
--   **Formalization Note** `IsSolution Φ α t₀ x v` includes $t_0>0$; derivatives are `HasDerivWithinAt … (Set.Ici t₀) t`, so at $t_0$ they are right derivatives; values of $x,v$ before $t_0$ play no role. `IsStronglyConvex Φ μ` is the gradient inequality as printed on p. 10 (with `gradient Φ`), together with $\mu>0$; continuous differentiability of $\Phi$ is a separate hypothesis of each theorem. `energy Φ x v xstar lam ξ t` is $\mathcal E_{\lambda,\xi}(t)$ with $\min\Phi$ written as $\Phi(x^*)$, and `energyP … lam p t` is $\mathcal E^p_\lambda(t)$, with the real power $t^p$ (`Real.rpow`, used only for $t\ge t_0>0$). `pExp α`, `lam α`, `t1 t₀ α μ` are $p$, $\lambda$, $t_1$ above. The definitions carry no hypotheses; $\lambda\ge0$, $p\ge0$, $x^*\in\operatorname{argmin}\Phi$ are stated in each theorem.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 1 (standing assumption, (1)), p. 2 (§2.1, t₀ > 0), p. 4 (§2.3, E_{λ,ξ}, E^p_λ), p. 10 (§3.3, strong convexity), p. 11 (proof of Theorem 3.4: p, λ, t₁)

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting

open InnerProductSpace

namespace InertialAVD.StrongCvx

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Strong convexity with constant `μ` (p. 10): `μ > 0` and
`Φ(y) ≥ Φ(x) + ⟨∇Φ(x), y − x⟩ + (μ/2)‖x − y‖²` for all `x, y ∈ H`. -/
def IsStronglyConvex (Φ : H → ℝ) (μ : ℝ) : Prop :=
  0 < μ ∧ ∀ x y : H, Φ x + ⟪gradient Φ x, y - x⟫_ℝ + μ / 2 * ‖x - y‖ ^ 2 ≤ Φ y

/-- The anchored energy `E_{λ,ξ}(t) = t²(Φ(x(t)) − min Φ) + ½‖λ(x(t) − x*) + t ẋ(t)‖²
+ (ξ/2)‖x(t) − x*‖²` (§2.3, p. 4); `min Φ` is written `Φ x*` since `x* ∈ argmin Φ`. -/
noncomputable def energy (Φ : H → ℝ) (x v : ℝ → H) (xstar : H) (lam ξ t : ℝ) : ℝ :=
  t ^ 2 * (Φ (x t) - Φ xstar) + 1 / 2 * ‖lam • (x t - xstar) + t • v t‖ ^ 2
    + ξ / 2 * ‖x t - xstar‖ ^ 2

/-- The anchored energy `E^p_λ(t) = t^p E_{λ,0}(t)` (§2.3, p. 4), with the real power `t ^ p`. -/
noncomputable def energyP (Φ : H → ℝ) (x v : ℝ → H) (xstar : H) (lam p t : ℝ) : ℝ :=
  t ^ p * energy Φ x v xstar lam 0 t

/-- The exponent fixed in the proof of Theorem 3.4 (p. 11): `p = (2/3)(α − 3)`. -/
noncomputable def pExp (α : ℝ) : ℝ := 2 / 3 * (α - 3)

/-- The anchor coefficient fixed in the proof of Theorem 3.4 (p. 11): `λ = (2/3)α`. -/
noncomputable def lam (α : ℝ) : ℝ := 2 / 3 * α

/-- The time `t₁ = max {t₀, √(pλ/μ)}` of the proof of Theorem 3.4 (p. 11). -/
noncomputable def t1 (t₀ α μ : ℝ) : ℝ := max t₀ (Real.sqrt (pExp α * lam α / μ))

end InertialAVD.StrongCvx


