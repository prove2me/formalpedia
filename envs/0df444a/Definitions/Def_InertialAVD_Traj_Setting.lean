-- Prove2me | Definitions.Def_InertialAVD_Traj_Setting
-- name    : InertialAVD_Traj_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:38.304993+00:00
-- url     : https://prove2.me/theorems/6128a781-a63c-458c-99c5-e3b3db186428
-- title:
--   System (1) on $[t_0,+\infty[$, the energies $W$, $h_z$, $\mathcal E_{\lambda,\xi}$, and weak convergence of a trajectory
-- statement:
--   Let $\mathcal H$ be a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, let $\Phi:\mathcal H\to\mathbb R$ be a continuously differentiable convex function, and let $\alpha\in\mathbb R$. The object of study is the second-order differential equation with asymptotically vanishing damping
--   $$\ddot x(t) + \frac{\alpha}{t}\,\dot x(t) + \nabla\Phi(x(t)) = 0. \tag{1}$$
--
--   1. **Solution of (1).** Given $t_0>0$, a pair of maps $x, v:\mathbb R\to\mathcal H$ is a *solution of (1) on $[t_0,+\infty[$* if, at every $t\ge t_0$, the map $x$ has derivative $v(t)$ and $v$ has derivative $-\frac{\alpha}{t}v(t)-\nabla\Phi(x(t))$, both derivatives taken within $[t_0,+\infty[$ (one-sided at $t_0$). Thus $v=\dot x$ and $\ddot x=\dot v$ satisfies (1); the values for $t<t_0$ play no role.
--   2. **Global energy** (4): $W(t)=\frac12\|\dot x(t)\|^2+\Phi(x(t))$.
--   3. **Anchored distance** (5): for $z\in\mathcal H$, $h_z(t)=\frac12\|x(t)-z\|^2$.
--   4. **Anchored energy** (§2.3): for $\lambda,\xi\in\mathbb R$ and a minimizer $x^*$ of $\Phi$ (so $\min\Phi=\Phi(x^*)$),
--   $$\mathcal E_{\lambda,\xi}(t)=t^2\big(\Phi(x(t))-\min\Phi\big)+\frac12\big\|\lambda(x(t)-x^*)+t\,\dot x(t)\big\|^2+\frac{\xi}{2}\|x(t)-x^*\|^2.$$
--   5. **Weak convergence of a trajectory**: $x(t)\rightharpoonup p$ as $t\to+\infty$ means $\langle x(t),y\rangle\to\langle p,y\rangle$ for every $y\in\mathcal H$.
--   6. **Weak sequential limit point**: $p$ is a weak limit point of $x(t)$ as $t\to+\infty$ if there are times $s_n\to+\infty$ with $x(s_n)\rightharpoonup p$ (weak convergence of a sequence, from the published definition `InertialFB.IFB.WeakTendsto`).
--
--   These objects are shared by every statement of the mission: the dissipation of $W$, the differential inequality for $h_z$, and the Lyapunov analysis through $\mathcal E_{\lambda,\xi}$ are all phrased with them.
--
--   **Formalization Note** (1) is encoded as the first-order system $\dot x=v$, $\dot v=-\frac{\alpha}{t}v-\nabla\Phi(x)$ so that no separate second-derivative function is needed; $v(t)$ is always used for $\dot x(t)$. The condition $t_0>0$ is part of the predicate, since $\alpha/0$ would be $0$ in Lean and remove the singularity of the damping. $\nabla\Phi$ is Mathlib's `gradient`. The anchored energy takes $\lambda$ (written `lam`), $\xi$ and $x^*$ as arguments; $\min\Phi$ is written $\Phi(x^*)$, which is the minimum when $x^*$ is a minimizer (each theorem states that hypothesis). Existence of solutions is not assumed or defined: every statement is about a given solution, as in the paper.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 1, (1) and standing assumption; p. 2, §2.1, (4); p. 3, (5); p. 4, §2.3, definition of E_{λ,ξ}; p. 24, Lemma A.2 (weak limit points)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis

open Filter Topology

namespace InertialAVD.Traj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `(x, v)` is a solution of (1), `ẍ(t) + (α/t) ẋ(t) + ∇Φ(x(t)) = 0`, on `[t₀, +∞[`
(Attouch–Chbani–Peypouquet–Redont, Optimization Online 5179 (2015), p. 1, (1); p. 2, §2.1).
It is written as the first-order system `ẋ = v`, `v̇ = -(α/t) v - ∇Φ(x)`: the time origin
`t₀` is positive, and at every `t ≥ t₀` the map `x` has derivative `v t` and `v` has derivative
`-(α/t) • v t - ∇Φ(x t)`, both within `[t₀, +∞[` (one-sided at `t₀`). Values for `t < t₀`
play no role. -/
def IsSolution (Φ : H → ℝ) (α t₀ : ℝ) (x v : ℝ → H) : Prop :=
  0 < t₀ ∧ ∀ t ∈ Set.Ici t₀,
    HasDerivWithinAt x (v t) (Set.Ici t₀) t ∧
    HasDerivWithinAt v (-(α / t) • v t - gradient Φ (x t)) (Set.Ici t₀) t

/-- The global energy (4): `W(t) = ½‖ẋ(t)‖² + Φ(x(t))`, with `v t` standing for `ẋ(t)`. -/
noncomputable def energyW (Φ : H → ℝ) (x v : ℝ → H) (t : ℝ) : ℝ :=
  (1 / 2) * ‖v t‖ ^ 2 + Φ (x t)

/-- The anchored distance (5): `h_z(t) = ½‖x(t) - z‖²`. -/
noncomputable def anchorDist (x : ℝ → H) (z : H) (t : ℝ) : ℝ :=
  (1 / 2) * ‖x t - z‖ ^ 2

/-- The anchored energy of §2.3 (p. 4), for `λ = lam`, `ξ` and a minimizer `x*`:
`E_{λ,ξ}(t) = t²(Φ(x(t)) - min Φ) + ½‖λ(x(t) - x*) + t ẋ(t)‖² + (ξ/2)‖x(t) - x*‖²`,
where `min Φ = Φ x*`. -/
noncomputable def anchoredEnergy (Φ : H → ℝ) (x v : ℝ → H) (lam ξ : ℝ) (xstar : H) (t : ℝ) : ℝ :=
  t ^ 2 * (Φ (x t) - Φ xstar) + (1 / 2) * ‖lam • (x t - xstar) + t • v t‖ ^ 2
    + (ξ / 2) * ‖x t - xstar‖ ^ 2

/-- Weak convergence of a trajectory as `t → +∞`: `x(t) ⇀ p`, i.e. `⟪x t, y⟫ → ⟪p, y⟫` for
every `y ∈ H` (the continuous-time analogue of `InertialFB.IFB.WeakTendsto`). -/
def WeakTendstoAtTop (x : ℝ → H) (p : H) : Prop :=
  ∀ y : H, Tendsto (fun t => inner ℝ (x t) y) atTop (𝓝 (inner ℝ p y))

/-- `p` is a weak sequential limit point of `x(t)` as `t → +∞`: there are times `s n → +∞`
with `x (s n) ⇀ p`. -/
def IsWeakLimitPoint (x : ℝ → H) (p : H) : Prop :=
  ∃ s : ℕ → ℝ, Tendsto s atTop atTop ∧ InertialFB.IFB.WeakTendsto (fun n => x (s n)) p

end InertialAVD.Traj


