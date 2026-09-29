-- Prove2me | Definitions.Def_HilbertSixth_Boltzmann
-- name    : HilbertSixth_Boltzmann
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T03:47:34.60899+00:00
-- url     : https://prove2.me/theorems/ba44268d-6bc3-49df-9100-e023aff828c1
-- title:
--   The hard-sphere Boltzmann equation, Maxwellians and the $\mathrm{Bol}_\beta$ norm
-- statement:
--   Formalization of Definition 1.4 of arXiv:2503.01800 (equivalently (1.13)-(1.14) of arXiv:2408.07818): the Cauchy problem for the Boltzmann equation with hard-sphere collision kernel and collision rate $\alpha$,
--
--   $$(\partial_t + v\cdot\nabla_x)\,n = \alpha \int_{\mathbb{R}^d}\int_{\mathbb{S}^{d-1}} \big((v-v_1)\cdot\omega\big)_{+}\big(n' n_1' - n\, n_1\big)\,\mathrm{d}\omega\,\mathrm{d}v_1, \qquad n(0) = n_0,$$
--
--   with $v' = v - ((v-v_1)\cdot\omega)\omega$ and $v_1' = v_1 + ((v-v_1)\cdot\omega)\omega$. The transport operator is expressed along the free characteristics: $s \mapsto n(s, x + (s-t)v, v)$ is required to be differentiable at $s=t$ with derivative $\alpha Q(n,n)(t,x,v)$. The unit sphere carries the $(d-1)$-dimensional Hausdorff measure of $\mathbb{R}^d$.
--
--   Also included: the global Maxwellian $(2\pi)^{-d/2}e^{-|v|^2/2}$, the local Maxwellian
--
--   $$\mathcal{M}(x,v) = \frac{\rho(x)}{(2\pi T(x))^{d/2}}\,e^{-|v-u(x)|^2/(2T(x))}$$
--
--   of equation (1.41), and the bound $\|f\|_{\mathrm{Bol}_\beta} \le B$ for the norm $\|f\|_{\mathrm{Bol}_\beta} = \sum_{k\in\mathbb{Z}^d}\sup_{|x-k|\le 1,\,v} e^{\beta|v|^2}|f(x,v)|$ of equation (1.15) of arXiv:2408.07818.
-- source:
--   Deng--Hani--Ma, Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory, https://arxiv.org/abs/2503.01800, Definition 1.4 (eq. 1.15), eq. (1.41); Deng--Hani--Ma, Long time derivation of the Boltzmann equation from hard sphere dynamics, https://arxiv.org/abs/2408.07818, Definition 1.4 (eq. 1.13-1.14), eq. (1.15)

import Definitions.Def_HilbertSixth_Geometry

/-!
# The hard-sphere Boltzmann equation

Formalization of Definition 1.4 (and equations (1.15), (1.41)) of Deng–Hani–Ma,
*Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic
theory* (arXiv:2503.01800); the same collision operator appears as (1.13)–(1.14) of
the companion paper arXiv:2408.07818.

The unit sphere `S^{d-1}` carries the `(d-1)`-dimensional Hausdorff measure of the
Euclidean space `ℝ^d`.
-/

open MeasureTheory

namespace HilbertSixth

/-- The post-collisional velocity `v' = v - ((v - v₁) · ω) ω`. -/
noncomputable def outVel₁ {d : ℕ} (v v₁ ω : Vec d) : Vec d := v - dotp (v - v₁) ω • ω

/-- The post-collisional velocity `v₁' = v₁ + ((v - v₁) · ω) ω`. -/
noncomputable def outVel₂ {d : ℕ} (v v₁ ω : Vec d) : Vec d := v₁ + dotp (v - v₁) ω • ω

/-- **The hard-sphere collision operator.**
`Q(f, g)(x, v) = ∫_{ℝ^d} ∫_{S^{d-1}} ((v - v₁) · ω)₊ (f(x,v') g(x,v₁') - f(x,v) g(x,v₁)) dω dv₁`,
with `v' = v - ((v-v₁)·ω) ω` and `v₁' = v₁ + ((v-v₁)·ω) ω`, and `dω` the
`(d-1)`-dimensional Hausdorff measure on the unit sphere of `ℝ^d`. -/
noncomputable def collisionOp (d : ℕ) (f g : Vec d → Vec d → ℝ) (x v : Vec d) : ℝ :=
  ∫ v₁ : Vec d, ∫ ω in Metric.sphere (0 : Vec d) 1,
      max (dotp (v - v₁) ω) 0 *
        (f x (outVel₁ v v₁ ω) * g x (outVel₂ v v₁ ω) - f x v * g x v₁)
    ∂(μH[(d : ℝ) - 1])

/-- **Definition 1.4 — the Cauchy problem for the hard-sphere Boltzmann equation**
with collision rate `α` on the time interval `[0, tfin]`:
`(∂_t + v · ∇_x) n = α Q(n, n)`, `n(0, ·, ·) = n₀`.

The transport operator is expressed along the free characteristics: for every
`t ∈ [0, tfin]`, `x` and `v`, the map `s ↦ n(s, x + (s - t) v, v)` is differentiable
at `s = t` with derivative `α Q(n(t), n(t))(x, v)`. -/
def IsBoltzmannSolution (d : ℕ) (α tfin : ℝ) (n₀ : Vec d → Vec d → ℝ)
    (n : ℝ → Vec d → Vec d → ℝ) : Prop :=
  (∀ x v : Vec d, n 0 x v = n₀ x v) ∧
  ∀ t ∈ Set.Icc (0 : ℝ) tfin, ∀ x v : Vec d,
    HasDerivAt (fun s : ℝ => n s (x + (s - t) • v) v)
      (α * collisionOp d (n t) (n t) x v) t

/-- The centred Gaussian `(2π)^{-d/2} e^{-|v|²/2}`, the global Maxwellian of unit
density, zero velocity and unit temperature. -/
noncomputable def globalMaxwellian (d : ℕ) (v : Vec d) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-‖v‖ ^ 2 / 2)

/-- **Equation (1.41) — the local Maxwellian**
`M(x, v) = ρ(x) (2π T(x))^{-d/2} exp(-|v - u(x)|² / (2 T(x)))`
attached to macroscopic density `ρ`, velocity `u` and temperature `T`. -/
noncomputable def localMaxwellian (d : ℕ) (ρ T : Vec d → ℝ) (u : Vec d → Vec d)
    (x v : Vec d) : ℝ :=
  ρ x * (2 * Real.pi * T x) ^ (-(d : ℝ) / 2) *
    Real.exp (-‖v - u x‖ ^ 2 / (2 * T x))

/-- `BolLe d β B f` says that the `Bol_β` norm of (1.15) of arXiv:2408.07818,
`‖f‖_{Bol β} = ∑_{k ∈ ℤ^d} sup {e^{β|v|²} |f(x,v)| : |x - k| ≤ 1, v ∈ ℝ^d}`,
is at most `B`: there is a summable family `c : ℤ^d → ℝ` dominating the suprema over
the unit balls centred at the lattice points, with `∑_k c k ≤ B`. -/
def BolLe (d : ℕ) (β B : ℝ) (f : Vec d → Vec d → ℝ) : Prop :=
  ∃ c : (Fin d → ℤ) → ℝ,
    (∀ (k : Fin d → ℤ) (x v : Vec d),
        ‖x - vecOf (fun i => (k i : ℝ))‖ ≤ 1 →
        Real.exp (β * ‖v‖ ^ 2) * |f x v| ≤ c k) ∧
    Summable c ∧ ∑' k, c k ≤ B

end HilbertSixth


