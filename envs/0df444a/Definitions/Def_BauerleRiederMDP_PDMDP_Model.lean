-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_Model
-- name    : BauerleRiederMDP_PDMDP_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:23.989018+00:00
-- url     : https://prove2.me/theorems/bd6633bb-4e1c-427e-a84c-9c2edb883a31
-- title:
--   Definition 8.1.1: Piecewise Deterministic Markov Decision Model
-- statement:
--   A **Piecewise Deterministic Markov Decision Model** consists of the data $(E,U,\mu,\lambda,Q,r,\beta)$: the state space $E$, a Borel subset of $\mathbb R^d$; the control action space $U$; the drift $\mu(x,u)\in\mathbb R^d$; the rate $\lambda>0$ of the Poisson process of jump times; the stochastic kernel $Q$ of the jump goals; the measurable reward rate $r$; and the discount rate $\beta\ge0$. For every control and every $x\in E$ the initial value problem
--   $$
--   d\varphi^\alpha_t(x)=\int\mu(\varphi^\alpha_t(x),u)\,\alpha_t(du)\,dt,\qquad\varphi^\alpha_0(x)=x\tag{8.7}
--   $$
--   has a unique solution with values in $E$. For a deterministic control it is $dx_t=\mu(x_t,\alpha_t)\,dt$, $x_0=x$.
--
--   **Formalization Note** Solutions are in the sense of Carathéodory: continuous, equal to $x$ plus the integral of the drift, with the drift integrable. The flow is a field pinned by existence and uniqueness, so it is determined by $\mu$. The relaxed assumption of p.250 is part of the structure and contains the deterministic one.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 8.1.1, pp.243–244, and (8.7), p.250

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.PDMDP

/-- `γ` solves the initial value problem (8.7) of Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.250, PDF 261,
`dφ^α_t(x) = ∫ μ(φ^α_t(x), u) α_t(du) dt`, `φ^α_0(x) = x`, for the relaxed control `α`, and stays
in `E`. For a deterministic control, whose `α_t` are one-point measures, this is the initial value
problem `dx_t = μ(x_t, α_t) dt`, `x_0 = x` of p.244, PDF 255.

**Formalization Note** A solution is one in the sense of Carathéodory: continuous, and equal to
`x` plus the integral of the drift, the drift being integrable so that no Bochner junk value
enters. It is extended by `x` to `t ≤ 0`, which makes solutions on `ℝ₊` and functions on `ℝ` the
same thing. -/
structure IsRelaxedSolution {d : ℕ} {E : Set (EuclideanSpace ℝ (Fin d))} {U : Type*}
    [MeasurableSpace U] (μ : E × U → EuclideanSpace ℝ (Fin d)) (α : RelaxedControl U) (x : E)
    (γ : ℝ → E) : Prop where
  continuous : Continuous γ
  nonpos : ∀ t ≤ 0, γ t = x
  integrable : ∀ t, 0 ≤ t →
    ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), Integrable (fun u => μ (γ s, u)) (α.1 s)
  intervalIntegrable : ∀ t, 0 ≤ t →
    IntervalIntegrable (fun s => ∫ u, μ (γ s, u) ∂(α.1 s)) volume 0 t
  solves : ∀ t, 0 ≤ t → (γ t : EuclideanSpace ℝ (Fin d)) =
    (x : EuclideanSpace ℝ (Fin d)) + ∫ s in (0 : ℝ)..t, ∫ u, μ (γ s, u) ∂(α.1 s)

/-- Definition 8.1.1 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), pp.243–244, PDF 254–255). A **Piecewise Deterministic Markov Decision
Model** consists of the data `(E, U, μ, λ, Q, r, β)`: the state space `E`, a Borel subset of `ℝ^d`,
the control action space `U`, the drift `μ(x,u) ∈ ℝ^d`, the rate `λ > 0`, the stochastic kernel `Q`
of the jump goals, the measurable reward rate `r`, and the discount rate `β ≥ 0`. For all controls
the initial value problem has a unique solution `φ^α_t(x) ∈ E`, which is the field `flow`, measurable
in `(x,α)` and continuous in `t` (`JumpModel`). The relaxed controls are included: "we again assume
that a unique solution of (8.7) exists" (p.250, PDF 261), which covers `α ∈ A`.

**Formalization Note** `flow` is pinned by `flow_solves` and `flow_unique`, so it is determined by
`μ`. `U` is any Borel space with a topology here; the theorems of the mission take `U` compact and
metrizable, which is a compact Borel subset of a Polish space. Measurability of `μ` is the standing
convention of the book and is not printed. -/
structure Model {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) (U : Type*) [MeasurableSpace U]
    extends JumpModel E U where
  E_measurable : MeasurableSet E
  /-- The drift `μ(x,u)`. -/
  μ : E × U → EuclideanSpace ℝ (Fin d)
  μ_measurable : Measurable μ
  flow_solves : ∀ α x, IsRelaxedSolution μ α x (flow α x)
  flow_unique : ∀ α x γ, IsRelaxedSolution μ α x γ → γ = flow α x

end BauerleRiederMDP.PDMDP


