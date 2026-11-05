-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel
-- name    : BauerleRiederMDP_PDMDP_JumpModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:43.071191+00:00
-- url     : https://prove2.me/theorems/f7d0a4ef-dbdc-4433-8075-3cb359f00b80
-- title:
--   Piecewise deterministic jump data $(\varphi,Q,\lambda,r,\beta)$
-- statement:
--   The data shared by the Piecewise Deterministic Markov Decision Model and the continuous-time Markov Decision Chain: the flow $\varphi^\alpha_t(x)$ for relaxed controls $\alpha$, measurable in $(x,\alpha)$ for $\alpha\in A$ and continuous in $t$; the stochastic kernel $Q$ from $E\times U$ to $E$ of the jump goals; the rate $\lambda>0$ of the Poisson process of jump times; the measurable reward rate $r:E\times U\to\mathbb R$; and the discount rate $\beta\ge0$.
--
--   All process-level and embedded objects are defined on this structure, so that the chain is literally a special case, with $\varphi^\alpha_t(x)=x$.
--
--   **Formalization Note** A deterministic control enters the flow as its one-point relaxed control. The flow is extended by $x$ to $t<0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 8.1.1, pp.243–244, and p.257

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.PDMDP

/-- The data common to the Piecewise Deterministic Markov Decision Model of Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 8.1.1,
pp.243–244, PDF 254–255, and to the continuous-time Markov Decision Chain of §8.3, pp.256–257,
PDF 267–268, which is the special case of a constant flow: the flow `φ^α_t(x)`, for relaxed
controls by (8.7), p.250, PDF 261, the stochastic kernel `Q` of the jump goals, the rate `λ > 0` of
the Poisson process of jump times, the reward rate `r` and the discount rate `β ≥ 0`.

The flow is "measurable in `(x, α)`" for `α ∈ A` and "continuous in `t`" (p.244).

**Formalization Note** A deterministic control `α ∈ A` enters the flow as its one-point relaxed
control, for which (8.7) is the initial value problem of p.244. The flow is read at `t ≥ 0` and is
extended by `x` to `t < 0`, so that continuity in `t` is continuity on `ℝ`. -/
structure JumpModel (E U : Type*) [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSpace U] where
  /-- The flow `φ^α_t(x)`, as `flow α x t`. -/
  flow : RelaxedControl U → E → ℝ → E
  flow_nonpos : ∀ α x t, t ≤ 0 → flow α x t = x
  flow_continuous : ∀ α x, Continuous (flow α x)
  flow_measurable : ∀ t, Measurable fun p : E × ControlFn U => flow p.2.toRelaxed p.1 t
  /-- The stochastic kernel `Q` from `E × U` to `E`. -/
  Q : Kernel (E × U) E
  Q_markov : IsMarkovKernel Q
  /-- The rate `λ` of the Poisson process of jump times. -/
  lam : ℝ
  lam_pos : 0 < lam
  /-- The reward rate. -/
  r : E × U → ℝ
  r_measurable : Measurable r
  /-- The discount rate. -/
  β : ℝ
  β_nonneg : 0 ≤ β

attribute [instance] JumpModel.Q_markov

end BauerleRiederMDP.PDMDP


