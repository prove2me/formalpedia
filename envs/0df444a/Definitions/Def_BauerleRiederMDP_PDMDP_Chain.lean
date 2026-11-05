-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_Chain
-- name    : BauerleRiederMDP_PDMDP_Chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:25.368738+00:00
-- url     : https://prove2.me/theorems/80b5df36-ff34-421c-b7c7-e38c6160167e
-- title:
--   Continuous-time Markov Decision Chain with infinite horizon
-- statement:
--   A **continuous-time Markov Decision Chain** adds a discount rate $\beta\ge0$ to the rate data. It is a Piecewise Deterministic model with the uniformized kernel $Q$ and flow $\varphi^\alpha_t(x)=x$. Its discrete-time model $(E,U,Q',r')$ has
--   $$
--   Q'(\{y\}|x,u):=\frac{\lambda}{\beta+\lambda}Q(\{y\}|x,u),\qquad r'(x,u):=\frac1{\beta+\lambda}r(x,u).
--   $$
--   The stationary rule with $\pi_t=f^*(X_{t-})$ uses the constant control functions $f(x)(t)=f^*(x)$.
--
--   **Formalization Note** The operator $T$ is that of the model $(E,U,Q',r')$, in the form with $Q$. It equals the book's form with the rates at every $x$ with $v(x)>-\infty$, and it has no term $\infty-\infty$ at $v(x)=-\infty$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), pp.256–257

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel
import Definitions.Def_BauerleRiederMDP_PDMDP_RateModel
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.PDMDP

/-- A **continuous-time Markov Decision Chain** with infinite horizon (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §8.3, pp.256–257,
PDF 267–268): rate data and a discount rate `β ≥ 0`. -/
structure Chain (E U : Type*) [MeasurableSpace E] [MeasurableSpace U] extends RateModel E U where
  /-- The discount rate. -/
  β : ℝ
  β_nonneg : 0 ≤ β

namespace Chain

variable {E U : Type*} [TopologicalSpace E] [MeasurableSpace E] [Countable E]
  [MeasurableSingletonClass E] [MeasurableSpace U]

/-- The chain as a Piecewise Deterministic Markov Decision Model (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.257, PDF 268): the
uniformized kernel `Q`, and `φ^α_t(x) = x`, the flow between two jumps being independent of `α`. -/
noncomputable def toJump (C : Chain E U) : JumpModel E U where
  flow _ x _ := x
  flow_nonpos _ _ _ _ := rfl
  flow_continuous _ _ := continuous_const
  flow_measurable _ := measurable_fst
  Q := C.Q
  Q_markov := inferInstance
  lam := C.lam
  lam_pos := C.lam_pos
  r := C.r
  r_measurable := C.r_measurable
  β := C.β
  β_nonneg := C.β_nonneg

/-- The discrete-time model `(E, U, Q', r')` of the chain (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.257, PDF 268):
`Q'({y}|x,u) := λ/(β+λ) Q({y}|x,u)` and `r'(x,u) := r(x,u)/(β+λ)`. Its operator `T` is the maximal
reward operator of the chain,
`(Tv)(x) = 1/(β+λ) sup_u {r(x,u) + λ ∑_y v(y) Q({y}|x,u)}`.

**Formalization Note** The book writes `T` with the rates,
`(Tv)(x) = 1/(β+λ) sup_u {r(x,u) + ∑_y q_{xy}(u) v(y)} + λ/(β+λ) v(x)`, which is the same operator
at every `x` with `v(x) > -∞`. In the form with `Q` no term `∞ - ∞` occurs at `v(x) = -∞`. -/
noncomputable def stage (C : Chain E U) : StageModel E U where
  rew x u := ((C.r (x, u) / (C.β + C.lam) : ℝ) : EReal)
  kern x u := ENNReal.ofReal (C.lam / (C.β + C.lam)) • C.Q (x, u)

end Chain

/-- The stationary decision rule `f*` with constant control functions: `f(x)(t) = f*(x)`, that is,
`π_t = f*(X_{t-})` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.3.1 b), p.258, PDF 269). -/
def stationaryRule {S U : Type*} [MeasurableSpace S] [MeasurableSpace U] (f : S → U)
    (hf : Measurable f) : DecisionRule S U :=
  ⟨fun p => f p.2, hf.comp measurable_snd⟩

end BauerleRiederMDP.PDMDP


