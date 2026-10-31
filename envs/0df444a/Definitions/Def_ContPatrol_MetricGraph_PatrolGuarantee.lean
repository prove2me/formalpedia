-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_PatrolGuarantee
-- name    : ContPatrol_MetricGraph_PatrolGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:44.823232+00:00
-- url     : https://prove2.me/theorems/01b0a0cc-1400-4ee4-a44d-1f34a4581453
-- title:
--   Mixed strategies and the guarantees they secure
-- statement:
--   A **mixed patrol** is a family of patrols $S_\omega$ indexed by a probability space $(\Omega,P)$. It **guarantees** $r$ if every pure attack $(x,\tau)$ with $\tau\ge0$ is intercepted with probability at least $r$:
--   $$P\{\omega: x\in S_\omega([\tau,\tau+\alpha])\}\ge r .$$
--
--   A **mixed attack** is a probability measure $\nu$ on pairs (point, start time) with no mass on negative start times. It **holds the Patroller to** $r$ if every patrol $S$ intercepts it with probability at most $r$:
--   $$\nu\{(x,\tau): x\in S([\tau,\tau+\alpha])\}\le r .$$
--
--   These are the two sides of the zero-sum game whose value is the interception probability under best play.
--
--   **Formalization Note** Each evaluation $\omega\mapsto S_\omega(t)$ is required to be measurable, so that interception probabilities are genuine probabilities. No upper bound is placed on the start time of an attack (no finite horizon).
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, §3, pp.5–6

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_IsPatrol

namespace ContPatrol

namespace MetricGraph

open MeasureTheory

variable {V E : Type}

/-- **A mixed patrol guaranteeing interception probability r.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, p.6:
"For mixed strategies, the expected payoff can be interpreted as the probability that the attack
is intercepted."

A mixed patrol is a family of patrols `S ω` indexed by a probability space `(Ω, P)`.
`G.PatrolGuarantee α P S r` says: `P` is a probability measure, every `S ω` is a patrol, every
evaluation `ω ↦ S ω t` is measurable, and every pure attack `(x, τ)` with `τ ≥ 0` is intercepted
with probability at least `r`.

**Formalization Note.** Measurability of the evaluations is required so that the interception
probability is a genuine probability rather than an outer measure (which could overstate a
Patroller guarantee). Guarantees against pure attacks are guarantees against mixed attacks, by
averaging. -/
def PatrolGuarantee (G : MetricGraph V E) (α : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Ω → ℝ → G.Point) (r : ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ ω, G.IsPatrol (S ω)) ∧ (∀ t, Measurable fun ω => S ω t) ∧
    ∀ (x : G.Point) (τ : ℝ), 0 ≤ τ → r ≤ (P {ω | G.Intercepts α (S ω) (x, τ)}).toReal

/-- **A mixed attack holding every patrol to interception probability at most r.**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, §3, pp.5–6.

A mixed attack is a probability measure `ν` on pairs `(x, τ)` (attacked point, start time) with
no mass on start times `τ < 0`. `G.AttackGuarantee α ν r` says that every patrol intercepts it
with probability at most `r`.

**Formalization Note.** No finite time horizon is imposed on `τ` (p.6: "We follow Garrec (2019)
in not imposing a finite time horizon"). The interception set need not be measurable for an
arbitrary patrol; `ν` of it is then the outer measure, which only makes an upper bound harder. -/
def AttackGuarantee (G : MetricGraph V E) (α : ℝ) (ν : Measure (G.Point × ℝ)) (r : ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ν {a | a.2 < 0} = 0 ∧
    ∀ S : ℝ → G.Point, G.IsPatrol S → (ν {a | G.Intercepts α S a}).toReal ≤ r

end MetricGraph

end ContPatrol


