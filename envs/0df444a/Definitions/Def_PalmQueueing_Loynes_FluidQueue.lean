-- Prove2me | Definitions.Def_PalmQueueing_Loynes_FluidQueue
-- name    : PalmQueueing_Loynes_FluidQueue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T23:05:51.897189+00:00
-- url     : https://prove2.me/theorems/3faa1d24-0e36-42d3-a36c-cb19997bd818
-- title:
--   The fluid queue: arrival and service measures and the fluid Loynes problem
-- statement:
--   §2.7 replaces the discrete customers of §2.1 by general $\theta_t$-compatible,
--   $\sigma$-finite, non-negative random measures $M$ on the real line. Writing
--   $M_{s,t} = M([s,t))$, such a measure satisfies, for all $s \le u \le t$,
--   $M_{s,t} = M_{s,u} + M_{u,t}$, and for all $s \le t$, $M_{s,t} = M_{0,t-s} \circ \theta_s$; the
--   map $t \mapsto M_{s,t}$ is continuous on the left.
--
--   A **fluid queue** is defined from two such measures, $A$ and $C$, the arrival and the service
--   measures: $A_{s,t}$ is the amount of fluid which arrives to the queue on the interval $[s,t)$,
--   whereas $C_{s,t}$ is the maximum amount of fluid that the server can drain on $[s,t)$. Fluid that
--   cannot be drained instantly accumulates in the buffer. Both $A$ and $C$ are assumed to have
--   positive and finite intensities, denoted $\lambda$ and $\mu$ respectively.
--
--   The **Loynes problem for the fluid queue** (p.131) asks whether there is a compatible process
--   $W(t) = W(0)\circ\theta_t$ such that, for all $s \le t$,
--   $$ W(t) = \max\Big( W(s) + A_{s,t} - C_{s,t}, \;\; \sup_{s \le u \le t} (A_{u,t} - C_{u,t}) \Big) .
--   \tag{2.7.6} $$
--
--   `fluidLoynesSet` is the set whose supremum is the fluid Loynes variable (2.7.7),
--   $\{A_{u,t} - C_{u,t} : u \le t\}$. Taking $u = t$ shows it contains $0$, so it is never empty.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, §2.7-§2.7.2, pp. 128-131

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# The fluid queue (§2.7, pp.128-131)

§2.7 replaces the discrete customers of §2.1 by two `θ_t`-compatible, σ-finite, non-negative random
measures on the line: the **arrival measure** `A`, where `A_{s,t}` is the amount of fluid arriving
on `[s, t)`, and the **service measure** `C`, where `C_{s,t}` is the maximum amount the server can
drain on `[s, t)`. Both are assumed to have positive finite intensities, `λ` and `µ`.

A random measure enters through the three properties p.128 lists for `M_{s,t} = M([s,t))`:
additivity, the flow relation `M_{s,t} = M_{0,t−s} ∘ θ_s`, and non-negativity.
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `m` is the interval function `M_{s,t} = M([s,t))` of a `θ_t`-compatible non-negative random
measure (p.128). -/
def IsFlowMeasure (θ : Flow Ω) (m : ℝ → ℝ → Ω → ℝ) : Prop :=
  (∀ (s t : ℝ) (ω : Ω), s ≤ t → 0 ≤ m s t ω) ∧
  (∀ (s u t : ℝ) (ω : Ω), s ≤ u → u ≤ t → m s t ω = m s u ω + m u t ω) ∧
  (∀ (s t : ℝ) (ω : Ω), s ≤ t → m s t ω = m 0 (t - s) (θ s ω)) ∧
  (∀ (s t : ℝ), Measurable fun ω => m s t ω)

/-- The Loynes problem for the fluid queue, `(2.7.6)` (p.131): `{W(t)}` is a workload process of
the fluid queue with arrival measure `A` and service measure `C` when, for all `s ≤ t`,

`W(t) = max( W(s) + A_{s,t} − C_{s,t}, sup_{s ≤ u ≤ t} (A_{u,t} − C_{u,t}) )`. -/
def IsFluidWorkload (A C : ℝ → ℝ → Ω → ℝ) (W : ℝ → Ω → ℝ) : Prop :=
  ∀ (s t : ℝ) (ω : Ω), s ≤ t →
    W t ω = max (W s ω + A s t ω - C s t ω)
      (sSup {x | ∃ u : ℝ, s ≤ u ∧ u ≤ t ∧ x = A u t ω - C u t ω})

/-- The set whose supremum is the fluid Loynes variable `(2.7.7)`:
`{ A_{u,t} − C_{u,t} : u ≤ t }`. It contains `0` (take `u = t`), so it is never empty. -/
def fluidLoynesSet (A C : ℝ → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : Set ℝ :=
  {x | ∃ u : ℝ, u ≤ t ∧ x = A u t ω - C u t ω}

end PalmQueueing.Loynes


