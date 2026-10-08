-- Prove2me | Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
-- name    : KingmanSubadditive_StationaryIncrements_Stationarity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:24:00.628554+00:00
-- url     : https://prove2.me/theorems/520b2a4a-0676-4de7-8afb-a75a96eade1c
-- title:
--   Stationary processes and processes with stationary increments on $t \ge 0$ (§1.4)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $y=(y_t)_{t\ge 0}$ a real-valued process, each $y_t$ a random variable. Joint laws of processes are laws on the path space $\mathbb R^{[0,\infty)}$ with the product $\sigma$-algebra, i.e. the collection of all finite-dimensional distributions.
--
--   1. $y$ is **stationary** if for every $\tau\ge 0$ the shifted process $(y_{t+\tau})_{t\ge0}$ has the same joint law as $(y_t)_{t\ge0}$.
--   2. $y$ has **stationary increments** if for every $\tau\ge0$
--   $$ (y_{t+\tau}-y_\tau)_{t\ge 0} \;\overset{d}{=}\; (y_t-y_0)_{t\ge0}. $$
--
--   Kingman uses both notions in §1.4 without defining them; these are the standard meanings. A stationary process has stationary increments, which is how the proof of Theorem 3 gets the property its statement asks for.
--
--   **Formalization Note** The process is a function $y:\mathbb R\to\Omega\to\mathbb R$ whose values at $t<0$ play no role. Each definition includes almost-everywhere measurability of every $y_t$, $t\ge0$, so that the push-forward measures compared are never Lean's junk value $0$ for a non-measurable map.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 888, §1.4, Theorem 3 and its proof (notions used, not defined, in the paper)

import Mathlib

open MeasureTheory

namespace KingmanSubadditive.StationaryIncrements

/-- **Stationary process** on the half-line `t ≥ 0` (the notion used, without definition, in the
proof of Theorem 3, Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973),
DOI 10.1214/aop/1176996798, §1.4, p. 888).

A real-time process `y : ℝ → Ω → ℝ` is *stationary* under `P` if each `y t` (`t ≥ 0`) is a random
variable and, for every `τ ≥ 0`, the shifted process `(y_{t+τ})_{t ≥ 0}` has the same joint law
as `(y_t)_{t ≥ 0}`.

**Formalization Note.** The joint law is the push-forward of `P` under the path map
`Ω → (Set.Ici 0 → ℝ)`, with the product σ-algebra on the path space (so equality of laws is
equality of all finite-dimensional distributions). The measurability clause is part of the
definition, so that `Measure.map` never takes its junk value `0` on a non-measurable path map.
Values `y t` for `t < 0` play no role. -/
def IsStationary {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (y : ℝ → Ω → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → AEMeasurable (y t) P) ∧
  ∀ τ : ℝ, 0 ≤ τ →
    P.map (fun ω (t : Set.Ici (0 : ℝ)) => y ((t : ℝ) + τ) ω) =
      P.map (fun ω (t : Set.Ici (0 : ℝ)) => y (t : ℝ) ω)

/-- **Process with stationary increments** on the half-line `t ≥ 0` (Kingman 1973, §1.4,
pp. 888, Theorem 3; the paper uses the standard notion without defining it).

A real-time process `y : ℝ → Ω → ℝ` has *stationary increments* under `P` if each `y t`
(`t ≥ 0`) is a random variable and, for every `τ ≥ 0`, the increment process
`(y_{t+τ} − y_τ)_{t ≥ 0}` has the same joint law as `(y_t − y_0)_{t ≥ 0}`.

**Formalization Note.** Joint laws are push-forwards of `P` under path maps
`Ω → (Set.Ici 0 → ℝ)` with the product σ-algebra; the measurability clause rules out the junk
value `Measure.map f P = 0` for a non-measurable `f`. Values `y t` for `t < 0` play no role. -/
def HasStationaryIncrements {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (y : ℝ → Ω → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → AEMeasurable (y t) P) ∧
  ∀ τ : ℝ, 0 ≤ τ →
    P.map (fun ω (t : Set.Ici (0 : ℝ)) => y ((t : ℝ) + τ) ω - y τ ω) =
      P.map (fun ω (t : Set.Ici (0 : ℝ)) => y (t : ℝ) ω - y 0 ω)

end KingmanSubadditive.StationaryIncrements


