-- Prove2me | Definitions.Def_PalmQueueing_Loynes_StationaryRegime
-- name    : PalmQueueing_Loynes_StationaryRegime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T23:09:54.615709+00:00
-- url     : https://prove2.me/theorems/39022cec-81bc-4a6c-aa64-7bf1a43bf4d8
-- title:
--   Pathwise workload equations and the traffic intensity in [0, ∞]
-- statement:
--   The workload processes of §2.1 and §2.7 are random processes whose defining equations hold $P$-almost surely. This module states those equations **at one sample point** $\omega$, so that theorems can require them almost surely.
--
--   - The **traffic intensity** (2.1.3) is $\rho = \lambda E^0_A[\sigma_0] \in [0, \infty]$, computed as $\lambda$ times the Lebesgue integral of the non-negative service time $\sigma_0$ under the Palm probability $P^0_A$; it is $+\infty$ when $E^0_A[\sigma_0] = +\infty$.
--   - A sample path $t \mapsto W(t,\omega)$ is a **workload path** of the $G/G/1/\infty$ queue, with left limits $W_l(t,\omega) = W(t-,\omega)$, when it is right-continuous, has these left limits at every $s$, and satisfies Lindley's equation
--   $$ W(t) = \big(W(T_n-) + \sigma_n - (t - T_n)\big)^+, \qquad t \in [T_n, T_{n+1}),\ n \in \mathbb{Z}. \tag{2.1.6} $$
--   - A sample path $t \mapsto W(t,\omega)$ satisfies the **fluid-queue recurrence** when, for all $s \le t$,
--   $$ W(t) = \max\Big( W(s) + A_{s,t} - C_{s,t},\ \sup_{s \le u \le t} (A_{u,t} - C_{u,t}) \Big). \tag{2.7.6} $$
--
--   **Formalization Note.** Paths are real-valued, so a workload path is finite. The traffic intensity uses the lower Lebesgue integral in $[0,\infty]$ rather than a Bochner integral, which would return $0$ for a non-integrable $\sigma_0$.
-- source:
--   Baccelli & Brémaud, Elements of Queueing Theory, 2nd ed., Springer 2003, DOI 10.1007/978-3-662-11657-9, pp.77-78 (Eqs. (2.1.3), (2.1.6)) and p.131 (Eq. (2.7.6))

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_SingleServerQueue
import Definitions.Def_PalmQueueing_Loynes_FluidQueue

/-!
# Pathwise workload equations and the traffic intensity in `[0, ∞]` (§2.1.1-2.1.2, §2.7.2)

The book's workload processes are random processes whose defining equations — Lindley's equation
(2.1.6) and the fluid recurrence (2.7.6) — hold `P`-almost surely: on a `P`-null, `θ_t`-invariant
set of sample paths (for instance one on which `Σ σ_i` grows faster than `−T_n`) no finite solution
exists at all, whatever `ρ` is. The two predicates below state the equations **at one sample point
`ω`**, so that a theorem can require them `P`-a.s. (`∀ᵐ ω ∂P, IsWorkloadPath Q W Wl ω`), which is
the book's reading.

The traffic intensity is also given here with values in `[0, ∞]`: `ρ = λ E⁰_A[σ₀]` is `+∞` when
`σ₀` is not `P⁰_A`-integrable, and then no stationary workload exists. A Bochner integral would
return `0` for such a `σ₀` and make "`ρ < 1`" hold for the most unstable input.
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology
open PalmQueueing.Palm
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `(2.1.3)` in `[0, ∞]`: the **traffic intensity** `ρ = λ E⁰_A[σ₀]`, computed with the lower
Lebesgue integral of the non-negative service time, so that `ρ = +∞` when `E⁰_A[σ₀] = +∞`. -/
noncomputable def Queue.trafficIntensity (Q : Queue Ω) : ℝ≥0∞ :=
  ENNReal.ofReal Q.toPalmSetting.lam * ∫⁻ ω, ENNReal.ofReal (Q.sigma 0 ω) ∂Q.toPalmSetting.P0

/-- The sample path `t ↦ W(t, ω)` is a **workload path** of the queue `Q`, with left limits
`t ↦ Wl(t, ω)` (p.78): right-continuous, with `Wl(s, ω) = W(s−, ω)` for every `s`, and obeying
Lindley's equation

`(2.1.6)  W(t) = (W(T_n−) + σ_n − (t − T_n))⁺,  t ∈ [T_n, T_{n+1})`

for every `n ∈ ℤ`. Being `ℝ`-valued, the path is finite. -/
def IsWorkloadPath (Q : Queue Ω) (W Wl : ℝ → Ω → ℝ) (ω : Ω) : Prop :=
  (∀ s : ℝ, ContinuousWithinAt (fun u => W u ω) (Set.Ici s) s) ∧
  (∀ s : ℝ, Tendsto (fun u => W u ω) (nhdsWithin s (Set.Iio s)) (nhds (Wl s ω))) ∧
  ∀ (n : ℤ) (t : ℝ),
    t ∈ Set.Ico (Q.toPalmSetting.N.T n ω) (Q.toPalmSetting.N.T (n + 1) ω) →
      W t ω = max (Wl (Q.toPalmSetting.N.T n ω) ω + Q.sigma n ω
        - (t - Q.toPalmSetting.N.T n ω)) 0

/-- The sample path `t ↦ W(t, ω)` satisfies the fluid-queue recurrence `(2.7.6)` (p.131): for all
`s ≤ t`,

`W(t) = max( W(s) + A_{s,t} − C_{s,t}, sup_{s ≤ u ≤ t} (A_{u,t} − C_{u,t}) )`. -/
def IsFluidWorkloadPath (A C : ℝ → ℝ → Ω → ℝ) (W : ℝ → Ω → ℝ) (ω : Ω) : Prop :=
  ∀ s t : ℝ, s ≤ t →
    W t ω = max (W s ω + A s t ω - C s t ω)
      (sSup {x | ∃ u : ℝ, s ≤ u ∧ u ≤ t ∧ x = A u t ω - C u t ω})

end PalmQueueing.Loynes


