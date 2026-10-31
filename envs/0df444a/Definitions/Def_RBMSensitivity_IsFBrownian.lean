-- Prove2me | Definitions.Def_RBMSensitivity_IsFBrownian
-- name    : RBMSensitivity_IsFBrownian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:21.042029+00:00
-- url     : https://prove2.me/theorems/ae3b8c56-d429-4898-8c53-23f3017fef2a
-- title:
--   A $J$-dimensional $\{\mathcal F_t\}$-Brownian motion
-- statement:
--   A **$J$-dimensional $\{\mathcal F_t\}$-Brownian motion** on $(\Omega,\mathcal F,\mathbb P)$ is a process $W=(W^1,\dots,W^J)$ with independent coordinates, each a continuous $\{\mathcal F_t\}$-martingale started at the origin with quadratic variation $[W^j]_t=t$.
--
--   It is the noise that drives every reflected Brownian motion and derivative process in the mission, and one such $W$ is fixed throughout.
--
--   **Formalization Note** The formal definition uses the equivalent description given by Lévy's characterization: $W$ is adapted, almost surely continuous, starts at $0$, and for $s\le t$ the increment $W(t)-W(s)$ is independent of $\mathcal F_s$ with law $N(0,(t-s)E_J)$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §1.4, p.4

import Mathlib
import Definitions.Def_RBMSensitivity_E
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- A `J`-dimensional `{F_t}`-Brownian motion on `(Ω, F, P)`: arXiv:1907.00472v2, §1.4, p.4.

**Formalization Note.** The paper asks for independent coordinates, each a continuous
`{F_t}`-martingale started at the origin with quadratic variation `[W^j]_t = t`. Quadratic variation
is not available at this Mathlib revision, so the definition states the equivalent form from Lévy's
characterization: adapted, a.s. continuous, started at `0` a.s., and for `s ≤ t` the increment
`W t - W s` is independent of `F_s` with law `N(0, (t - s) E_J)`. Paths are continuous almost surely
rather than for every `ω`, which under the usual conditions is the same up to indistinguishability. -/
structure IsFBrownian {J : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (W : ℝ≥0 → Ω → E J) : Prop where
  adapted : Adapted 𝓕 W
  continuous : ∀ᵐ ω ∂P, Continuous fun t => W t ω
  start : ∀ᵐ ω ∂P, W 0 ω = 0
  indep : ∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (𝓕 s) P
  law : ∀ s t : ℝ≥0, s ≤ t →
    P.map (fun ω => (W t ω - W s ω).ofLp) = Measure.pi fun _ : Fin J => gaussianReal 0 (t - s)

end RBMSensitivity


