-- Prove2me | Definitions.Def_NetworkControl_CapacityRegion_AdmissibleService
-- name    : NetworkControl_CapacityRegion_AdmissibleService
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:19:29.936979+00:00
-- url     : https://prove2.me/theorems/103e8229-c4d5-48fc-8c5a-fe89e89670e1
-- title:
--   Definition 3.5 — admissible service process
-- statement:
--   A server (transmission-rate) process $\mathrm{svc}:\mathbb N\to\Omega\to\mathbb R$ is
--   *admissible with time-average rate $\mu$* (Def. 3.5, p. 26) if:
--   (i) its time-average expected rate converges to $\mu$;
--   (ii) there is a finite $\mu_{\max}$ with $\mathrm{svc}(t)\le\mu_{\max}$ pointwise, for every
--   $t$ (the book's bound is stated outright, not merely in expectation);
--   (iii) for every $\delta>0$ there is a window $T$ such that, from every initial time $t_0$,
--   $\mathbb E\{\frac1T\sum_{k=0}^{T-1}\mathrm{svc}(t_0+k)\mid\mathcal H(t_0)\}\ge\mu-\delta$
--   almost everywhere.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 26, Definition 3.5 and Eq. (3.3)

import Mathlib

namespace NetworkControl.CapacityRegion

open MeasureTheory

/-- Definition 3.5 (p. 26), restated as a structure, mirroring `AdmissibleArrival`. A server
process `svc : ℕ → Ω → ℝ` is admissible with time-average rate `rate` if: (i) its time-average
expected rate converges to `rate`; (ii) it is uniformly bounded above by some finite `svcMax`
(the book's `μmax`, pointwise, not merely in expectation); (iii) for every `δ > 0` there is a
window `T` such that, from any initial time `t0`, the `T`-slot conditional average is at least
`rate - δ`, a.e. -/
structure AdmissibleService {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℕ mΩ) (svc : ℕ → Ω → ℝ) (rate : ℝ) : Prop where
  integrable :
    ∀ t : ℕ, Integrable (svc t) P
  time_average :
    Filter.Tendsto (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, svc τ ω ∂P)
      Filter.atTop (nhds rate)
  upper_bound :
    ∃ svcMax : ℝ, ∀ t : ℕ, ∀ ω : Ω, svc t ω ≤ svcMax
  averaging_bound :
    ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, 0 < T ∧ ∀ t0 : ℕ,
      (fun _ : Ω => rate - δ)
        ≤ᵐ[P] (P[(fun ω => (1 / (T : ℝ)) * ∑ k ∈ Finset.range T, svc (t0 + k) ω) | 𝓕 t0])

end NetworkControl.CapacityRegion


