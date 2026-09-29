-- Prove2me | Definitions.Def_NetworkControl_CapacityRegion_AdmissibleArrival
-- name    : NetworkControl_CapacityRegion_AdmissibleArrival
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:19:17.168985+00:00
-- url     : https://prove2.me/theorems/8264a58d-17a2-4f51-8f94-be2c80ec2008
-- title:
--   Definition 3.4 — admissible arrival process
-- statement:
--   An arrival process $A:\mathbb N\to\Omega\to\mathbb R$ on a filtered probability space
--   $(\Omega,P,\mathcal F)$ is *admissible with rate $\lambda$* (Def. 3.4, p. 25) if:
--   (i) its time-average expected rate converges to $\lambda$;
--   (ii) there is a finite $A_{\max}$ with $\mathbb E\{A(t)^2\mid\mathcal H(t)\}\le A_{\max}^2$
--   for every $t$, where $\mathcal H(t)$ is the history of slots $0,\dots,t-1$ (modeled here as
--   the filtration value $\mathcal F(t)$);
--   (iii) for every $\delta>0$ there is a window $T$ such that, from every initial time $t_0$,
--   $\mathbb E\{\frac1T\sum_{k=0}^{T-1}A(t_0+k)\mid\mathcal H(t_0)\}\le\lambda+\delta$ almost
--   everywhere.
--
--   **Formalization note.** Explicit `Integrable` guards are attached to the plain expectation in
--   (i) and to `A(t)^2` in (ii): Mathlib's Bochner integral and `condExp` both default to `0` for
--   a non-integrable function, which would otherwise let a process with an undefined or infinite
--   second moment satisfy (ii) vacuously (Faithfulness trap 2) — the book assumes these moments
--   are genuinely finite, it does not derive their finiteness.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, pp. 25-26, Definition 3.4 and Eq. (3.2)

import Mathlib

namespace NetworkControl.CapacityRegion

open MeasureTheory

/-- Definition 3.4 (p. 25), restated as a structure. An arrival process `A : ℕ → Ω → ℝ` on a
filtered probability space `(Ω, P, 𝓕)` is admissible with rate `lam` if: (i) its time-average
expected rate converges to `lam`; (ii) its second moment given the history `𝓕 t` (`H(t)`, the
events of slots `0,…,t-1`, per the book's own description) is uniformly bounded by some finite
`Amax^2`; (iii) for every `δ > 0` there is an averaging window `T` such that, from any initial
time `t0`, the `T`-slot conditional average exceeds `lam` by no more than `δ`, a.e. -/
structure AdmissibleArrival {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℕ mΩ) (A : ℕ → Ω → ℝ) (lam : ℝ) : Prop where
  integrable :
    ∀ t : ℕ, Integrable (A t) P
  time_average :
    Filter.Tendsto (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, A τ ω ∂P)
      Filter.atTop (nhds lam)
  second_moment_bound :
    ∃ Amax : ℝ, ∀ t : ℕ, Integrable (fun ω => (A t ω) ^ 2) P ∧
      (P[(fun ω => (A t ω) ^ 2) | 𝓕 t]) ≤ᵐ[P] (fun _ => Amax ^ 2)
  averaging_bound :
    ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, 0 < T ∧ ∀ t0 : ℕ,
      (P[(fun ω => (1 / (T : ℝ)) * ∑ k ∈ Finset.range T, A (t0 + k) ω) | 𝓕 t0])
        ≤ᵐ[P] (fun _ => lam + δ)

end NetworkControl.CapacityRegion


