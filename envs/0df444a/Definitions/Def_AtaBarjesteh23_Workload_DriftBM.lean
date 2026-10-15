-- Prove2me | Definitions.Def_AtaBarjesteh23_Workload_DriftBM
-- name    : AtaBarjesteh23_Workload_DriftBM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:39:48.735118+00:00
-- url     : https://prove2.me/theorems/d39cec90-ae3f-4cc1-b1d4-a90e8b0e9ae2
-- title:
--   Brownian motion with drift μ and variance σ² with respect to a filtration, started at 0
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $\mathbb F=(\mathcal F_t)_{t\in\mathbb R}$. A process $B=(B(t))_{t\ge0}$ is an **$\mathbb F$-Brownian motion with drift $\mu$ and variance $\sigma^2$, started at $0$**, if
--
--   1. $B(0)=0$;
--   2. every path $t\mapsto B(t,\omega)$ is continuous on $[0,\infty)$;
--   3. $B(t)$ is $\mathcal F_t$-measurable for every $t\ge0$;
--   4. for $0\le s\le t$ the increment $B(t)-B(s)$ is independent of $\mathcal F_s$ and has the normal law
--   $$B(t)-B(s)\sim\mathcal N\big(\mu(t-s),\ \sigma^2(t-s)\big).$$
--
--   This is the driving noise of the equivalent workload formulation of Ata and Barjesteh (§5, p. 15: "$B$ is a Brownian motion with infinitesimal drift $\mu$ and infinitesimal variance $\sigma^2$"). It is the standard notion of a Brownian motion with drift relative to the filtration to which the controls are adapted.
--
--   **Formalization Note** Time is indexed by $\mathbb R$; values at negative times play no role and are unconstrained. The start at $0$ is used by the paper's proofs ($W(0)=0$) though not printed.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 15, below (31) (the Brownian motion B of the EWF)

import Mathlib

open MeasureTheory ProbabilityTheory Set

namespace AtaBarjesteh23.Workload

/-- `B` is a Brownian motion with drift `μ` and variance `σ²` with respect to the filtration `𝔽`
under `P`, started at `0`: `B 0 = 0`, continuous paths on `[0, ∞)`, `B t` is `𝔽 t`-measurable,
and for `0 ≤ s ≤ t` the increment `B t - B s` is independent of `𝔽 s` with law
`N(μ (t - s), σ² (t - s))`. Times `t < 0` play no role. -/
def IsDriftBM {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝔽 : Filtration ℝ mΩ) (P : Measure Ω)
    (B : ℝ → Ω → ℝ) (μ σ : ℝ) : Prop :=
  (∀ ω, B 0 ω = 0) ∧ (∀ ω, ContinuousOn (fun t => B t ω) (Ici 0)) ∧
    (∀ t, 0 ≤ t → StronglyMeasurable[𝔽 t] (B t)) ∧
    ∀ s t, 0 ≤ s → s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (𝔽 s) P ∧
      P.map (fun ω => B t ω - B s ω) = gaussianReal (μ * (t - s)) (σ ^ 2 * (t - s)).toNNReal

end AtaBarjesteh23.Workload


