-- Prove2me | Definitions.Def_RankBasedSDI_LoadBalancing_PoissonProcess
-- name    : RankBasedSDI_LoadBalancing_PoissonProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:27:48.371997+00:00
-- url     : https://prove2.me/theorems/3ebc1763-1206-4c82-8dc1-0ae8fd31a651
-- title:
--   Poisson process of intensity $\lambda\ge0$ with right-continuous paths
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\lambda\ge0$. A process $N=(N(t), t\ge0)$ is a **Poisson process of intensity $\lambda$** if:
--
--   1. every sample path satisfies $N(0)=0$, takes values in $\{0,1,2,\dots\}$, and is nondecreasing and right-continuous on $[0,\infty)$;
--   2. $N$ has independent increments: for $0\le t_0\le t_1\le\dots\le t_k$ the increments $N(t_{j})-N(t_{j-1})$ are independent;
--   3. for $0\le s\le t$ the increment $N(t)-N(s)$ is Poisson with mean $\lambda(t-s)$, i.e.
--
--   $$
--   P\big(N(t)-N(s)=k\big)=e^{-\lambda(t-s)}\frac{(\lambda(t-s))^k}{k!},\qquad k=0,1,2,\dots
--   $$
--
--   The exogenous arrival streams $E^n_i$ and the load-balancing stream $A^n_0$ of the model are Poisson processes in this sense.
--
--   **Formalization Note** Time is real and only $t\ge0$ is used. The increment law is Mathlib's `poissonMeasure` pushed to $\mathbb R$. The intensity is in $\mathbb R_{\ge0}$, and intensity $0$ gives the point mass at $0$. Independent increments are Mathlib's `HasIndepIncrements`, applied to the process restricted to $\mathbb R_{\ge0}$.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 3, §2.1 (mutually independent Poisson processes with right-continuous sample paths)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RankBasedSDI.LoadBalancing

/-- A **Poisson process of intensity `rate ≥ 0`** on `(Ω, P)` (Atar & Ichiba,
arXiv:2409.15121v1, §2.1 p. 3: "mutually independent Poisson processes of intensities … assumed
to have right-continuous sample paths"). Every sample path starts at `0`, takes values in `ℕ`, is
nondecreasing and right-continuous on `[0, ∞)`; the increments over disjoint intervals are
independent; and `N(t) − N(s)` has the Poisson law of mean `rate · (t − s)` for `0 ≤ s ≤ t`
(`poissonMeasure 0` is the point mass at `0`, so `rate = 0` needs no special case). Time is real and
only `t ≥ 0` is used. -/
def IsPoissonProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (rate : ℝ≥0)
    (Np : Ω → ℝ → ℝ) : Prop :=
  (∀ ω, Np ω 0 = 0) ∧
  (∀ ω (t : ℝ), 0 ≤ t → ∃ k : ℕ, Np ω t = k) ∧
  (∀ ω, MonotoneOn (Np ω) (Set.Ici 0)) ∧
  (∀ ω (t : ℝ), 0 ≤ t → ContinuousWithinAt (Np ω) (Set.Ici t) t) ∧
  HasIndepIncrements (fun (t : ℝ≥0) ω => Np ω t) P ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t →
    HasLaw (fun ω => Np ω t - Np ω s)
      ((poissonMeasure (rate * Real.toNNReal (t - s))).map (fun k : ℕ => (k : ℝ))) P)

end RankBasedSDI.LoadBalancing


