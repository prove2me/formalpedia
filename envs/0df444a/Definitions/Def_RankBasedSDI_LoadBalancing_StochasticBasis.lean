-- Prove2me | Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
-- name    : RankBasedSDI_LoadBalancing_StochasticBasis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:20.617248+00:00
-- url     : https://prove2.me/theorems/81d40668-e374-434f-81ed-01281481a81a
-- title:
--   Usual conditions, standard Brownian motion in dimension $d$, and $\mathbb F$-Brownian motion
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $\mathbb F=\{\mathcal F_t, t\ge 0\}$.
--
--   1. $(\Omega,\mathcal F,\mathbb F,P)$ satisfies the **usual conditions** if the filtration is right-continuous, $\mathcal F_t=\bigcap_{s>t}\mathcal F_s$ for every $t\ge0$, and $\mathcal F_0$ contains every $P$-null event of $\mathcal F$.
--   2. A process $B=(B_1,\dots,B_d)$ is a **standard Brownian motion in dimension $d$** if every sample path is continuous on $[0,\infty)$, each coordinate $B_i$ is a real Brownian motion (centred Gaussian finite-dimensional laws with $\mathrm{Cov}(B_i(s),B_i(t))=\min(s,t)$, so $B_i(0)=0$ a.s.), and the coordinate processes $B_1,\dots,B_d$ are mutually independent.
--   3. $B$ is an **$\mathbb F$-Brownian motion in dimension $d$** if, in addition, $B(t)$ is $\mathcal F_t$-measurable for every $t$ and the increment $B(t)-B(s)$ is independent of $\mathcal F_s$ for all $0\le s\le t$.
--
--   These are the stochastic-basis ingredients of a weak solution of the rank-based equations.
--
--   **Formalization Note** The filtration is a Mathlib `Filtration` indexed by $\mathbb R_{\ge0}$, while processes are maps $\Omega\to\mathbb R\to\mathbb R^d$ evaluated at $t\ge0$. Completeness is in the Karatzas–Shreve form ($\mathcal F_0$ contains the $P$-null events of $\mathcal F$), so a weak solution may live on a non-complete σ-algebra. Each coordinate uses Mathlib's `IsBrownianReal`.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 7, §2.3 (stochastic basis satisfying the usual conditions, F-Brownian motion in dimension N)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RankBasedSDI.LoadBalancing

/-!
Atar & Ichiba, arXiv:2409.15121v1, §2.3 p. 7: the stochastic basis of a weak solution.
Paths are maps `ℝ → (Fin d → ℝ)` evaluated only at times `t ≥ 0`; filtrations are indexed by
`ℝ≥0` (Mathlib's convention) and evaluated at `(t : ℝ)`.
-/

/-- **Usual conditions** for a filtered probability space `(Ω, 𝓕, 𝔽, P)`: the filtration is
right-continuous, `𝓕_t = ⋂_{s > t} 𝓕_s`, and `𝓕_0` contains every `P`-null event of `𝓕`
(Karatzas–Shreve, Def. 1.2.25). -/
def UsualConditions {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) : Prop :=
  (∀ t : ℝ≥0, F t = ⨅ (s : ℝ≥0) (_ : t < s), F s) ∧
  (∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A)

/-- **Standard Brownian motion in dimension `d`** with every sample path continuous on
`[0, ∞)`: each coordinate is a real Brownian motion (Mathlib's `IsBrownianReal`, so it starts
at `0` a.s. with Gaussian independent increments of variance `t − s`), and the `d` coordinate
processes are mutually independent. -/
def IsStandardBM {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (B : Ω → ℝ → Fin d → ℝ) : Prop :=
  (∀ ω (i : Fin d), ContinuousOn (fun t => B ω t i) (Set.Ici 0)) ∧
  (∀ i : Fin d, IsBrownianReal (fun (t : ℝ≥0) ω => B ω t i) P) ∧
  iIndepFun (fun (i : Fin d) ω (t : ℝ≥0) => B ω t i) P

/-- **`𝔽`-Brownian motion in dimension `d`**: a standard `d`-dimensional Brownian motion that is
`𝔽`-adapted and whose increments `B(t) − B(s)`, `s ≤ t`, are independent of `𝓕_s`. -/
def IsFBrownian {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) {d : ℕ} (B : Ω → ℝ → Fin d → ℝ) : Prop :=
  IsStandardBM P B ∧
  (∀ t : ℝ≥0, Measurable[F t] (fun ω => B ω t)) ∧
  (∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => B ω t - B ω s) inferInstance) (F s) P)

end RankBasedSDI.LoadBalancing


