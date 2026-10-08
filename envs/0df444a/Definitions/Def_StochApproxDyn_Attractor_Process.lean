-- Prove2me | Definitions.Def_StochApproxDyn_Attractor_Process
-- name    : StochApproxDyn_Attractor_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:24:43.956341+00:00
-- url     : https://prove2.me/theorems/86874a50-92c7-458a-af26-19181714315f
-- title:
--   The standing assumption (24) of Section 7 and the set $\mathrm{Att}(X)$ of attainable points
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $(M,d)$, with $M$ carrying its Borel $\sigma$-algebra. Let $X=(X(t))_{t\ge0}$ be a stochastic process on a probability space $(\Omega,\mathcal F,P)$ with values in $M$, and let $(\mathcal F_t)_{t\ge0}$ be a filtration (a nondecreasing family of sub-$\sigma$-algebras of $\mathcal F$).
--
--   For $t\ge0$, $\delta>0$, $T>0$ let $E(t,\delta,T)$ be the event
--   $$E(t,\delta,T)=\Big\{\sup_{s\ge t}\ \sup_{0\le h\le T} d\big(X(s+h),\Phi_h(X(s))\big)\ \ge\ \delta\Big\}.$$
--   **Standing assumption of Section 7.** $X$ satisfies it with the function $w:\mathbb R_+^3\to\mathbb R_+$ if
--
--   1. every path $t\mapsto X(t)(\omega)$ is continuous;
--   2. $X$ is adapted: $X(t)$ is $\mathcal F_t$-measurable for every $t$;
--   3. for all $\delta>0$, $T>0$ and $t\ge0$, almost surely
--   $$P\big(E(t,\delta,T)\mid\mathcal F_t\big)\le w(t,\delta,T); \tag{24}$$
--   4. for all $\delta>0$, $T>0$, $t\mapsto w(t,\delta,T)$ is nonincreasing and tends to $0$ as $t\to\infty$ (the paper's $\lim_{t\to\infty}w(t,\delta,T)\downarrow0$).
--
--   A point $p\in M$ is **attainable** by $X$ if for each $t>0$ and every open neighbourhood $U$ of $p$
--   $$P(\exists s\ge t:\ X(s)\in U)>0 .$$
--   $\mathrm{Att}(X)$ denotes the set of attainable points.
--
--   Condition (24) says that, conditionally on the past, the process shadows the semiflow over every window of length $T$ after time $t$ up to an error $\delta$, except with a probability that vanishes as $t\to\infty$. It holds for the interpolated processes of most stochastic approximation algorithms.
--
--   **Formalization Note** The process is `X : ℝ≥0 → Ω → M`; the paper also allows càdlàg paths, and this formalization takes the continuous-path option only. The double supremum in $E(t,\delta,T)$ is computed in `ℝ≥0∞` with the extended distance, so the event is exactly "sup $\ge\delta$" even when the supremum is not attained or is infinite. The conditional probability is the conditional expectation `P[1_E | ℱ t]` of the indicator, and the event is **required to be measurable** for $\delta,T>0$: without it the conditional expectation would be the junk value $0$. The paper takes this measurability for granted; for separable $M$ it follows from continuity of the paths. Measurability in `adapted` is Borel measurability, `Measurable[ℱ t] (X t)`. $w$ takes values in `ℝ≥0`. The event in the attainability condition is measured by $P$ as an outer measure (it is measurable for continuous paths and open $U$).
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 30, Section 7, standing assumptions and Eq. (24); p. 31, Section 7.1 (attainable points, Att(X))

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics

open scoped NNReal ENNReal
open MeasureTheory

namespace StochApproxDyn.Attractor

/-- The event `{ω | sup_{s ≥ t} sup_{0 ≤ h ≤ T} d(X(s+h), Φ_h(X(s))) ≥ δ}` of (24) (Benaïm 1999,
p. 30), with the double supremum computed in `ℝ≥0∞` (so it may be `∞`). -/
def deviationEvent {Ω M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (t δ T : ℝ≥0) : Set Ω :=
  {ω | (δ : ℝ≥0∞) ≤ ⨆ (s : ℝ≥0) (_ : t ≤ s) (h : ℝ≥0) (_ : h ≤ T),
      edist (X (s + h) ω) (Φ h (X s ω))}

/-- The standing assumptions of Section 7 (p. 30). `X` is a continuous-time process on the
probability space `(Ω, 𝓕, P)` with continuous paths in `M`, adapted to the filtration `ℱ`, and for
all `δ > 0`, `T > 0`, `t ≥ 0`
`P(sup_{s≥t} sup_{0≤h≤T} d(X(s+h), Φ_h(X(s))) ≥ δ | ℱ_t) ≤ w(t, δ, T)`   (24)
for a function `w : ℝ₊³ → ℝ₊` with `w(t, δ, T) ↓ 0` as `t → ∞` (nonincreasing in `t`, limit `0`).
The conditional probability is the conditional expectation of the indicator of the event; that
event is required to be measurable (field `measurableSet_deviationEvent`). -/
structure SatisfiesStandingAssumption {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [MeasurableSpace M] (Φ : Flow ℝ≥0 M) (P : Measure Ω) (ℱ : Filtration ℝ≥0 m0)
    (X : ℝ≥0 → Ω → M) (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0) : Prop where
  continuous_path : ∀ ω, Continuous (fun t => X t ω)
  adapted : ∀ t, Measurable[ℱ t] (X t)
  measurableSet_deviationEvent :
    ∀ t δ T : ℝ≥0, 0 < δ → 0 < T → MeasurableSet (deviationEvent Φ X t δ T)
  condProb_le : ∀ t δ T : ℝ≥0, 0 < δ → 0 < T →
    P[(deviationEvent Φ X t δ T).indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P]
      fun _ => (w t δ T : ℝ)
  antitone_w : ∀ δ T : ℝ≥0, 0 < δ → 0 < T → Antitone (fun t => w t δ T)
  tendsto_w : ∀ δ T : ℝ≥0, 0 < δ → 0 < T →
    Filter.Tendsto (fun t => w t δ T) Filter.atTop (nhds 0)

/-- `Att(X)`, the set of points attainable by `X` (p. 31): `p` is attainable if for each `t > 0`
and every open neighbourhood `U` of `p`, `P(∃ s ≥ t : X(s) ∈ U) > 0`. -/
def attainableSet {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] (P : Measure Ω)
    (X : ℝ≥0 → Ω → M) : Set M :=
  {p | ∀ t : ℝ≥0, 0 < t → ∀ U : Set M, IsOpen U → p ∈ U →
    0 < P {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ U}}

end StochApproxDyn.Attractor


