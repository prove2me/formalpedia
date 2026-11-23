-- Prove2me | Definitions.Def_NHPPArrivals_LinearRate_Supplement_ConditionalSample
-- name    : NHPPArrivals_LinearRate_Supplement_ConditionalSample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:06:19.196807+00:00
-- url     : https://prove2.me/theorems/d3c5829e-f294-4e55-8a00-76343ac3997b
-- title:
--   Standing rate assumptions, scaled one-arrival density and full conditional vector law (5)
-- statement:
--   Fix $T>0$. An admissible rate is nonnegative and integrable on $[0,T]$ and has only finitely many zeros there. Let $\Lambda(t)=\int_0^t\lambda(s)\,ds$ and use the published one-arrival law with density $\lambda/\Lambda(T)$ on $[0,T]$. Its pushforward under $s\mapsto s/T$ is denoted $\mu_{\lambda,T}$. Define
--   $$f(t)=\frac{T\lambda(tT)}{\Lambda(T)}\quad(0\le t\le1),\qquad f(t)=0\quad(t\notin[0,1]).$$
--   The order-statistic law of $n$ independent draws from a measure $\mu$ is the pushforward of $\mu^{\otimes n}$ by sorting the whole vector. The conditional vector law is the pushforward of $P(\cdot\mid N(T)=n)$ by $(X_1/T,\ldots,X_n/T)$, with conditioning defined by restriction and division by the event probability. This definition supplies no order-statistic identification; Theorem 1 must prove it and positivity of every conditioning event, including $n=0$.
--   These objects connect the published deterministic cdf to the NHPP model. Values of the rate outside $[0,T]$ do not matter. No continuity or positive lower bound is required.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, DOI 10.1287/msom.2014.0490, p. 471, §3.2, (4)–(5), THEOREM 1

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf
import Definitions.Def_NHPPArrivals_LinearRate_Supplement_PoissonProcess

namespace NHPPArrivals.LinearRate.Supplement

open MeasureTheory ProbabilityTheory

/-- The standing rate assumptions of §3.2, without continuity or boundedness. -/
def AdmissibleRate (lam : ℝ → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ IntervalIntegrable lam volume 0 T ∧
  (∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ lam s) ∧
  {s ∈ Set.Icc (0 : ℝ) T | lam s = 0}.Finite

noncomputable def scaledArrivalLaw (lam : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  (arrivalLaw lam T).map (fun s => s / T)

/-- Formula (5) on [0,1], extended by zero outside. -/
noncomputable def condDensity (lam : ℝ → ℝ) (T t : ℝ) : ℝ :=
  if t ∈ Set.Icc (0 : ℝ) 1 then T * lam (t * T) / cumRate lam T else 0

noncomputable def orderedLaw (μ : Measure ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  (Measure.pi (fun _ : Fin n => μ)).map (fun x => x ∘ Tuple.sort x)

/-- The full vector law conditioned on the actual count, including n=0. -/
noncomputable def conditionalVectorLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℝ → Ω → ℕ) (X : ℕ → Ω → ℝ) (T : ℝ) (n : ℕ) :
    Measure (Fin n → ℝ) :=
  ((P {ω | N T ω = n})⁻¹ • P.restrict {ω | N T ω = n}).map
    (fun ω i => X (i : ℕ) ω / T)

end NHPPArrivals.LinearRate.Supplement


