-- Prove2me | Definitions.Def_XuZeevi_Variance_Sampling
-- name    : XuZeevi_Variance_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:06:52.391064+00:00
-- url     : https://prove2.me/theorems/4b77972e-04b8-4e51-93d2-bd3254ae7292
-- title:
--   Sampling, empirical means, central moments and probability events
-- statement:
--   For a probability measure $P$ on an arbitrary measurable space $Z$, `sampleLaw` is $P^{\otimes n}$ on $Z^n$ and `splitLaw` is its product with an independent copy. The sample index is $\{0,\ldots,n-1\}$. The empirical mean of $f$ is the published empirical risk for a singleton index, $P_nf=n^{-1}\sum_i f(z_i)$. The variance is the central second moment $\int(f-Pf)^2\,dP$.
--
--   A property holds with probability at least $p$ when it holds throughout some measurable event of measure at least $\max(p,0)$. For a measurable property this is precisely its usual probability inequality, including a vacuous negative lower bound. This definition prevents an outer-measure bound on a nonmeasurable good set from masquerading as a probability guarantee. Later statements explicitly carry the paper's exact-event measurability convention where necessary. Neither a topology nor a sigma algebra on the hypothesis class is required.
--
--   These are constructions, not concentration assumptions. Theorems require $n>0$ and integrability through bounded measurable losses or finite moments; outside those domains Lean's empirical mean at $n=0$ and nonintegrable Bochner integral are zero.
-- source:
--   Xu and Zeevi, arXiv:2011.06186v4, §1.1 p. 3, §2.2 p. 5 footnote 1, §3.1 p. 8, Strategy 1 p. 11 (PDF pages equal printed pages)

import Definitions.Def_NatureSLT_Consistency_risk

open MeasureTheory

namespace XuZeevi.Variance

/-- Product law of the primary sample, §1.1 and Strategy 1. -/
noncomputable def sampleLaw {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) (n : ℕ) : Measure (Fin n → Z) :=
  Measure.pi (fun _ : Fin n => P)

/-- The independent primary/auxiliary split of 2n observations. -/
noncomputable def splitLaw {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) (n : ℕ) : Measure ((Fin n → Z) × (Fin n → Z)) :=
  (sampleLaw P n).prod (sampleLaw P n)

/-- Empirical mean, using the published empirical-risk definition with one index. -/
noncomputable def empiricalMean {Z : Type*} {n : ℕ} (s : Fin n → Z)
    (f : Z → ℝ) : ℝ :=
  NatureSLT.Consistency.empiricalRisk (fun _ : Unit => f) s ()

/-- Central second moment. Used only for measurable bounded losses or integrable moments. -/
noncomputable def variance {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) (f : Z → ℝ) : ℝ :=
  ∫ z, (f z - ∫ x, f x ∂P) ^ 2 ∂P

/-- A property holds on a measurable event of probability at least p.
For measurable properties this is exactly the usual probability inequality;
no outer-measure convention or measurable structure on the hypothesis class is imposed. -/
def HighProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p : ℝ) (A : Ω → Prop) : Prop :=
  ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal p ≤ P E ∧ ∀ ω ∈ E, A ω

end XuZeevi.Variance


