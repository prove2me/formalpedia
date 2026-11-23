-- Prove2me | Definitions.Def_PrescAnalytics_ERM_Supplement_Censoring
-- name    : PrescAnalytics_ERM_Supplement_Censoring
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:54:30.443949+00:00
-- url     : https://prove2.me/theorems/1b910419-7820-4dc7-a5d2-ab56015c55d6
-- title:
--   The observed censoring indicator, weighted product-limit transform and censoring assumptions
-- statement:
--   For scalar response $Y$ and threshold $V$, the observed response is $U=\min(Y,V)$ and the observable indicator is exactly $\delta=\mathbf1[U<V]$. In increasing order of observed responses, write $R_i=\sum_{\ell\ge i}w_{N,(\ell)}$. Then
--   $$a_{N,(i)}=\mathbf1[\delta_{(i)}=1]\frac{w_{N,(i)}}{R_i}\prod_{k<i:\delta_{(k)}=1}\frac{R_k-w_{N,(k)}}{R_k}.$$
--   These masses enter the published weighted objective without renormalizing residual mass. Ties are ordered by lower original index. Conditional independence is expressed under the conditional kernel; no shared atoms refers to the two marginal distributions. The strict ordering of conditional upper endpoints uses extended-real essential suprema. In particular marginal atomlessness is not replaced by conditional atomlessness or by an assumption that $Y\ne V$ almost surely.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, pp. 24–25, Eq. (24), Theorem 11

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Supplement_Prescription

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace PrescAnalytics.ERM.Supplement

/-- Scalar responses retain the published one-dimensional Euclidean carrier. -/
def scalarVector (t : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => t)

/-- Observed response U=min(Y,V), keeping exactly δ=I[U<V] as printed. -/
def observedU {dx : ℕ} (p : EuclideanSpace ℝ (Fin dx) × (EuclideanSpace ℝ (Fin 1) × ℝ)) : ℝ :=
  min (p.2.1 0) p.2.2

def observedDelta {dx : ℕ}
    (p : EuclideanSpace ℝ (Fin dx) × (EuclideanSpace ℝ (Fin 1) × ℝ)) : Prop :=
  observedU p < p.2.2

/-- Ordering u_(1)≤...≤u_(N), with lower original index first on ties. -/
noncomputable def censorRank (u : ℕ → ℝ) (N i : ℕ) : ℕ :=
  ((Finset.range N).filter (fun j => u j < u i ∨ (u j = u i ∧ j < i))).card

/-- The at-risk weight starting at observation i in the sorted order. -/
noncomputable def riskWeight (w : ℕ → ℕ → ℝ) (u : ℕ → ℝ) (N i : ℕ) : ℝ :=
  ∑ j ∈ (Finset.range N).filter (fun j => censorRank u N i ≤ censorRank u N j), w N j

/-- Product-limit transform (24), assigned back to original observation indices.
The residual product-limit mass is not renormalized; zero denominators give zero ratios. -/
noncomputable def kaplanMeierWeight (w : ℕ → ℕ → ℝ) (u : ℕ → ℝ) (δ : ℕ → Prop)
    (N i : ℕ) : ℝ := by
  classical
  exact if i < N ∧ δ i then
    (w N i / riskWeight w u N i) *
      ∏ k ∈ (Finset.range N).filter (fun k => censorRank u N k < censorRank u N i ∧ δ k),
        ((riskWeight w u N k - w N k) / riskWeight w u N k)
  else 0

noncomputable def censoredPrescription {Ω : Type*} {dx dz : ℕ}
    (m : Method) (C δ : ℝ)
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin 1) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin dx) × (EuclideanSpace ℝ (Fin 1) × ℝ))
    (N : ℕ) (ω : Ω) (x : EuclideanSpace ℝ (Fin dx)) : Set (EuclideanSpace ℝ (Fin dz)) :=
  PrescAnalytics.KNN.weightedArgmin c
    (kaplanMeierWeight (methodWeight m C δ (fun i => (S i ω).1) x)
      (fun i => observedU (S i ω)) (fun i => observedDelta (S i ω)))
    (fun i => scalarVector (observedU (S i ω))) Z N

/-- Conditional upper endpoints in EReal, not a default real supremum. -/
noncomputable def upperY {dx : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin dx) × (EuclideanSpace ℝ (Fin 1) × ℝ)))
    [IsFiniteMeasure ν] (x : EuclideanSpace ℝ (Fin dx)) : EReal :=
  essSup (fun p => (p.1 0 : EReal)) (ν.condKernel x)

noncomputable def upperV {dx : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin dx) × (EuclideanSpace ℝ (Fin 1) × ℝ)))
    [IsFiniteMeasure ν] (x : EuclideanSpace ℝ (Fin dx)) : EReal :=
  essSup (fun p => (p.2 : EReal)) (ν.condKernel x)

/-- The censoring assumptions literally printed in Theorem 11: conditional independence,
no shared marginal atoms, and strict ordering of conditional upper supports on Xs.
This deliberately does not infer P(Y=V)=0 from marginal atomlessness. -/
def CensorAssumptions {dx : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin dx) × (EuclideanSpace ℝ (Fin 1) × ℝ)))
    [IsFiniteMeasure ν] (Xs : Set (EuclideanSpace ℝ (Fin dx))) : Prop :=
  (∀ᵐ x ∂(ν.map Prod.fst), ∀ (A : Set (EuclideanSpace ℝ (Fin 1))) (B : Set ℝ),
    MeasurableSet A → MeasurableSet B →
      ν.condKernel x (A ×ˢ B) =
        ν.condKernel x (A ×ˢ Set.univ) * ν.condKernel x (Set.univ ×ˢ B)) ∧
  (∀ t : ℝ, ν {p | p.2.1 0 = t} = 0 ∨ ν {p | p.2.2 = t} = 0) ∧
  (∀ x ∈ Xs, upperY ν x < upperV ν x)

end PrescAnalytics.ERM.Supplement


