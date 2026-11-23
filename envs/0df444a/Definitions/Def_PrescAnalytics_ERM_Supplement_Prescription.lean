-- Prove2me | Definitions.Def_PrescAnalytics_ERM_Supplement_Prescription
-- name    : PrescAnalytics_ERM_Supplement_Prescription
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:53:30.2935+00:00
-- url     : https://prove2.me/theorems/c655cb9e-0b11-4401-9a4f-64ce498b51d1
-- title:
--   Dispatch of the five weights to the published prescription and limiting predicates
-- statement:
--   Each of the five source weight constructions is used in the same published objective:
--   $$\widehat{\mathcal Z}_N(x)=\arg\min_{z\in\mathcal Z}\sum_{i=1}^N w_{N,i}(x)c(z;y^i).$$
--   The combined predicate is precisely asymptotic optimality and consistency from the published definition: almost surely in the data path, then almost everywhere in $x$, the full-information optimizer exists, the empirical argmin is eventually nonempty, and every eventual selection has both asserted limits. Neither bounded decision sets nor a preselected optimizer is built into this interface.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, pp. 3, 10–11, 18, Eq. (3), Definition 1

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Supplement_Recursive
import Definitions.Def_PrescAnalytics_ERM_Supplement_LocalLinear

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace PrescAnalytics.ERM.Supplement

/-- The five constructions (12)–(16). All share the published weighted objective and argmin. -/
inductive Method where
  | knn | kernel (K : KernelKind) | recursive | local (K : KernelKind) | nonnegative (K : KernelKind)

noncomputable def methodWeight {dx : ℕ} (m : Method) (C δ : ℝ)
    (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx)) : ℕ → ℕ → ℝ :=
  match m with
  | .knn => PrescAnalytics.KNN.knnWeight C δ xs x
  | .kernel K => kernelWeight K C δ xs x
  | .recursive => recursiveWeight C δ xs x
  | .local K => localWeight false K C δ xs x
  | .nonnegative K => localWeight true K C δ xs x

noncomputable def prescription {Ω : Type*} {dx dy dz : ℕ} (m : Method) (C δ : ℝ)
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))
    (N : ℕ) (ω : Ω) (x : EuclideanSpace ℝ (Fin dx)) : Set (EuclideanSpace ℝ (Fin dz)) :=
  PrescAnalytics.KNN.weightedArgmin c (methodWeight m C δ (fun i => (S i ω).1) x)
    (fun i => (S i ω).2) Z N

/-- Exactly the conjunction of the two published predicates, with eventual attainment included. -/
def OptimalAndConsistent {Ω : Type*} [MeasurableSpace Ω] {dx dy dz : ℕ}
    (P : Measure Ω)
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsFiniteMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (rule : ℕ → Ω → EuclideanSpace ℝ (Fin dx) → Set (EuclideanSpace ℝ (Fin dz))) : Prop :=
  PrescAnalytics.KNN.IsAsymptoticallyOptimal P μ c Z rule ∧
    PrescAnalytics.KNN.IsConsistent P μ c Z rule

end PrescAnalytics.ERM.Supplement


