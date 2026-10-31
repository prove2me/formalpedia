-- Prove2me | Definitions.Def_KeskinLiSong_DDPO_StatisticalObjects
-- name    : KeskinLiSong_DDPO_StatisticalObjects
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:43:05.929473+00:00
-- url     : https://prove2.me/theorems/fb5fab6f-eb7a-4441-8dbf-1b3ae18ec288
-- title:
--   Statistical objects and measurable history policies
-- statement:
--   Reusable Euclidean vectors, genuine maximizers and metric projections, exponential families on a specified reference measure, local moment-generating-function laws, independent finite samples, and measurable policies on finite observation-action histories. The full natural parameter domain is characterized by a finite positive normalizing integral. The parameter set is compact and need not be convex; no identifiability or Fisher-information assumption is imposed. The local MGF condition includes integrability, centering, the second-moment bound, and all three positive constants.
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), pp. 8–11 and 22

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace KeskinLiSong.DDPO

/-- Euclidean parameter vectors, including the two demand and beta parameters. -/
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A genuine optimizer; an empty feasible set has no optimizer. -/
def Maximizes {α : Type*} (S : Set α) (f : α → ℝ) (a : α) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, f b ≤ f a

/-- Euclidean projection as a relation, with all ties retained. -/
def Projects {d : ℕ} (S : Set (Vector d)) (x y : Vector d) : Prop :=
  y ∈ S ∧ ∀ z ∈ S, dist x y ≤ dist x z

/-- Exponential family with a specified dominating measure; no minimality or
identifiability condition is imposed. The natural domain and compact parameter
set are distinct: maximum likelihood is unconstrained before projection. -/
structure ExponentialFamily (d : ℕ) where
  baseMeasure : Measure ℝ
  base : ℝ → ℝ
  statistic : ℝ → Vector d
  logPartition : Vector d → ℝ
  naturalDomain : Set (Vector d)
  naturalDomain_exact : ∀ v, v ∈ naturalDomain ↔
    (∫⁻ z, ENNReal.ofReal (base z * Real.exp (inner ℝ v (statistic z))) ∂baseMeasure) ≠ 0 ∧
    (∫⁻ z, ENNReal.ofReal (base z * Real.exp (inner ℝ v (statistic z))) ∂baseMeasure) ≠ ∞
  parameterSet : Set (Vector d)
  compact_parameters : IsCompact parameterSet
  parameters_nonempty : parameterSet.Nonempty
  parameters_natural : parameterSet ⊆ naturalDomain
  base_nonnegative : ∀ z, 0 ≤ base z
  density_measurable : ∀ v ∈ naturalDomain,
    Measurable (fun z => base z * Real.exp (inner ℝ v (statistic z) - logPartition v))
  normalized : ∀ v ∈ naturalDomain,
    ∫⁻ z, ENNReal.ofReal (base z * Real.exp (inner ℝ v (statistic z) - logPartition v))
      ∂baseMeasure = 1

def ExponentialFamily.density {d : ℕ} (F : ExponentialFamily d)
    (v : Vector d) (z : ℝ) : ℝ :=
  F.base z * Real.exp (inner ℝ v (F.statistic z) - F.logPartition v)

def ExponentialFamily.law {d : ℕ} (F : ExponentialFamily d)
    (v : Vector d) : Measure ℝ :=
  F.baseMeasure.withDensity (fun z => ENNReal.ofReal (F.density v z))

def ExponentialFamily.likelihood {d : ℕ} (F : ExponentialFamily d)
    (sample : List ℝ) (v : Vector d) : ℝ :=
  (sample.map (F.density v)).prod

def ExponentialFamily.ProjectedMLE {d : ℕ} (F : ExponentialFamily d)
    (sample : List ℝ) (estimate : Vector d) : Prop :=
  ∃ raw, Maximizes F.naturalDomain (F.likelihood sample) raw ∧
    Projects F.parameterSet raw estimate

/-- The local MGF condition includes integrability, so a total Bochner integral
cannot turn a divergent moment generating function into zero. -/
structure LocalMGF where
  law : Measure ℝ
  probability : IsProbabilityMeasure law
  sigma : ℝ
  rho : ℝ
  radius : ℝ
  sigma_pos : 0 < sigma
  rho_pos : 0 < rho
  radius_pos : 0 < radius
  first_integrable : Integrable (fun e : ℝ => e) law
  centered : ∫ e, e ∂law = 0
  second_integrable : Integrable (fun e : ℝ => e ^ 2) law
  variance_bound : ∫ e, e ^ 2 ∂law ≤ sigma ^ 2
  exponential_integrable : ∀ a : ℝ, |a| ≤ radius →
    Integrable (fun e => Real.exp (a * e)) law
  exponential_bound : ∀ a : ℝ, |a| ≤ radius →
    ∫ e, Real.exp (a * e) ∂law ≤ Real.exp (rho * sigma ^ 2 * a ^ 2 / 2)

/-- Finite-dimensional product sampling, with genuine independent coordinates. -/
def iidLaw (μ : Measure ℝ) (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ => μ)

/-- Deterministic measurable policies on finite observation-action histories.
This reusable information pattern does not reveal unknown parameters. -/
structure HistoryPolicy (O A : Type*) [MeasurableSpace O] [MeasurableSpace A] where
  action : (k : ℕ) → (Fin k → O × A) → A
  measurable_action : ∀ k, Measurable (action k)

end KeskinLiSong.DDPO


