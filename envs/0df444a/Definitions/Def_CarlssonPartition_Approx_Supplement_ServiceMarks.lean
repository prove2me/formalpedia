-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Supplement_ServiceMarks
-- name    : CarlssonPartition_Approx_Supplement_ServiceMarks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:19:51.708003+00:00
-- url     : https://prove2.me/theorems/98ea4407-7040-4793-ad7f-0f16b829fa05
-- title:
--   §3.4 — conditional service laws, pointwise moments, and possibly infinite spatial mixtures
-- statement:
--   Let $K(x,ds)$ be a measurable probability kernel for on-site duration at location $x$. On the service region $R$, durations are nonnegative and both first and second moments are finite at every location. Define
--    $$
--    \bar s(x)=\int s\,K(x,ds),\qquad
--    \sigma_s^2(x)=\int(s-\bar s(x))^2\,K(x,ds).
--    $$
--    For a location law $\mu$, the joint location/service law is $\mu(dx)K(x,ds)$. Its spatial first and second moments are nonnegative extended integrals
--    $$
--    \int\!\int s\,K(x,ds)\mu(dx),\qquad
--    \int\!\int s^2\,K(x,ds)\mu(dx).
--    $$
--    They may be infinite despite pointwise finite moments. Homogeneity means that the same conditional service law applies at every location in $R$. Independence between different orders belongs to the joint iid mark law in the renewal layer. This definition does not add independence of service from location or an aggregate moment bound.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), §3.4, pp. 13–14 (PDF 14–15)

import Mathlib

noncomputable section

namespace CarlssonPartition.Approx.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A measurable location-dependent distribution of on-site service durations.
`FiniteOn` records exactly the source's pointwise moment assumptions on the region;
it does not impose a uniform bound or finiteness of the spatially mixed second moment. -/
structure ServiceMarks (V : Type*) [MeasurableSpace V] where
  law : Kernel V ℝ
  probability : IsMarkovKernel law

/-- Source §3.4: nonnegative service, finite mean and variance at every location in `R`.
Square integrability is the finite-second-moment reading of finite mean and variance. -/
def ServiceMarks.FiniteOn {V : Type*} [MeasurableSpace V]
    (S : ServiceMarks V) (R : Set V) : Prop :=
  ∀ x ∈ R, S.law x (Set.Ici 0) = 1 ∧
    Integrable (fun s : ℝ => s) (S.law x) ∧
    Integrable (fun s : ℝ => s ^ 2) (S.law x)

/-- The location-dependent mean. It is used as a real expectation only on `FiniteOn`. -/
def ServiceMarks.mean {V : Type*} [MeasurableSpace V]
    (S : ServiceMarks V) (x : V) : ℝ :=
  ∫ s : ℝ, s ∂S.law x

/-- The location-dependent variance, used only where `FiniteOn` holds. -/
def ServiceMarks.variance {V : Type*} [MeasurableSpace V]
    (S : ServiceMarks V) (x : V) : ℝ :=
  ∫ s : ℝ, (s - S.mean x) ^ 2 ∂S.law x

/-- The actual spatial mixture of location and service. Markovness is supplied locally
so composition-product cannot fall back to its value on a non-s-finite kernel. -/
def ServiceMarks.jointLaw {V : Type*} [MeasurableSpace V]
    (S : ServiceMarks V) (locationLaw : Measure V) : Measure (V × ℝ) :=
  letI := S.probability
  locationLaw ⊗ₘ S.law

/-- Nonnegative spatially averaged service time. Unlike a Bochner integral, this retains
`⊤` when pointwise finite service means have a nonintegrable spatial average. -/
def ServiceMarks.spatialMean {V : Type*} [MeasurableSpace V]
    (S : ServiceMarks V) (locationLaw : Measure V) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ s : ℝ, ENNReal.ofReal s ∂S.law x ∂locationLaw

/-- The second moment of the spatial mixture. It is not assumed finite by `FiniteOn`. -/
def ServiceMarks.spatialSecond {V : Type*} [MeasurableSpace V]
    (S : ServiceMarks V) (locationLaw : Measure V) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ s : ℝ, ENNReal.ofReal (s ^ 2) ∂S.law x ∂locationLaw

/-- Homogeneous service is the specialization in which all locations in the region
have the same probability law; heterogeneous laws are not identified with this case. -/
def ServiceMarks.HomogeneousOn {V : Type*} [MeasurableSpace V]
    (S : ServiceMarks V) (R : Set V) : Prop :=
  ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ x ∈ R, S.law x = ν

end CarlssonPartition.Approx.Supplement


