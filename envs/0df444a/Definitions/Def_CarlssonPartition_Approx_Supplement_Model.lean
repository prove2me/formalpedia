-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Supplement_Model
-- name    : CarlssonPartition_Approx_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:24:28.491932+00:00
-- url     : https://prove2.me/theorems/7e928005-41ee-4e69-8e10-ec85fccd6eca
-- title:
--   §3 and §3.4 — joint spatial/service input model, unrestricted rate families, and physical executions
-- statement:
--   The paper-specific model consists of the published spatial instance and a measurable location-dependent service kernel $K(x,ds)$. Its standing hypotheses are the published compactness, convexity, probability-density, fleet, speed and capacity conditions, together with nonnegative pointwise finite first and second service moments. It adds no spatial moment bound.
--
--    The demand law and joint order law are constructed, rather than unrelated free distributions:
--    $$
--    \mu(dx)=\mathbf1_R(x)f(x)\,dx,\qquad H(dx,ds)=\mu(dx)K(x,ds).
--    $$
--    A model input is the general independently marked stationary renewal process with this exact joint mark law. Finite nonnegative service durations are represented by nonnegative reals; mapping $s$ to its nonnegative part changes no mass under the standing hypotheses. A family indexed by positive arrival rate requires intensity exactly $\lambda$ at each rate; the gap law may vary across rates. It is not restricted to fixed-shape rescaling or to Poisson arrivals. Requests and random physical executions reuse their general definitions.
--
--    Spatial mean service, mean radial distance, the light-traffic value and workload use nonnegative extended integrals, so infinite values remain visible:
--    $$
--    T_0=\frac{E\|X-x_0\|}{v}+E S,\qquad
--    w(\lambda)=\frac{\lambda E S}{m}+\frac{2\lambda E\|X-x_0\|}{mvq}.
--    $$
--    Heavy traffic uses the workload-from-below comap filter. A separate finite-mean domain is not part of the source standing assumptions. This integrated model does not assert a causal dispatch mechanism, an optimal policy, a performance limit, or the existence of a benchmark.
--
--   StableRate restricts policies to positive arrival rates whose extended workload is strictly below one; stableHeavy pulls the workload-from-below filter back to this subtype. Policies in overload are not required to exist.
--
--   Poisson arrivals are a separate predicate on an input family: at every rate the iid gaps are exponential with that rate, $G_\lambda=\mathrm{Exp}(\lambda)$. It is not part of the standing assumptions; only the corrected Theorems 4 and 8 assume it (the source proofs use M/G/1 queues on p. ec4 and the Poisson interarrival variance $1/\lambda^2$ on p. ec11).
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), §3 pp. 6–7 (PDF 7–8); §3.4 pp. 13–14 (PDF 14–15); proof of Theorem 4 p. ec4 (PDF 41)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_MarkedRenewal
import Definitions.Def_CarlssonPartition_Approx_Supplement_Heterogeneous
import Definitions.Def_CarlssonPartition_Approx_Supplement_Executions

noncomputable section

namespace CarlssonPartition.Approx.Supplement

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

/-- Paper-specific data extend, rather than duplicate, the published spatial instance.
No stochastic performance, queueing estimate or benchmark is a field of this structure. -/
structure Model where
  spatial : CarlssonPartition.Approx.Instance
  service : ServiceMarks CarlssonPartition.Equitable.Plane

/-- The source's spatial and pointwise service hypotheses. In particular, this does not
assume integrability of the spatial mixture of the first or second service moment. -/
def Model.Standing (M : Model) : Prop :=
  serviceStanding M.spatial M.service

/-- Homogeneous iid on-site marks have one law at every point and the source's mean.
Across-order independence is supplied by the input's iid joint mark law, not here. -/
def Model.Homogeneous (M : Model) : Prop :=
  M.service.HomogeneousOn M.spatial.R ∧
    ∀ x ∈ M.spatial.R, M.service.mean x = M.spatial.sbar

/-- Actual joint location/duration law. Nonnegative service durations are represented by
`ℝ≥0`; the truncation changes no mass under `Model.Standing`. The measurable map is
explicit so its pushforward does not silently default on a nonmeasurable function. -/
def Model.orderLaw (M : Model) :
    Measure (CarlssonPartition.Equitable.Plane × ℝ≥0) :=
  Measure.map (fun z : CarlssonPartition.Equitable.Plane × ℝ =>
    (z.1, Real.toNNReal z.2)) (M.service.jointLaw (locationLaw M.spatial))

/-- A stationary renewal input at its actual intensity, with the model's constructed
joint mark law. No cross-rate scaling or Poisson assumption is imposed. The sample space
can also carry randomization, subject to the eventual causal-policy interface. -/
structure Model.Input (M : Model) (Ω : Type*) [MeasurableSpace Ω] where
  renewal : MarkedRenewal Ω (CarlssonPartition.Equitable.Plane × ℝ≥0)
  mark_law : renewal.markLaw = M.orderLaw

/-- Requests read from the actual stationary input, with no arrival-rate rescaling. -/
def Model.Input.request {M : Model} {Ω : Type*} [MeasurableSpace Ω]
    (A : M.Input Ω) (ω : Ω) (j : ℤ) : Request CarlssonPartition.Equitable.Plane :=
  A.renewal.request ω j

/-- Physical executions reuse the general random routing object. The alias supplies
neither an execution nor a causal-policy or performance hypothesis. -/
abbrev Model.Input.Execution {M : Model} {Ω : Type*} [MeasurableSpace Ω]
    (A : M.Input Ω) :=
  CarlssonPartition.Approx.Supplement.Execution A.renewal M.spatial.m

/-- A family of source inputs indexed by positive arrival rate. The input law may vary
with the rate: fixed-shape scaling is not smuggled into the source model. -/
structure Model.InputFamily (M : Model) (Ω : Type*) [MeasurableSpace Ω] where
  input : {lam : ℝ // 0 < lam} → M.Input Ω
  intensity : ∀ lam, (input lam).renewal.palm.lam = lam.val

/-- Poisson arrivals: at every rate the iid interarrival gaps of the stationary renewal input
are exponential with that rate (`expMeasure λ`, mean `1/λ`). This is the arrival law of
Theorem 3 (Bertsimas and van Ryzin 1993b) and of the paper's own proofs (the M/G/1 queues of
p. ec4 and the interarrival variance `1/λ²` of p. ec11). It is a hypothesis only of the
corrected Theorems 4 and 8, never part of `Model.Standing`. -/
def Model.InputFamily.Poisson {M : Model} {Ω : Type*} [MeasurableSpace Ω]
    (A : M.InputFamily Ω) : Prop :=
  ∀ lam, (A.input lam).renewal.gapLaw = ProbabilityTheory.expMeasure lam.val

/-- The primary spatial mean and light-traffic value retain infinity; only homogeneous
service with its finite common mean is used in the light-traffic theorem. -/
def Model.meanService (M : Model) : ℝ≥0∞ :=
  M.service.spatialMean (locationLaw M.spatial)

def Model.radialMean (M : Model) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ‖x - M.spatial.x0‖ ∂locationLaw M.spatial

def Model.lightValue (M : Model) : ℝ≥0∞ :=
  M.radialMean / ENNReal.ofReal M.spatial.v + M.meanService

/-- The heterogeneous workload from below, including inputs with infinite spatial mean.
When the latter is infinite no positive rate is stable; no conversion to real zero occurs. -/
def Model.workload (M : Model) (lam : ℝ) : ℝ≥0∞ :=
  heterogeneousWorkload M.spatial M.service M.spatial.m lam M.spatial.R M.spatial.f

def Model.heavy (M : Model) : Filter ℝ :=
  Filter.comap M.workload (nhdsWithin 1 (Set.Iio 1))

/-- Positive, strictly subcritical rates: the source domain for stationary policies.
Requiring admissible stationary policies at every positive rate would include overload. -/
abbrev Model.StableRate (M : Model) := {lam : ℝ // 0 < lam ∧ M.workload lam < 1}

/-- Heavy traffic restricted to the stable positive-rate domain. -/
def Model.stableHeavy (M : Model) : Filter M.StableRate :=
  Filter.comap Subtype.val M.heavy

/-- The real finite-mean regime is a visible separate domain, not part of Standing. -/
def Model.FiniteMean (M : Model) : Prop :=
  finiteMeanDomain M.spatial M.service M.spatial.R M.spatial.f

end CarlssonPartition.Approx.Supplement


