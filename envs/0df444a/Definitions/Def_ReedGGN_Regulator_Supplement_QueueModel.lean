-- Prove2me | Definitions.Def_ReedGGN_Regulator_Supplement_QueueModel
-- name    : ReedGGN_Regulator_Supplement_QueueModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:03:32.261592+00:00
-- url     : https://prove2.me/theorems/a9329c58-b098-4a7b-b73e-2e2fef3e4cf2
-- title:
--   §2, §4 — Stochastic primitives and queue scalings
-- statement:
--   A stochastic queue family consists of FCFS sample paths, initial counts $Q_0^N$, arrivals $A^N$, an iid initial-residual sequence of law $F_0$, and an iid fresh-service sequence of fixed nonnegative law $F$. The fresh services have finite mean exactly one and are independent of initial data and arrivals. No higher moment, density, strictly positive service duration or special arrival law is required. Initial counts and arrivals may be dependent at fluid scale. The stronger four-block independence needed in §5 is a separate predicate.
--
--   The published counts define all processes, with
--
--   $$\bar Q^N=Q^N/N,\quad\bar W_0^N=W_0^N/N,\quad\bar M_2^N=M_2^N/N,\quad\tilde Q^N=(Q^N-N)/\sqrt N.$$
--
--   The initial count and arrival process have the corresponding fluid and centered diffusion scalings. The deterministic-entry service-noise sum uses positive integers $i\le Nt$ and right-continuous indicators $\mathbf1\{i/N+\eta_i>t\}$. The printed ≥ in Proposition 5.1 is corrected consistently with (2.5). Index $n$ represents $N=n+1$. Finite-horizon extensions of the published sample path append arrivals after the observation horizon, allowing finite-total-arrival processes without changing any observation. No convergence or tightness is a field of the queue model.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, §2, pp.6–7; §4, pp.10–12; (5.1), (5.8), (5.12), pp.17,19,21

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_PathLimits
import Definitions.Def_ReedGGN_Regulator_Supplement_FCFS
import Definitions.Def_ReedGGN_Regulator_FluidInput

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

/-- The service law is carried by [0,∞), integrable, of mean exactly one. No density,
 second moment, bounded support, or absence of atoms is required. -/
def ServiceLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧ Integrable id μ ∧ (∫ x, x ∂μ) = 1

/-- Initial residual laws need only be probability laws on [0,∞). -/
def ResidualLaw (μ₀ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ₀ ∧ μ₀ (Set.Iio 0) = 0

/-- Primitive stochastic FCFS family; index n means N=n+1 servers. The finite-horizon extensions allow finitely many arrivals. The two service sequences
 are fixed across N as on p.10. Fresh services are independent of the initial data and arrivals;
 the deterministic scheduling rule makes entry j depend only on earlier fresh services. Initial
 count and arrivals may be dependent (in particular no independence is added to Theorem 4.1).
 Neither LLNs nor Gaussian limits nor tightness are fields of this model. -/
structure QueueFamily (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (μ μ₀ : Measure ℝ) where
  sample : ℕ → Ω → ℕ → ReedGGN.SystemEq.SamplePath
  arrivals : ℕ → Ω → ℝ≥0 → ℕ
  arrivals_mono : ∀ n ω, Monotone (arrivals n ω)
  arrivals_cadlag : ∀ n ω, KurtzProtter91.Integrals.IsCadlag (fun t => (arrivals n ω t : ℝ))
  arrivals_measurable : ∀ n t, Measurable (fun ω => arrivals n ω t)
  horizon_agrees : ∀ n ω (H : ℕ) (t : ℝ≥0), (t : ℝ) ≤ H → (sample n ω H).A t = arrivals n ω t
  initial_agrees : ∀ n ω H, (sample n ω H).Q₀ = (sample n ω 0).Q₀
  fresh : ℕ → Ω → ℝ
  residual : ℕ → Ω → ℝ
  service_law : ServiceLaw μ
  residual_law : ResidualLaw μ₀
  size : ∀ n ω H, (sample n ω H).N = n + 1
  fresh_eq : ∀ n ω H i, (sample n ω H).η i = fresh i ω
  residual_eq : ∀ n ω H i, (sample n ω H).ηt i = residual i ω
  fcfs : ∀ n H, ∀ᵐ ω ∂P, IsFCFS (sample n ω H)
  count_measurable : ∀ n, Measurable (fun ω => (sample n ω 0).Q₀)
  arrival_measurable : ∀ n H i, Measurable (fun ω => (sample n ω H).τ i)
  wait_measurable : ∀ n H i, Measurable (fun ω => (sample n ω H).w i)
  initial_wait_measurable : ∀ n H i, Measurable (fun ω => (sample n ω H).wt i)
  fresh_measurable : ∀ i, Measurable (fresh i)
  residual_measurable : ∀ i, Measurable (residual i)
  fresh_iid : iIndepFun (fun i : ℕ => fresh (i + 1)) P
  residual_iid : iIndepFun (fun i : ℕ => residual (i + 1)) P
  fresh_dist : ∀ i, Measure.map (fresh (i + 1)) P = μ
  residual_dist : ∀ i, Measure.map (residual (i + 1)) P = μ₀
  fresh_independent : ∀ n, IndepFun (fun ω i => fresh (i + 1) ω)
    (fun ω => ((sample n ω 0).Q₀, (fun hi : ℕ × ℕ => (sample n ω hi.1).τ hi.2),
      (fun i => residual (i + 1) ω))) P

/-- H-local extensions append ghost arrivals strictly after H. Thus real-valued inverse
 arrival times in the immutable base layer do not exclude finite-total-arrival processes.
 Every observation at t uses an extension whose horizon is strictly larger than t. -/
noncomputable def localSample {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ μ₀ : Measure ℝ}
    (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) (t : ℝ≥0) : ReedGGN.SystemEq.SamplePath :=
  q.sample n ω (⌈(t : ℝ)⌉₊ + 1)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ μ₀ : Measure ℝ}

/-- Four independent primitive blocks, as invoked in the p.22 proof. Only §5 uses this.
 Blocks are initial count, full residual sequence, arrivals, full fresh sequence. -/
def PrimitiveIndependent (q : QueueFamily Ω P μ μ₀) : Prop :=
  ∀ n, iIndepFun (fun i : Fin 4 => fun ω =>
    if i = 0 then (fun _ : ℕ × ℕ => ((q.sample n ω 0).Q₀ : ℝ))
    else if i = 1 then (fun j : ℕ × ℕ => q.residual (j.2 + 1) ω)
    else if i = 2 then (fun j : ℕ × ℕ => (q.sample n ω j.1).τ j.2)
    else (fun j : ℕ × ℕ => q.fresh (j.2 + 1) ω)) P

/-- Fluid and diffusion scalings (N=n+1 throughout). -/
noncomputable def q0bar (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : ℝ :=
  ((q.sample n ω 0).Q₀ : ℝ) / (n + 1 : ℕ)
noncomputable def qbar (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => (ReedGGN.SystemEq.Q (localSample q n ω t) t : ℝ) / (n + 1 : ℕ)
noncomputable def abar (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => (q.arrivals n ω t : ℝ) / (n + 1 : ℕ)
noncomputable def wbar (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => ReedGGN.SystemEq.W0 μ₀ (localSample q n ω t) t / (n + 1 : ℕ)
noncomputable def mbar (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => ReedGGN.SystemEq.M2 μ (localSample q n ω t) t / (n + 1 : ℕ)
noncomputable def ibar (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => ReedGGN.SystemEq.I μ μ₀ (localSample q n ω t) t / (n + 1 : ℕ)
noncomputable def agbar (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => ReedGGN.SystemEq.AG μ (localSample q n ω t) t / (n + 1 : ℕ)
noncomputable def q0diff (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : ℝ :=
  (((q.sample n ω 0).Q₀ : ℝ) - (n + 1 : ℕ)) / Real.sqrt (n + 1 : ℕ)
noncomputable def qdiff (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => ((ReedGGN.SystemEq.Q (localSample q n ω t) t : ℝ) - (n + 1 : ℕ)) /
    Real.sqrt (n + 1 : ℕ)
noncomputable def wdiff (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => ReedGGN.SystemEq.W0 μ₀ (localSample q n ω t) t / Real.sqrt (n + 1 : ℕ)
noncomputable def mdiff (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => ReedGGN.SystemEq.M2 μ (localSample q n ω t) t / Real.sqrt (n + 1 : ℕ)
noncomputable def adiff (q : QueueFamily Ω P μ μ₀) (ρ : ℕ → ℝ) (n : ℕ) (ω : Ω) : RPath :=
  fun t => ((q.arrivals n ω t : ℝ) - (n + 1 : ℕ) * ρ n * t) /
    Real.sqrt (n + 1 : ℕ)

/-- Deterministic-entry service noise, with right-continuous survival indicator `>`.
 The printed ≥ at p.20 is a slip; see (2.5) and the requirement that this is in D. -/
noncomputable def mhat (q : QueueFamily Ω P μ μ₀) (n : ℕ) (ω : Ω) : RPath :=
  fun t => (∑ i ∈ Finset.Icc 1 (⌊(n + 1 : ℕ) * (t : ℝ)⌋₊),
    ((if (t : ℝ) < (i : ℝ) / (n + 1 : ℕ) + q.fresh i ω then (1 : ℝ) else 0) -
      tail μ ((t : ℝ) - (i : ℝ) / (n + 1 : ℕ)))) / Real.sqrt (n + 1 : ℕ)

end ReedGGN.Regulator.Supplement


