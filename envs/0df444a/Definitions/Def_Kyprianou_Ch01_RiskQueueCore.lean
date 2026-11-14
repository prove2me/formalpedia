-- Prove2me | Definitions.Def_Kyprianou_Ch01_RiskQueueCore
-- name    : Kyprianou_Ch01_RiskQueueCore
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T00:11:47.049108+00:00
-- url     : https://prove2.me/theorems/aa464022-2263-4f17-91f1-3df957bdc560
-- title:
--   Chapter 1 insurance and M/G/1 queue model, ruin, integrated-tail law and idle time
-- statement:
--   Nontrivial path and distribution interfaces matching Kyprianou (2006), Chapter 1 §§1.3.1–1.3.2. No theorem conclusions are assumed or installed as axioms. Ruin is strict (<0); time, exponential moments, and idle time are represented with appropriate domains; nonlattice restriction is explicit. Lean elaboration remains to be verified.
-- source:
--   Kyprianou (2006), Chapter 1 pp. 16–21, (1.11)–(1.13) and Theorems 1.8–1.12.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_QueueingFundamentals_MG1_transforms

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

set_option autoImplicit false
namespace Kyprianou.Ch01

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Aggregate claims up to time t from a driftless compound-Poisson driver. -/
noncomputable def aggregateClaims
    (arrival claims : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ProbabilityTheory.compoundPoisson 0 arrival claims (t : ℝ) ω

/-- Cramér–Lundberg insurance surplus starting at capital x. -/
noncomputable def riskSurplus
    (arrival claims : ℕ → Ω → ℝ) (premium x : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  x + premium * (t : ℝ) - aggregateClaims arrival claims t ω

/-- Ultimate strict ruin, which is distinct from hitting the boundary 0. -/
def ruinEvent
    (arrival claims : ℕ → Ω → ℝ) (premium x : ℝ) : Set Ω :=
  {ω | ∃ t : ℝ≥0, 0 < t ∧ riskSurplus arrival claims premium x t ω < 0}

/-- The first strict-ruin time on paths where ruin occurs. Outside the ruin
    event its value is deliberately unused. -/
noncomputable def ruinTime
    (arrival claims : ℕ → Ω → ℝ) (premium x : ℝ) (ω : Ω) : ℝ≥0 :=
  sInf {t : ℝ≥0 | 0 < t ∧ riskSurplus arrival claims premium x t ω < 0}

/-- Nonnegative claim deficit at the strict first-passage epoch on ruin paths. -/
noncomputable def ruinDeficit
    (arrival claims : ℕ → Ω → ℝ) (premium x : ℝ) (ω : Ω) : ℝ :=
  -(riskSurplus arrival claims premium x
      (ruinTime arrival claims premium x ω) ω)

/-- Ultimate ruin probability from starting capital x. -/
noncomputable def ruinProbability
    (P : Measure Ω) (arrival claims : ℕ → Ω → ℝ)
    (premium x : ℝ) : ℝ :=
  (P (ruinEvent arrival claims premium x)).toReal

/-- Integrated-tail distribution function for positive claims of mean mu.
    Outside the positive half-line the interval integral is zero. -/
noncomputable def integratedTailCDF
    (F : Measure ℝ) (mu x : ℝ) : ℝ :=
  (1 / mu) * ∫ y in Set.Ioc (0 : ℝ) x,
    (F (Set.Ioi y)).toReal ∂volume

/-- Distributional Pollaczek–Khintchine convolution series. -/
noncomputable def pkCDF
    (eta : Measure ℝ) (rho x : ℝ) : ℝ :=
  (1 - rho) * ∑' k : ℕ,
    rho ^ k * ((QueueingFundamentals.MG1.convPow eta k)
      (Set.Iic x)).toReal

/-- M/G/1 workload as the reflected risk process, with initial workload w. -/
noncomputable def queueWorkload
    (arrival claims : ℕ → Ω → ℝ) (w : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  max w (sSup {z : ℝ | ∃ s : ℝ≥0,
    s ≤ t ∧ z = riskSurplus arrival claims 1 0 s ω}) -
      riskSurplus arrival claims 1 0 t ω

/-- Total idle time in extended nonnegative reals, allowing infinite idle time. -/
noncomputable def totalIdleTime
    (arrival claims : ℕ → Ω → ℝ) (w : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ici (0 : ℝ),
    if queueWorkload arrival claims w (Real.toNNReal t) ω = 0
      then (1 : ℝ≥0∞) else 0 ∂volume

/-- Laplace exponent of the unit-premium spectrally negative compound Poisson process. -/
noncomputable def queueLaplaceExponent
    (rate : ℝ≥0) (F : Measure ℝ) (θ : ℝ) : ℝ :=
  θ - (rate : ℝ) * (∫ x, (1 - Real.exp (-θ * x)) ∂F)

/-- Explicit nonlattice condition on a service/claim-size distribution. -/
def IsNonLattice (F : Measure ℝ) : Prop :=
  ∀ (a h : ℝ), 0 < h →
    F {x : ℝ | ∃ n : ℤ, x = a + h * (n : ℝ)} ≠ 1

end Kyprianou.Ch01


