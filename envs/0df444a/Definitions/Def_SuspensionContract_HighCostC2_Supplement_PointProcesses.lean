-- Prove2me | Definitions.Def_SuspensionContract_HighCostC2_Supplement_PointProcesses
-- name    : SuspensionContract_HighCostC2_Supplement_PointProcesses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:58:06.888801+00:00
-- url     : https://prove2.me/theorems/0b4a9aaf-b0d6-4f94-883b-efb7d6a7b305
-- title:
--   Simple counting processes, predictable intensity and discounted Stieltjes integrals
-- statement:
--   Time runs over the entire nonnegative half-line. A simple event stream is a locally finite sequence of event times in $[0,\infty]$, with infinity indicating an absent event. Its counting measure places a unit atom at each finite event time. The cumulative count and pre-event count are the masses of $[0,t]$ and $[0,t)$.
--
--   For a probability law $P$, public filtration $\mathcal F$, counting measure $dN$, and predictable nonnegative rate $\lambda$, the intensity condition is the predictable compensation identity
--   $$E_P\!\left[\int Z_t\,dN_t\right]=E_P\!\left[\int Z_t\lambda_t\,dt\right]$$
--   for every nonnegative predictable test process $Z$. Discounted integrals use the actual event or payment measure and retain infinite values. This is the general counting-process layer used by the contract model; it imposes no stationarity, finite event horizon, or utility identities.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, §2 pp. 8–10, public counting processes and (2)–(4)

import Mathlib

namespace SuspensionContract.HighCostC2.Supplement

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

/-- Time is the whole half-line; this is Lebesgue measure, not counting measure. -/
noncomputable def timeMeasure : Measure ℝ≥0 :=
  Measure.comap ((↑) : ℝ≥0 → ℝ) volume

/-- A possibly finite sequence of simple event times. Infinity records absent events. -/
structure EventStream (Ω : Type*) where
  time : ℕ → Ω → WithTop ℝ≥0
  ordered : ∀ ω i j, i < j → time i ω < time j ω ∨ time i ω = ⊤
  locallyFinite : ∀ (ω : Ω) (T : ℝ≥0), {n | time n ω ≤ (T : WithTop ℝ≥0)}.Finite

open Classical in
/-- The actual counting measure dN, including a possible atom at time zero. -/
noncomputable def EventStream.measure {Ω : Type*} (N : EventStream Ω) (ω : Ω) : Measure ℝ≥0 :=
  Measure.sum fun n => if N.time n ω = ⊤ then 0 else Measure.dirac ((N.time n ω).untopD 0)

/-- N_t is the cumulative count, represented in ℝ by the finite mass of [0,t]. -/
noncomputable def EventStream.count {Ω : Type*} (N : EventStream Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ((N.measure ω) (Iic t)).toReal

/-- N_{t-}, including the left state before any time-zero event. -/
noncomputable def EventStream.before {Ω : Type*} (N : EventStream Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ((N.measure ω) (Iio t)).toReal

/-- Jump of an event stream at a specified time. -/
noncomputable def EventStream.jump {Ω : Type*} (N : EventStream Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ((N.measure ω) {t}).toReal

/-- Nonnegative stochastic intensity via the predictable compensation identity. It does not
assume martingale representation, promise keeping, or any contract utility assertion. -/
def HasIntensity {Ω : Type*} [m : MeasurableSpace Ω] (F : Filtration ℝ≥0 m)
    (p : Measure Ω) (N : EventStream Ω) (rate : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ n, Measurable (N.time n)) ∧
  IsStronglyPredictable F rate ∧ (∀ t ω, 0 ≤ rate t ω) ∧
  ∀ Z : ℝ≥0 → Ω → ℝ≥0∞,
    Measurable[F.predictable] (Function.uncurry Z) →
    (∫⁻ ω, ∫⁻ t, Z t ω ∂(N.measure ω) ∂p) =
      ∫⁻ ω, ∫⁻ t, Z t ω * ENNReal.ofReal (rate t ω) ∂timeMeasure ∂p

/-- Càdlàg paths on the half-line. Left limits are required only at positive times. -/
def CadlagOnHalfLine (x : ℝ≥0 → ℝ) : Prop :=
  (∀ t, ContinuousWithinAt x (Ici t) t) ∧
  ∀ t, 0 < t → ∃ a : ℝ, Tendsto x (nhdsWithin t (Iio t)) (𝓝 a)

/-- The left limit of a real process; at zero the initial pre-jump value is given explicitly. -/
noncomputable def preValue {Ω : Type*} (x : ℝ≥0 → Ω → ℝ)
    (initial : Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t = 0 then initial ω else limUnder (nhdsWithin t (Iio t)) (fun s => x s ω)

/-- Nonnegative discounted Lebesgue–Stieltjes integral, permitting +infinity. -/
noncomputable def discounted (a : ℝ) (m : Measure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (Real.exp (-a * (t : ℝ))) ∂m

end SuspensionContract.HighCostC2.Supplement


