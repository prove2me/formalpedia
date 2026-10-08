-- Prove2me | Definitions.Def_PalmQueueing_Palm_SwissArmySetting
-- name    : PalmQueueing_Palm_SwissArmySetting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T20:42:35.104741+00:00
-- url     : https://prove2.me/theorems/6cf097de-f57e-416f-909b-56b4561d13c0
-- title:
--   The setting of the Swiss army formula: arrivals, departures, sojourn times and the integrator
-- statement:
--   Theorem 1.3.1 is stated about five objects that §1.3.7 introduces over two pages and never
--   bundles. This is that bundle.
--
--   Let $\{T_n\}$ and $\{\tau_n\}$ be two simple point processes on $\mathbb{R}$ with counting measures
--   $A$ and $D$; both are counting measures in the sense of p.2 (finite on bounded intervals) and
--   simple. The sequence $\{T_n\}$ satisfies the usual conventions. The sequence $\{\tau_n\}$
--   satisfies $D(\mathbb{R}_+) = D(\mathbb{R} - \mathbb{R}_+) = \infty$ but **need not be ordered**;
--   it is required only that for each $n \in \mathbb{Z}$
--   $$ \tau_n - T_n \;\stackrel{\mathrm{def}}{=}\; W_n \;\ge\; 0 . \tag{1.3.26} $$
--   One may read $T_n$ as the arrival time of customer $n$ and $\tau_n$ as its departure time, so that
--   $W_n$ is its sojourn time. Let $\{X(t)\}$ be a non-negative integer-valued process with
--   $$ X(b) - X(a) \;=\; A((a,b]) - D((a,b]) \tag{1.3.27} $$
--   — the number in system. Let $\{B(t)\}$ be a non-decreasing, real-valued process, continuous on the
--   right and with limits on the left (corlol), and let $\int_{(a,b]} h(s)\,dB(s)$ denote the
--   Stieltjes-Lebesgue integral of $h$ with respect to the measure canonically associated with
--   $\{B(t)\}$. Finally let $\{Z(t)\}$ be a non-negative real-valued process.
--
--   Three modelling points decide whether the goal theorem is the book's theorem.
--
--   * $\{\tau_n\}$ is **not** modelled as a point process: the book says explicitly that it need not be
--     ordered, so a monotonicity field would be a hypothesis the book does not make. It is a bare
--     measurable family with its own counting measure.
--   * $\{B(t)\}$ is carried as a Stieltjes function for each $\omega$ — a monotone, right-continuous
--     $\mathbb{R} \to \mathbb{R}$, which is exactly the book's description, and which comes with the
--     Stieltjes-Lebesgue measure that $dB$ integrates against.
--   * $X(s-)$ is the left limit and is carried as a separate process together with the hypothesis that
--     it *is* the left limit, rather than constructed: nothing in the book's hypotheses forces
--     $\{X(t)\}$ to be regularisable by a formula.
--
--   One hypothesis is present here that p.29 does not list. Theorem 1.3.1 names $\{Z(t)\}, A, D$ and
--   $\{X(t)\}$ as $\theta_t$-compatible and omits $\{B(t)\}$; the proof uses the compatibility of
--   $\{B(t)\}$ all the same, at the step "$R(t) = R(0) \circ \theta_t$" of p.30. Without it the
--   identity is false, its left side being independent of $t$ while its right side would not be.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, §1.3.7, pp. 28-29

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# The setting of the Swiss Army formula (§1.3.7, pp.28-29)

Theorem 1.3.1 is stated about five objects that §1.3.7 introduces over two pages and never
bundles: a second point process `{τ_n}` which **need not be ordered**, the sojourn times
`W_n = τ_n - T_n`, a non-negative integer-valued process `{X(t)}` whose increments are the
difference of the two counting measures, a non-decreasing corlol integrator `{B(t)}`, and a
non-negative process `{Z(t)}`. This module is that bundle.

Three modelling points are worth stating here because they decide whether the goal theorem is the
book's theorem.

* `{τ_n}` is *not* a `PointProcess`: the book says explicitly that it "need not be ordered", so the
  `StrictMono` field of `PointProcess` would be a hypothesis the book does not make. It is carried
  as a bare measurable family with its own counting measure.
* `{B(t)}` is carried as a `StieltjesFunction` for each `ω`. Mathlib's `StieltjesFunction` is
  exactly a monotone right-continuous function `ℝ → ℝ`, which is the book's "non-decreasing,
  real-valued, continuous on the right and with limits on the left", and it comes with the
  Stieltjes-Lebesgue measure `(B ω).measure` that `∫ h(s) dB(s)` integrates against.
* `X(s-)` is the left limit, and it is not optional: the proof runs through the integration by
  parts formula (1.3.29), which needs the predictable version. It is carried as a separate process
  together with the hypothesis that it *is* the left limit, rather than constructed, because
  nothing in the book's hypotheses forces `{X(t)}` to be regularisable by a formula.
-/

namespace PalmQueueing.Palm

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable family of instants `{τ_n}_{n ∈ ℤ}` on `ℝ` which, unlike a `PointProcess`, is
**not** required to be ordered (p.28: "it need not be ordered"). The departure times of §1.3.7. -/
structure InstantFamily (Ω : Type*) [MeasurableSpace Ω] where
  /-- The `n`-th instant. -/
  tau : ℤ → Ω → ℝ
  /-- Each instant is a random variable. -/
  measurable_tau : ∀ n, Measurable (tau n)

/-- The counting measure `D(ω, ·)` of the family, `D(ω, C) = #{n : τ_n(ω) ∈ C}`. -/
noncomputable def InstantFamily.count (D : InstantFamily Ω) (ω : Ω) : Measure ℝ :=
  Measure.sum fun n : ℤ => Measure.dirac (D.tau n ω)

/-- `D(ℝ₊) = D(ℝ - ℝ₊) = ∞` (p.28): infinitely many instants on each side of the origin. -/
def InstantFamily.BiInfinite (D : InstantFamily Ω) : Prop :=
  ∀ ω, D.count ω (Set.Ici (0 : ℝ)) = ⊤ ∧ D.count ω (Set.Iio (0 : ℝ)) = ⊤

/-- The family is **compatible with the flow**, in the counting-measure form the book's formulas
integrate against: `D(θ_t ω, C) = D(ω, C + t)`. -/
def InstantFamily.Compatible (D : InstantFamily Ω) (θ : Flow Ω) : Prop :=
  ∀ (t : ℝ) (ω : Ω) (C : Set ℝ), MeasurableSet C →
    D.count (θ t ω) C = D.count ω ((fun s => s - t) ⁻¹' C)

/-- A non-decreasing, real-valued corlol process `{B(t)}` (p.29), carried by the
`StieltjesFunction` it is for each `ω`, so that `(B ω).measure` is the Stieltjes-Lebesgue measure
`dB` of the book. -/
structure Integrator (Ω : Type*) [MeasurableSpace Ω] where
  /-- `B(·, ω)`, monotone and right continuous. -/
  B : Ω → StieltjesFunction ℝ
  /-- `B(t, ·)` is a random variable for each `t`. -/
  measurable_B : ∀ t : ℝ, Measurable fun ω => (B ω) t

/-- The integrator is **compatible with the flow**: its Stieltjes-Lebesgue measure shifts with
`θ_t` exactly as a point process' counting measure does, `dB(θ_t ω)(C) = dB(ω)(C + t)`.

Theorem 1.3.1's hypothesis list on p.29 names `{Z(t)}, A, D` and `{X(t)}` as `θ_t`-compatible and
omits `{B(t)}`; the proof uses it all the same, at the step "`R(t) = R(0) ∘ θ_t`" of p.30. Without
it the identity is false, since its left side does not depend on `t` and its right side would.
See `MODERATION_NOTES.md`. -/
def Integrator.Compatible (B : Integrator Ω) (θ : Flow Ω) : Prop :=
  ∀ (t : ℝ) (ω : Ω) (C : Set ℝ), MeasurableSet C →
    (B.B (θ t ω)).measure C = (B.B ω).measure ((fun s => s - t) ⁻¹' C)

/-- The full setting of §1.3.7 (pp.28-29): a stationary arrival process with its Palm probability,
a departure family, the sojourn times, the number in system with its left-limit version, the
integrator and the integrand. -/
structure SwissArmySetting (Ω : Type*) [MeasurableSpace Ω] where
  /-- The arrival process `{T_n}` with counting measure `A`, its flow, `P`, `P⁰_A` and `λ_A`. -/
  toPalmSetting : PalmSetting Ω
  /-- The departure family `{τ_n}` with counting measure `D`. -/
  D : InstantFamily Ω
  /-- The sojourn times `W_n = τ_n - T_n`. -/
  W : ℤ → Ω → ℝ
  /-- The number in system `{X(t)}`. -/
  X : ℝ → Ω → ℝ
  /-- Its left-limit process `{X(s-)}`. -/
  Xl : ℝ → Ω → ℝ
  /-- The integrator `{B(t)}`. -/
  B : Integrator Ω
  /-- The integrand `{Z(t)}`. -/
  Z : ℝ → Ω → ℝ
  /-- `D` is a counting measure in the sense of p.2: finite on bounded intervals. -/
  D_locallyFinite : ∀ (ω : Ω) (a b : ℝ), D.count ω (Set.Icc a b) < ⊤
  /-- `D` is simple (p.28: "two simple point processes"): no two instants coincide. -/
  D_simple : ∀ (ω : Ω) (x : ℝ), D.count ω {x} ≤ 1
  /-- `D` has infinitely many points on each side of the origin (p.28). -/
  biInfinite : D.BiInfinite
  /-- `(1.3.26)`: `τ_n - T_n = W_n ≥ 0`. -/
  sojourn : ∀ (n : ℤ) (ω : Ω), D.tau n ω - toPalmSetting.N.T n ω = W n ω ∧ 0 ≤ W n ω
  /-- `{W_n}` is a sequence of marks of `A` (p.29). -/
  markSequence : IsMarkSequence toPalmSetting.θ toPalmSetting.N W
  /-- `{X(t)}` is non-negative and integer-valued (p.28). -/
  X_nonneg_int : ∀ (t : ℝ) (ω : Ω), 0 ≤ X t ω ∧ ∃ k : ℤ, X t ω = (k : ℝ)
  /-- `(1.3.27)`: `X(b) - X(a) = A((a,b]) - D((a,b])`. -/
  balance : ∀ (a b : ℝ) (ω : Ω), a ≤ b →
    X b ω - X a ω =
      (toPalmSetting.N.count ω (Set.Ioc a b)).toReal - (D.count ω (Set.Ioc a b)).toReal
  /-- `{Xl(t)}` is the left-limit process of `{X(t)}`. -/
  leftLimit : IsLeftLimitProcess X Xl
  /-- `{Z(t)}` is non-negative (p.29). -/
  Z_nonneg : ∀ (t : ℝ) (ω : Ω), 0 ≤ Z t ω
  /-- `Z(t, ·)` is a random variable at each time. -/
  Z_measurable : ∀ t : ℝ, Measurable (Z t)
  /-- `X(t, ·)` is a random variable at each time. -/
  X_measurable : ∀ t : ℝ, Measurable (X t)
  /-- `X(t-, ·)` is a random variable at each time. -/
  Xl_measurable : ∀ t : ℝ, Measurable (Xl t)
  /-- `{Z(t)}` is `θ_t`-compatible. -/
  Z_compatible : IsCompatible toPalmSetting.θ Z
  /-- `A` is `θ_t`-compatible (already a field of `PalmSetting`, restated for readability). -/
  A_compatible : toPalmSetting.N.Compatible toPalmSetting.θ
  /-- `D` is `θ_t`-compatible. -/
  D_compatible : D.Compatible toPalmSetting.θ
  /-- `{X(t)}` is `θ_t`-compatible. -/
  X_compatible : IsCompatible toPalmSetting.θ X
  /-- `{B(t)}` is `θ_t`-compatible; see `Integrator.Compatible` for why this is here and not on
  p.29. -/
  B_compatible : B.Compatible toPalmSetting.θ

end PalmQueueing.Palm


