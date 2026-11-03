-- Prove2me | Definitions.Def_LeanLevy_Processes_CompoundPoissonLaw
-- name    : LeanLevy_Processes_CompoundPoissonLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-31T10:23:45.212168+00:00
-- url     : https://prove2.me/theorems/c4917990-d8e7-4508-bd87-d573bec7916b
-- title:
--   LeanLevy source module: Processes.CompoundPoissonLaw
-- statement:
--   Pinned source definition and helper bundle. The original generated Lean module passed the earlier local build. This draft awaits Prove2Me remote compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Probability_Poisson
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic

/-!
# The jump-count law of a compound Poisson process is Poisson

For a compound Poisson driver with interarrival rate `r`, the arrival times
`arrival τ n ω = ∑_{i ≤ n} τ i ω` are the partial sums of the i.i.d. exponential interarrival
times. This file identifies the law of the associated *jump count*
`jumpCount (arrival τ · ω) t = #{n : arrival τ n ω ≤ t}` as a Poisson law with mean `r · t`.

The mathematical core is the classical fact that the sum of `n + 1` i.i.d. exponential rate `r`
variables has the Gamma density `r^{n+1} s^n e^{-rs} / n!` on `(0, ∞)`. We prove this by induction
on `n`: the base case is the exponential density, and the induction step convolves with one more
exponential — computed here from scratch as `withDensity ∗ withDensity = withDensity` of the density
convolution, since mathlib has no sum-of-exponentials-is-Gamma. The survival function of the arrival
time is then a finite interval integral, evaluated by the fundamental theorem of calculus, and the
Poisson jump-count law follows by telescoping the survival probabilities.

## Main results

* `ProbabilityTheory.arrival_survival` — `P(arrival τ n > t) = e^{-rt} ∑_{k ≤ n} (rt)^k / k!`.
* `ProbabilityTheory.map_jumpCount_arrival` — the law of the jump count at time `t` is
  `poissonMeasure (r · t)`.
* `ProbabilityTheory.charFun_map_compoundPoisson` — the characteristic function of the
  compound-Poisson-with-drift marginal at time `t` is
  `exp(t · (i b ξ + r · (charFun ν' ξ − 1)))`.
* `ProbabilityTheory.compoundPoissonTriple` — the Lévy–Khintchine triple `(b', 0, r · ν')` of a
  compound Poisson process with drift `b`, jump rate `r`, and jump law `ν'`.
* `ProbabilityTheory.charFun_map_compoundPoisson_eq_exponent` — the marginal's characteristic
  function is `exp(t · ψ_T)` for `T = compoundPoissonTriple b r ν'`, realizing the finite-activity,
  zero-Gaussian Lévy–Khintchine triples.
* `ProbabilityTheory.isInfinitelyDivisible_map_compoundPoisson` — every marginal is infinitely
  divisible.
-/

open MeasureTheory Filter Finset
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ}
  {μ : Measure Ω}

/-! ## The Gamma density of the arrival times -/

/-- The real-valued Gamma`(n + 1, R)` density: `R^{n+1} s^n e^{-Rs} / n!`. -/
private noncomputable def arrivalDensityReal (R : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  R ^ (n + 1) * s ^ n * Real.exp (-(R * s)) / n.factorial

/-- The Gamma`(n + 1, R)` density as an `ℝ≥0∞`-valued function, supported on `[0, ∞)`. -/
private noncomputable def arrivalDensity (R : ℝ) (n : ℕ) (s : ℝ) : ℝ≥0∞ :=
  (Set.Ici 0).indicator (fun s => ENNReal.ofReal (arrivalDensityReal R n s)) s









/-- The survival polynomial `e^{-Rt} ∑_{k ≤ n} (Rt)^k / k!`. -/
private noncomputable def survivalPoly (R : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(R * t)) * ∑ k ∈ Finset.range (n + 1), (R * t) ^ k / (k.factorial : ℝ)



/-! ## Base case: the exponential density -/



/-! ## Convolution of densities -/





/-! ## The Gamma law of the arrival times -/



/-! ## Survival function -/











/-! ## The jump count is Poisson -/



/-! ## The characteristic function of the compound Poisson marginal -/








-- This large conditioning proof (independence factorization + Poisson generating series) became
-- slower after the mathlib bump; the elaboration budget is raised to accommodate it.


/-! ## The Lévy–Khintchine triple of the compound Poisson marginal -/

/-- **The Lévy–Khintchine triple of a compound Poisson process** with drift `b`, jump rate `r`,
and (probability) jump law `ν'`. The Gaussian part vanishes, the Lévy measure is the finite measure
`r · ν'`, and the drift is corrected by the small-jump compensator `∫_{|x| < 1} x d(r · ν')` so that
the compensated Lévy–Khintchine exponent reproduces the compound-Poisson characteristic exponent
`i b ξ + r (charFun ν' ξ − 1)` (proved in this file en route to
`charFun_map_compoundPoisson_eq_exponent`). By uniqueness of the triple
of an infinitely divisible law (`existsUnique_levyKhintchineTriple`) this is *the* Lévy–Khintchine
triple of the time-`1` marginal. -/
noncomputable def compoundPoissonTriple (b : ℝ) (r : ℝ≥0) (ν' : Measure ℝ)
    [IsProbabilityMeasure ν'] (hν' : ν' {0} = 0) : LevyKhintchineTriple where
  drift := b + ∫ x in {x : ℝ | |x| < 1}, x ∂((r : ℝ≥0∞) • ν')
  gaussianVariance := 0
  levyMeasure := (r : ℝ≥0∞) • ν'
  levyMeasure_isLevyMeasure := by
    haveI : IsFiniteMeasure ((r : ℝ≥0∞) • ν') := Measure.smul_finite ν' ENNReal.coe_ne_top
    refine IsLevyMeasure.of_isFiniteMeasure ?_
    rw [Measure.smul_apply, hν', smul_zero]









end ProbabilityTheory


