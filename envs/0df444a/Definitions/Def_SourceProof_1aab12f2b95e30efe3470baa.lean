-- Prove2me | Definitions.Def_SourceProof_1aab12f2b95e30efe3470baa
-- name    : SourceProof_1aab12f2b95e30efe3470baa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:24:12.685323+00:00
-- url     : https://prove2.me/theorems/d9b404d8-7b56-4098-9a8f-ae456af7b057
-- title:
--   LevyStochCalc source module: SourceProof_1aab12f2b95e30efe3470baa
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit` comes from the `LevyStochCalc.BSDEJ.PicardLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F001
import Definitions.Def_SourceProof_27f689978bb8ca67ff7e2231
import Definitions.Def_SourceProof_8222c374c1c82ec98450f68e
import Definitions.Def_SourceProof_8597dc90ffad905522400a1d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The limit of the Picard iterates and existence of a solution

The Picard iterates of a backward equation with jumps are Cauchy for the energy of the value
process, for the energies of the diffusion coordinates and for the marked energy of the jump
integrand, so completeness of the admissible integrands produces an admissible limit triple
which the iterates approach in the exponentially weighted norm at the Young weight
`max 2 (24 L²)`. A further Picard step along the limit triple contracts that distance by `1/4`
against every iterate, so its output is at zero weighted distance from the limit triple; a
Lipschitz generator takes the same value along two triples agreeing almost everywhere on
`Ω × [0, T]`, so the output is its own Picard output and solves the equation.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.congr_inputs` — a Picard output along one input
  triple is a Picard output along any input triple agreeing with it almost everywhere on the
  horizon.
* `LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit` — an energy-Cauchy sequence of
  admissible triples converges in the weighted norm to an admissible triple.
* `LevyStochCalc.BSDEJ.Solves.exists_solvesBSDEJ` — a backward equation with jumps whose
  generator is Lipschitz and square integrable at the origin and whose terminal datum is square
  integrable has a solution.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Truncation to the horizon -/

/-! ### Changing the input triple of a Picard step on a null set -/

/-! ### Triples at zero weighted distance -/

/-! ### The weighted norm against the energies -/

/-! ### The limit of an energy-Cauchy sequence of admissible triples -/

section Limit

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {T : ℝ}


theorem _root_.Prove2MeSourceProof.h_1aab12f2b95e30efe3470baa {q : ℕ → Triple Ω E d}
    (hA : ∀ n, Admissible D T (q n).1 (q n).2.1 (q n).2.2)
    (hcY : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => (q m).1 s ω - (q n).1 s ω) < ε)
    (hcZ : ∀ i : Fin d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => (q m).2.1 s ω i - (q n).2.1 s ω i) < ε)
    (hcU : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => (q m).2.2 s ω e - (q n).2.2 s ω e) < ε)
    {β : ℝ} (hβ : 0 ≤ β) :
    ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
      Admissible D T Y Z U ∧ Tendsto (fun n => wNorm P ν β T
        (fun t ω => (q n).1 t ω - Y t ω) (fun t ω => (q n).2.1 t ω - Z t ω)
        (fun t ω e => (q n).2.2 t ω e - U t ω e)) atTop (𝓝 0) := by
  classical
  obtain ⟨KY, hKYm, hKYp, hKYq, hKYt⟩ :=
    _root_.Prove2MeSourceProof.h_8222c374c1c82ec98450f68e (LevyStochCalc.BSDEJ.Solves.augJoint D).rightCont
      (H := fun n ω s => (q n).1 s ω) (fun n => (hA n).measurable_uncurry_Y)
      (fun n => (hA n).Y_prog) (fun n => (hA n).Y_sq) hcY
  have hZlim : ∀ i : Fin d, ∃ K : Ω → ℝ → ℝ, Measurable (Function.uncurry K)
      ∧ LevyStochCalc.Probability.ProgressivelyMeasurable (LevyStochCalc.BSDEJ.Solves.augJoint D) K
      ∧ (∀ ω, ∀ s ∉ Set.Icc (0 : ℝ) T, K ω s = 0)
      ∧ LevyStochCalc.Brownian.Ito.energy P T K ≠ ⊤
      ∧ Tendsto (fun n => LevyStochCalc.Brownian.Ito.energy P T
          (fun ω s => (q n).2.1 s ω i - K ω s)) atTop (𝓝 0) := by
    intro i
    refine _root_.Prove2MeSourceProof.h_27f689978bb8ca67ff7e2231 (LevyStochCalc.BSDEJ.Solves.augJoint D)
      (fun n => (hA n).Z_meas i) (fun n => (hA n).Z_prog i) (fun n ω s hs => ?_)
      (fun n => (hA n).Z_sq i) (hcZ i)
    have hv := (hA n).Z_vanish ω s hs
    simp [hv]
  choose KZ hKZm hKZp hKZz hKZq hKZt using hZlim
  obtain ⟨KU, hKUm, hKUp, hKUz, hKUq, hKUt⟩ :=
    _root_.Prove2MeSourceProof.h_8597dc90ffad905522400a1d (LevyStochCalc.BSDEJ.Solves.augJoint D)
      (fun n => (hA n).U_meas) (fun n => (hA n).U_prog) (fun n => (hA n).U_vanish)
      (fun n => (hA n).U_sq) hcU
  refine ⟨fun s ω => KY ω s, fun s ω i => KZ i ω s, fun s ω e => KU ω s e,
    { Y_meas := hKYm.comp measurable_swap, Y_prog := hKYp, Y_sq := hKYq,
      Z_meas := hKZm, Z_prog := hKZp,
      Z_vanish := fun ω s hs => funext fun i => hKZz i ω s hs, Z_sq := hKZq,
      U_meas := hKUm, U_prog := hKUp, U_vanish := hKUz, U_sq := hKUq }, ?_⟩
  have hsumZ : Tendsto (fun n => ∑ j, LevyStochCalc.Brownian.Ito.energy P T
      (fun ω s => (q n).2.1 s ω j - KZ j ω s)) atTop (𝓝 0) := by
    have hfs := tendsto_finsetSum (Finset.univ : Finset (Fin d))
      fun j (_ : j ∈ Finset.univ) => hKZt j
    simpa using hfs
  have hsum : Tendsto (fun n => LevyStochCalc.Brownian.Ito.energy P T
        (fun ω s => (q n).1 s ω - KY ω s)
      + (∑ j, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => (q n).2.1 s ω j - KZ j ω s))
      + LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => (q n).2.2 s ω e - KU ω s e)) atTop (𝓝 0) := by
    simpa using (hKYt.add hsumZ).add hKUt
  have hlim : Tendsto (fun n => ENNReal.ofReal (Real.exp (β * T)) *
      (LevyStochCalc.Brownian.Ito.energy P T (fun ω s => (q n).1 s ω - KY ω s)
        + (∑ j, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => (q n).2.1 s ω j - KZ j ω s))
        + LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => (q n).2.2 s ω e - KU ω s e))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (β * T)) * 0)) :=
    ENNReal.Tendsto.const_mul hsum (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le)
    (fun n => LevyStochCalc.BSDEJ.Solves.wNorm_le_energies hβ ((hA n).measurable_uncurry_Y.sub hKYm)
      fun j => ((hA n).Z_meas j).sub (hKZm j))
end Limit

/-! ### The fixed point of the Picard step -/

section FixedPoint

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}

end FixedPoint

/-! ### Existence of a solution -/

end LevyStochCalc.BSDEJ.Solves


