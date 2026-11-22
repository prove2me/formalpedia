-- Prove2me | Definitions.Def_SourceProof_dd09ea5fa8a71a081fb46fa8
-- name    : SourceProof_dd09ea5fa8a71a081fb46fa8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:13:07.417177+00:00
-- url     : https://prove2.me/theorems/41eb40f8-57fb-46e1-96ae-8705251bfc9f
-- title:
--   LevyStochCalc source module: SourceProof_dd09ea5fa8a71a081fb46fa8
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.exists_solvesBSDEJ_of_wNorm_limit` comes from the `LevyStochCalc.BSDEJ.PicardLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F001
import Definitions.Def_SourceProof_6aaece9b3ee7806711830a77

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

end Limit

/-! ### The fixed point of the Picard step -/

section FixedPoint

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_dd09ea5fa8a71a081fb46fa8 (hL : 0 ≤ L) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun r : ℝ × ℝ × (Fin d → ℝ) => f r.1 r.2.1 r.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)
    {q : ℕ → Triple Ω E d} (hA : ∀ n, Admissible D T (q n).1 (q n).2.1 (q n).2.2)
    (hstep : ∀ n, IsStep D f ξ T (q n).1 (q n).2.1 (q n).2.2
      (q (n + 1)).1 (q (n + 1)).2.1 (q (n + 1)).2.2)
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hq : Admissible D T Y Z U)
    (hlim : Tendsto (fun n => wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => (q n).1 t ω - Y t ω) (fun t ω => (q n).2.1 t ω - Z t ω)
      (fun t ω e => (q n).2.2 t ω e - U t ω e)) atTop (𝓝 0)) :
    ∃ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ),
      SolvesBSDEJ D f ξ T Y' Z' U' := by
  obtain ⟨Ys, Zs, Us, hAs, b, hbm, hbp, hbz, hbq, hb, hout⟩ :=
    hq.exists_step (L := L) hT hf hlip hf0 hξ2 hξm
  refine ⟨Ys, Zs, Us, ?_⟩
  have hcomm : ∀ n : ℕ, LevyStochCalc.BSDEJ.Solves.wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => Y t ω - (q n).1 t ω) (fun t ω => Z t ω - (q n).2.1 t ω)
      (fun t ω e => U t ω e - (q n).2.2 t ω e)
      = LevyStochCalc.BSDEJ.Solves.wNorm P ν (max 2 (24 * L ^ 2)) T
        (fun t ω => (q n).1 t ω - Y t ω) (fun t ω => (q n).2.1 t ω - Z t ω)
        (fun t ω e => (q n).2.2 t ω e - U t ω e) := fun n =>
    LevyStochCalc.BSDEJ.Solves.wNorm_sub_comm _ _ _ _ _ _
  have hbound : ∀ n : ℕ, LevyStochCalc.BSDEJ.Solves.wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => Ys t ω - Y t ω) (fun t ω => Zs t ω - Z t ω)
      (fun t ω e => Us t ω e - U t ω e)
      ≤ 2 * (4⁻¹ * LevyStochCalc.BSDEJ.Solves.wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => (q n).1 t ω - Y t ω) (fun t ω => (q n).2.1 t ω - Z t ω)
          (fun t ω e => (q n).2.2 t ω e - U t ω e))
        + 2 * LevyStochCalc.BSDEJ.Solves.wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => (q (n + 1)).1 t ω - Y t ω)
          (fun t ω => (q (n + 1)).2.1 t ω - Z t ω)
          (fun t ω e => (q (n + 1)).2.2 t ω e - U t ω e) := by
    intro n
    obtain ⟨b₂, hb₂m, hb₂p, hb₂z, hb₂q, hb₂, hout₂⟩ := hstep n
    have hcon : LevyStochCalc.BSDEJ.Solves.wNorm P ν (max 2 (24 * L ^ 2)) T
        (fun t ω => Ys t ω - (q (n + 1)).1 t ω)
        (fun t ω => Zs t ω - (q (n + 1)).2.1 t ω)
        (fun t ω e => Us t ω e - (q (n + 1)).2.2 t ω e)
        ≤ 4⁻¹ * LevyStochCalc.BSDEJ.Solves.wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => Y t ω - (q n).1 t ω) (fun t ω => Z t ω - (q n).2.1 t ω)
          (fun t ω e => U t ω e - (q n).2.2 t ω e) :=
      LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_of_picardOutput hL hlip hT hout hout₂
        (hq.measurable_uncurry_Y.sub (hA n).measurable_uncurry_Y)
        (fun j => (hq.Z_meas j).sub ((hA n).Z_meas j)) (hq.U_meas.sub (hA n).U_meas)
        hbm hbp hbz hbq hb hb₂m hb₂p hb₂z hb₂q hb₂
        (hq.wNorm_sub_ne_top (hA n) (LevyStochCalc.BSDEJ.Solves.zero_le_youngWeight L))
    refine le_trans (_root_.Prove2MeSourceProof.h_39fe24509dab75a4c4176089 (Y₂ := (q (n + 1)).1)
      (Z₂ := (q (n + 1)).2.1) (U₂ := (q (n + 1)).2.2)
      (hAs.measurable_uncurry_Y.sub (hA (n + 1)).measurable_uncurry_Y)
      (fun j => (hAs.Z_meas j).sub ((hA (n + 1)).Z_meas j))
      (hAs.U_meas.sub (hA (n + 1)).U_meas)) ?_
    refine add_le_add (mul_le_mul' le_rfl ?_) le_rfl
    rw [← hcomm n]
    exact hcon
  have hzero := LevyStochCalc.BSDEJ.Solves.eq_zero_of_le_two_mul_of_tendsto _ hlim hbound
  obtain ⟨hY, hZ, hU⟩ := LevyStochCalc.BSDEJ.Solves.ae_eq_of_wNorm_sub_eq_zero
    (hAs.measurable_uncurry_Y.sub hq.measurable_uncurry_Y)
    (fun j => (hAs.Z_meas j).sub (hq.Z_meas j)) (hAs.U_meas.sub hq.U_meas) hzero
  refine _root_.Prove2MeSourceProof.h_6aaece9b3ee7806711830a77
    (LevyStochCalc.BSDEJ.Solves.PicardOutput.congr_inputs (L := L) hlip ?_ ?_ ?_ hout)
  · filter_upwards [hY] with p hp
    exact hp.symm
  · filter_upwards [hZ] with p hp
    exact hp.symm
  · filter_upwards [hU] with p hp
    rw [← hp]
    exact lintegral_congr fun e => by rw [LevyStochCalc.BSDEJ.Solves.coe_nnnorm_sub_comm]
end FixedPoint

/-! ### Existence of a solution -/

end LevyStochCalc.BSDEJ.Solves


