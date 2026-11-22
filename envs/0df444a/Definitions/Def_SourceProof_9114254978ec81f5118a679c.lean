-- Prove2me | Definitions.Def_SourceProof_9114254978ec81f5118a679c
-- name    : SourceProof_9114254978ec81f5118a679c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:12:06.399942+00:00
-- url     : https://prove2.me/theorems/3f9eae82-83eb-4fde-9556-30e59a5678d8
-- title:
--   LevyStochCalc source module: SourceProof_9114254978ec81f5118a679c
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.energy_picardSeq_cauchy_coord` comes from the `LevyStochCalc.BSDEJ.PicardIteratesCauchy` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The geometric Cauchy estimate for the Picard iterates

The exponentially weighted norm `wNorm` at a nonnegative weight dominates the energies of the
value process, of the diffusion coordinates and of the jump integrand, and is subadditive along
an intermediate triple up to a factor of two. Combined with the one-step contraction at the Young
weight `β = max 2 (24 L²)`, this gives a geometric bound with ratio `1/4` on the weighted norm of
consecutive Picard iterates, and hence a Cauchy estimate for the iterates in the weighted norm
and in the unweighted energies on the horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Subadditivity and lower bounds for the weighted norm -/

section WNorm

variable {β T : ℝ}

end WNorm

/-! ### The geometric Cauchy estimate along the iterates -/

section Cauchy

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}
  (hT : 0 < T)
  (hf : ∀ u : E → ℝ, Measurable fun q : ℝ × ℝ × (Fin d → ℝ) => f q.1 q.2.1 q.2.2 u)
  (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
    (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
      ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
  (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
  (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)


theorem _root_.Prove2MeSourceProof.h_9114254978ec81f5118a679c (hL : 0 ≤ L) (p₀ : AdmTriple D T) (i : Fin d) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 s ω i
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 s ω i) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := LevyStochCalc.BSDEJ.Solves.wNorm_picardSeq_cauchy hT hf hlip hf0 hξ2 hξm hL p₀ ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  have hAm := LevyStochCalc.BSDEJ.Solves.picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ m
  have hAn := LevyStochCalc.BSDEJ.Solves.picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ n
  exact lt_of_le_of_lt
    (LevyStochCalc.BSDEJ.Solves.energy_coord_le_wNorm (Y := fun t ω => (LevyStochCalc.BSDEJ.Solves.picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 t ω
        - (LevyStochCalc.BSDEJ.Solves.picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
      (Z := fun t ω => (LevyStochCalc.BSDEJ.Solves.picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 t ω
        - (LevyStochCalc.BSDEJ.Solves.picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
      (U := fun t ω e => (LevyStochCalc.BSDEJ.Solves.picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 t ω e
        - (LevyStochCalc.BSDEJ.Solves.picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e) (LevyStochCalc.BSDEJ.Solves.zero_le_youngWeight L)
      (hAm.measurable_uncurry_Y.sub hAn.measurable_uncurry_Y)
      (fun j => (hAm.Z_meas j).sub (hAn.Z_meas j)) i) (hN m hm n hn)
end Cauchy

end LevyStochCalc.BSDEJ.Solves


