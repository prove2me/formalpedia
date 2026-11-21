-- Prove2me | Definitions.Def_SourceProof_e135e60f4c0109b1a168208c
-- name    : SourceProof_e135e60f4c0109b1a168208c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:37:55.27486+00:00
-- url     : https://prove2.me/theorems/0da20673-b99a-4a4f-8aed-fa4a8aa0700f
-- title:
--   LevyStochCalc source module: SourceProof_e135e60f4c0109b1a168208c
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion` comes from the `LevyStochCalc.Brownian.VectorItoVersionExists` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoVersionExists_F001
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000
import Definitions.Def_SourceProof_cf3c0bc6d72699b1e0b734c3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Existence of a continuous adapted version of a vector Itô process

Each entry of the diffusion matrix contributes an Itô integral against its own Brownian
coordinate, and each of those has a continuous adapted modification. Summing them over the
Brownian index and adding the initial value and the drift's window integral gives a continuous
adapted version of the vector Itô process.

## Main statements

* `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion` — a continuous adapted version exists.
* `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_aug` — the same over the augmented
  filtration, with no side conditions.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Exists

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
  (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
  (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_e135e60f4c0109b1a168208c
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X := by
  classical
  choose Y hYcont hYadapt hYmod using fun (p : Fin n) (k : Fin d) =>
    _root_.Prove2MeSourceProof.h_cf3c0bc6d72699b1e0b734c3 (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
      (hHs p k) hC0 (hCH p k) hℱ0 hnull
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  refine ⟨fun t ω p => X₀ ω p + (∫ s in Set.Icc (0 : ℝ) t, bdrift p ω s ∂volume)
      + ∑ k : Fin d, Y p k t ω, ?_, ?_, ?_⟩
  · intro ω
    refine continuous_pi fun p => (continuous_const.add
      (LevyStochCalc.continuous_setIntegral_Icc (Measurable.of_uncurry_left (hbm p)) hB0 (hB p ω))).add ?_
    exact continuous_finsetSum _ fun k _ => hYcont p k ω
  · intro t
    have hcoordm : ∀ p : Fin n, Measurable[ℱ t] fun ω =>
        X₀ ω p + (∫ s in Set.Icc (0 : ℝ) t, bdrift p ω s ∂volume) + ∑ k : Fin d, Y p k t ω := by
      intro p
      refine Measurable.add (Measurable.add (fun A hA => hle0 t _ (hX₀ p hA)) ?_)
        (Finset.measurable_sum _ fun k _ => hYadapt p k t)
      exact (((hbp p).stronglyMeasurable_setIntegral measurableSet_Icc
        Set.Icc_subset_Iic_self volume).mono le_rfl).measurable
    refine Measurable.stronglyMeasurable ?_
    letI : MeasurableSpace Ω := ℱ t
    exact measurable_pi_lambda _ hcoordm
  · intro t ht
    have hall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
        Y p k t ω = LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k t ω :=
      MeasureTheory.ae_all_iff.mpr fun p =>
        MeasureTheory.ae_all_iff.mpr fun k => hYmod p k t ht
    filter_upwards [hall] with ω hω
    funext p
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess, vectorItoMartingale]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hω p k
end Exists

end LevyStochCalc.Brownian.Ito


