-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoVersionExists_F000
-- name    : LevyStochCalc_Brownian_VectorItoVersionExists_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:39:33.167783+00:00
-- url     : https://prove2.me/theorems/4a7c3893-1606-48d2-b196-377e3edc678c
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoVersionExists
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoVersionExists. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoVersionExists_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoVersionExists_F001
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000
import Definitions.Def_SourceProof_e135e60f4c0109b1a168208c

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
/-- **A continuous adapted version of a vector Itô process exists over the augmented
filtration**, with no side conditions on the filtration. -/
theorem exists_isVectorItoVersion_aug
    (Hp : ∀ p k, Probability.ProgressivelyMeasurable (augFiltration ℱ P) (H p k))
    (Hs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable (augFiltration ℱ P) (bdrift p))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B) :
    ∃ X : ℝ → Ω → Fin n → ℝ, IsVectorItoVersion W (augFiltration ℱ P)
      (fun k => isBrownianFiltration_augFiltration (hcoord k)) H hHm Hp Hs X₀ bdrift X :=
  _root_.Prove2MeSourceProof.h_e135e60f4c0109b1a168208c W (augFiltration ℱ P)
    (fun k => isBrownianFiltration_augFiltration (hcoord k)) H hHm Hp Hs hC0 hCH
    (fun _ ht => le_of_eq (augFiltration_of_nonpos ℱ P ht).symm)
    (fun _ hs h0 => measurableSet_augFiltration_of_null ℱ P hs h0)
    (fun p _ hA => le_augFiltration ℱ P 0 _ (hX₀ p hA)) bdrift hbm hbp hB0 hB
end Exists

end LevyStochCalc.Brownian.Ito


