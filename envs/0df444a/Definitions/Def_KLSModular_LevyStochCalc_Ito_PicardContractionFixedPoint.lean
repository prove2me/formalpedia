-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContractionFixedPoint
-- name    : KLSModular_LevyStochCalc_Ito_PicardContractionFixedPoint
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:10:05.744002+00:00
-- url     : https://prove2.me/theorems/b914ab33-ae92-46bd-8cc4-7cc082e284b0
-- title:
--   The Picard limit and its finite Bielecki norm
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `picardLimit` is the `bieleckiLimit` of the process-space Picard iterates, and the bundle proves that it is jointly measurable and progressively measurable. When the explicit contraction factor is strictly less than $1$, `bieleckiNorm_picardLimit_lt_top` proves finiteness of its unweighted Bielecki norm on $[0,T]$. These declarations concern the limit construction and its regularity and do not themselves state a full fixed-point or SDE solution theorem.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.PicardContractionEstimate
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def picardLimit (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
--       ℝ → Ω → (Fin n → ℝ) :=
--     bieleckiLimit fun m =>
--       (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).X
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/PicardContractionEstimate`](https://prove2.me/theorems/8cad574e-6914-4d17-98ca-b6df8ebe8b41).
--
--   Theorems in source order:
--
--   - [`measurable_picardStepOnRawStop_slice`](https://prove2.me/theorems/b756fd53-bc8d-4424-9fc0-745ef08f7652)
--   - [`bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero`](https://prove2.me/theorems/f04f380e-8b10-422c-b9f4-8f255f38cc70)
--   - [`ae_eq_zero_of_bieleckiNorm_eq_zero`](https://prove2.me/theorems/03028af0-5e72-4f50-a46d-8baf738dd95f)
--   - [`picardSelfMapRaw_picardLimit_ae_eq`](https://prove2.me/theorems/f4ca4fcf-9668-4089-9376-14ea28fdaad0)
--   - [`bieleckiNorm_picardStepOnRawStop_diff_le`](https://prove2.me/theorems/9a6322fc-eee3-47fb-b0eb-e8fa350bde78)
--   - [`picardStepOnRawStop_congr_ae`](https://prove2.me/theorems/e25c11bd-0c57-4831-ab92-f4ec98009984)
--   - [`picardSelfMapRaw_isFixedPoint`](https://prove2.me/theorems/8d60ac0b-9ec8-46b3-ab34-28751499333d)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardContractionFixedPoint.lean) · `LevyStochCalc.Ito.PicardContractionFixedPoint` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardContractionFixedPoint.lean#L51-L108 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardContractionFixedPoint`, definition bundle `KLSModular_LevyStochCalc_Ito_PicardContractionFixedPoint`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContractionEstimate

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardContractionFixedPoint.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
variable {L : ℝ}
  (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
  (x₀ : Fin n → ℝ)
/-- **The limit of the Picard iterates.** -/
noncomputable def picardLimit (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
    ℝ → Ω → (Fin n → ℝ) :=
  bieleckiLimit fun m =>
    (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).X
theorem measurable_picardLimit (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
    Measurable (Function.uncurry
      (picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)) :=
  measurable_bieleckiLimit fun m =>
    (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).measurable_path
theorem progressivelyMeasurable_picardLimit (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T) (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ'
      fun ω s => picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ s ω i :=
  progressivelyMeasurable_bieleckiLimit
    (fun m i' => (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).adapted i') i
omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg in
/-- Slice measurability of a jointly measurable path map. -/
theorem measurable_slice_of_uncurry {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (t : ℝ) (i : Fin n) :
    Measurable fun ω => Z t ω i :=
  (measurable_pi_apply i).comp (Measurable.of_uncurry_left hZm)
/-- The limit of the Picard iterates has finite Bielecki norm at weight `0`. -/
theorem bieleckiNorm_picardLimit_lt_top {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) :
    bieleckiNorm (P := P) 0 T
      (picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀) < ⊤ := by
  have hYm := measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hbase : bieleckiNorm (P := P) β T X₀.X < ⊤ :=
    lt_of_le_of_lt (bieleckiNorm_le_bieleckiNorm_zero hβ.le T X₀.X) X₀.sup_L2
  have hsub := bieleckiNorm_picardIter_sub_bieleckiLimit_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs
    hReg hLip x₀ hβ hT X₀ hq 0
  have hfin : ((1 - (ENNReal.ofReal
        ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
          / (2 * β))) ^ ((1 : ℝ) / 2))⁻¹
      * bieleckiNorm (P := P) β T (fun t ω i =>
          (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
            - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i))
      ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hq).ne')
      (bieleckiNorm_sub_lt_top ℱ' hβ.le _ _).ne
  have hd : bieleckiNorm (P := P) β T (fun t ω i => X₀.X t ω i
      - picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ t ω i) < ⊤ := by
    refine lt_of_le_of_lt hsub ?_
    rw [pow_zero, one_mul]
    exact lt_top_iff_ne_top.mpr hfin
  refine lt_of_le_of_lt (bieleckiNorm_zero_le_mul (P := P) hβ.le _)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact bieleckiNorm_lt_top_of_approx β T
    (fun t i => measurable_slice_of_uncurry X₀.measurable_path t i)
    (fun t i => measurable_slice_of_uncurry hYm t i) hbase hd
end Picard
end Ito
end LevyStochCalc


