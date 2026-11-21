-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoThirdMoment_F000
-- name    : LevyStochCalc_Brownian_VectorItoThirdMoment_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:33:13.97882+00:00
-- url     : https://prove2.me/theorems/92d372dc-5a00-4de6-b0e4-b3400b62cad4
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.VectorItoThirdMoment
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.VectorItoThirdMoment in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F002
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F003
import Definitions.Def_SourceProof_5772ba714260d30ff9581e64
import Definitions.Def_SourceProof_5e84cb76e3723bb35ee92ba4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Third absolute moments of a vector Itô process's increments

The second-order Taylor remainder of a function with Lipschitz second derivative is cubic in the
increment, so Itô's formula in the vector setting needs the third absolute moment of `‖ΔX‖`. It
is assembled from the coordinatewise splitting: the supremum norm is controlled by the sum of the
coordinates, each coordinate by its drift part and its martingale part, and the martingale part
by the individual Itô increments.

## Main statements

* `LevyStochCalc.Brownian.Ito.integral_abs_sum_pow_three_le` — the third absolute moment of a
  finite sum.
* `LevyStochCalc.Brownian.Ito.integral_norm_pi_pow_three_le` — the third moment of the supremum
  norm from the coordinates.
* `LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_pow_three_le` —
  `𝔼‖ΔX‖³ ≤ 4n³((BΔt)³ + d³κ Δt√(Δt))` with `κ = (C² + (6+c)C⁴)/2`.
* `LevyStochCalc.Brownian.Ito.sum_integral_norm_vectorItoIncrement_pow_three_le` — the same
  summed over a uniform grid, of order `m^{-1/2}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section GenericThird

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The third absolute moment of a finite sum is at most the squared number of summands times the
sum of the third absolute moments. -/
theorem integral_abs_sum_pow_three_le {ι : Type*} [Fintype ι] {f : ι → Ω → ℝ}
    (hfm : ∀ i, Measurable (f i)) (hfi : ∀ i, Integrable (fun ω => |f i ω| ^ 3) P)
    {c : ι → ℝ} (hc : ∀ i, ∫ ω, |f i ω| ^ 3 ∂P ≤ c i) :
    ∫ ω, |∑ i, f i ω| ^ 3 ∂P ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ i, c i := by
  have hdom : Integrable (fun ω => (Fintype.card ι : ℝ) ^ 2 * ∑ i, |f i ω| ^ 3) P :=
    (MeasureTheory.integrable_finsetSum _ fun i _ => hfi i).const_mul _
  have hpt : ∀ ω, |∑ i, f i ω| ^ 3 ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ i, |f i ω| ^ 3 := fun ω => by
    have h1 : |∑ i, f i ω| ^ 3 ≤ (∑ i, |f i ω|) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) 3
    have h2 := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset ι))
      (f := fun i => |f i ω|) (fun j _ => abs_nonneg (f j ω)) 2
    simpa using h1.trans h2
  have hint : Integrable (fun ω => |∑ i, f i ω| ^ 3) P :=
    _root_.Prove2MeSourceProof.h_ca47293a4e2de3cbd71da814 hfm hfi
  calc ∫ ω, |∑ i, f i ω| ^ 3 ∂P
      ≤ ∫ ω, (Fintype.card ι : ℝ) ^ 2 * ∑ i, |f i ω| ^ 3 ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = (Fintype.card ι : ℝ) ^ 2 * ∑ i, ∫ ω, |f i ω| ^ 3 ∂P := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum _ fun i _ => hfi i]
    _ ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ i, c i := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hc i) (by positivity)
omit [IsProbabilityMeasure P] in
/-- The third moment of the supremum norm on `Fin n → ℝ` from the coordinates. -/
theorem integral_norm_pi_pow_three_le {n : ℕ} {x : Ω → Fin n → ℝ} (hxm : Measurable x)
    (h3 : ∀ p : Fin n, Integrable (fun ω => |x ω p| ^ 3) P) {c : Fin n → ℝ}
    (hc : ∀ p : Fin n, ∫ ω, |x ω p| ^ 3 ∂P ≤ c p) :
    ∫ ω, ‖x ω‖ ^ 3 ∂P ≤ (n : ℝ) ^ 2 * ∑ p, c p := by
  have hdom : Integrable (fun ω => (n : ℝ) ^ 2 * ∑ p : Fin n, |x ω p| ^ 3) P :=
    (MeasureTheory.integrable_finsetSum _ fun p _ => h3 p).const_mul _
  have hpt : ∀ ω, ‖x ω‖ ^ 3 ≤ (n : ℝ) ^ 2 * ∑ p : Fin n, |x ω p| ^ 3 := fun ω =>
    cube_norm_pi_le_sum_abs_cube (x ω)
  have hint : Integrable (fun ω => ‖x ω‖ ^ 3) P := by
    refine hdom.mono' (hxm.norm.pow_const 3).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
    exact hpt ω
  calc ∫ ω, ‖x ω‖ ^ 3 ∂P ≤ ∫ ω, (n : ℝ) ^ 2 * ∑ p : Fin n, |x ω p| ^ 3 ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = (n : ℝ) ^ 2 * ∑ p : Fin n, ∫ ω, |x ω p| ^ 3 ∂P := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum _ fun p _ => h3 p]
    _ ≤ (n : ℝ) ^ 2 * ∑ p : Fin n, c p :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hc p) (by positivity)
end GenericThird

section VectorThird

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in
/-- **Third absolute moment of the martingale part's increment.** -/
theorem integral_abs_vectorItoMartingale_sub_pow_three_le (p : Fin n) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u < v) :
    ∫ ω, |vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω| ^ 3 ∂P
      ≤ (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
        * ((v - u) * Real.sqrt (v - u)))) := by
  have hk : ∀ k : Fin d,
      Integrable (fun ω => |coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω| ^ 3) P
        ∧ ∫ ω, |coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω| ^ 3 ∂P
          ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * ((v - u) * Real.sqrt (v - u)) :=
    fun k => _root_.Prove2MeSourceProof.h_4ef3e5b73189336215f644cf (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
      (hHs p k) hC0 (hCH p k) hu huv
  have hbound := integral_abs_sum_pow_three_le (P := P)
    (f := fun (k : Fin d) ω => coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
      - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
    (fun k => (measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v).sub
      (measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u))
    (fun k => (hk k).1) (fun k => (hk k).2)
  simp_rw [vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs p u v]
  refine hbound.trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
include hC0 hCH in
/-- **Third absolute moment of a coordinate of the increment.** -/
theorem integral_abs_vectorItoProcess_sub_pow_three_le (X₀ : Ω → Fin n → ℝ)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ m, Measurable (Function.uncurry (bdrift m)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    (p : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    ∫ ω, |vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω p
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω p| ^ 3 ∂P
      ≤ 4 * ((B * (v - u)) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * ((v - u) * Real.sqrt (v - u))))) := by
  have hDint := integrable_abs_drift_pow_three (P := P) (bdrift p) (hbm p) hB0 (hB p) huv.le
  have hMint := integrable_abs_vectorItoMartingale_sub_pow_three W ℱ hcoord H hHm hHp hHs
    hC0 hCH p hu huv
  have hDmeas : Measurable fun ω : Ω => ∫ s in Set.Ioc u v, bdrift p ω s ∂volume :=
    measurable_setIntegral_Ioc (hbm p) _ _
  have hMmeas := (measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v).sub
    (measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u)
  have hDle : ∫ ω, |∫ s in Set.Ioc u v, bdrift p ω s ∂volume| ^ 3 ∂P ≤ (B * (v - u)) ^ 3 := by
    have hDbd : ∀ ω : Ω, |∫ s in Set.Ioc u v, bdrift p ω s ∂volume| ≤ B * (v - u) :=
      fun ω => _root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a (Measurable.of_uncurry_left (hbm p)) (hB p ω) huv.le
    calc ∫ ω, |∫ s in Set.Ioc u v, bdrift p ω s ∂volume| ^ 3 ∂P
        ≤ ∫ _ω : Ω, (B * (v - u)) ^ 3 ∂P :=
          MeasureTheory.integral_mono hDint (MeasureTheory.integrable_const _)
            (fun ω => pow_le_pow_left₀ (abs_nonneg _) (hDbd ω) 3)
      _ = (B * (v - u)) ^ 3 := by simp
  have hMle := integral_abs_vectorItoMartingale_sub_pow_three_le W ℱ hcoord H hHm hHp hHs
    hC0 hCH p hu huv
  simp_rw [vectorItoProcess_sub W ℱ hcoord H hHm hHp hHs X₀ bdrift hbm hB hu huv.le p]
  refine (_root_.Prove2MeSourceProof.h_5e84cb76e3723bb35ee92ba4 hDint hMint
    (integrable_abs_add_pow_three hDmeas hMmeas hDint hMint)).trans ?_
  linarith
include hC0 hCH in
/-- **Third moment of the norm of the increment.** -/
theorem integral_norm_vectorItoProcess_sub_pow_three_le (X₀ : Ω → Fin n → ℝ)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ m, Measurable (Function.uncurry (bdrift m)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    ∫ ω, ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 3 ∂P
      ≤ (n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((B * (v - u)) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * ((v - u) * Real.sqrt (v - u))))))) := by
  have h3 : ∀ p : Fin n, Integrable (fun ω =>
      |(vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω) p| ^ 3) P := fun p =>
    integrable_abs_vectorItoProcess_sub_pow_three W ℱ hcoord H hHm hHp hHs hC0 hCH X₀ bdrift
      hbm hB0 hB p hu huv
  have hc : ∀ p : Fin n, ∫ ω, |(vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω) p| ^ 3 ∂P
      ≤ 4 * ((B * (v - u)) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * ((v - u) * Real.sqrt (v - u))))) := fun p =>
    integral_abs_vectorItoProcess_sub_pow_three_le W ℱ hcoord H hHm hHp hHs hC0 hCH X₀ bdrift
      hbm hB0 hB p hu huv
  refine (integral_norm_pi_pow_three_le
    (_root_.Prove2MeSourceProof.h_5772ba714260d30ff9581e64 W ℱ hcoord H hHm hHp hHs X₀ bdrift hbm hB hu huv.le)
    h3 hc).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
end VectorThird

end LevyStochCalc.Brownian.Ito


