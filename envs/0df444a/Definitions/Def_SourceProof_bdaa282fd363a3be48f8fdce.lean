-- Prove2me | Definitions.Def_SourceProof_bdaa282fd363a3be48f8fdce
-- name    : SourceProof_bdaa282fd363a3be48f8fdce
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:18:19.799087+00:00
-- url     : https://prove2.me/theorems/23d8a2b4-4269-4419-bf4d-5b7ccd19fd91
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Square integrability of the Picard integrands along a state process

Linear growth of the coefficients, read off the Lipschitz hypothesis by comparison with the
state `0`, turns the bounds at that single state recorded by `IsRegular` into bounds along a
state process: whenever the state has finite energy over every horizon, the drift, diffusion
and jump integrands evaluated along it are square integrable at every horizon, and a member of
the process space frozen at `T` has that energy. Composing a jointly measurable coefficient
with a measurable, respectively progressively measurable, state process supplies the matching
measurability of the integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce {n d : ℕ} {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZsq : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (Z s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have key : ∀ x : ℝ, ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (x ^ 2) := LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real
  -- the pointwise linear-growth bound, in extended form
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖coeffs.σ s (Z s ω) i j‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    have h1 : ENNReal.ofReal (2 * (coeffs.σ s 0 i j) ^ 2)
        = 2 * (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2 := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), key, ENNReal.ofReal_ofNat]
    have h2 : ENNReal.ofReal (2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2))
        = ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
      rw [show 2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2)
          = (2 * L ^ 2) * ∑ i', (Z s ω i') ^ 2 by ring,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * L ^ 2),
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      exact congrArg _ (Finset.sum_congr rfl fun i' _ => (key _).symm)
    calc (‖coeffs.σ s (Z s ω) i j‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((coeffs.σ s (Z s ω) i j) ^ 2) := key _
      _ ≤ ENNReal.ofReal (2 * (coeffs.σ s 0 i j) ^ 2
            + 2 * (L ^ 2 * ∑ i', (Z s ω i') ^ 2)) :=
          ENNReal.ofReal_le_ofReal (LevyStochCalc.Ito.Picard.sq_sigma_le coeffs hLip s _ i j)
      _ = 2 * (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), h1, h2]
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => hpt ω s) ?_
  -- measurability of the two pieces
  have hσ0 : Measurable fun s : ℝ => (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2 := by
    have : Measurable fun s : ℝ => coeffs.σ s 0 i j :=
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        (hReg.2.1.comp (measurable_id.prodMk measurable_const))))
    exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hXi : ∀ i' : Fin n, Measurable fun p : Ω × ℝ => Z p.2 p.1 i' := fun i' =>
    (measurable_pi_apply i').comp
      (hZm.comp (measurable_snd.prodMk measurable_fst))
  have hBjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2) :=
    (Finset.measurable_sum _ fun i' _ =>
      ((hXi i').nnnorm.coe_nnreal_ennreal).pow_const 2).const_mul _
  -- split the sum
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (2 * (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T', 2 * (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T',
            ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun ω => MeasureTheory.lintegral_add_left (hσ0.const_mul 2) _
  rw [lintegral_congr hinner,
    MeasureTheory.lintegral_add_left measurable_const _]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · -- the state-zero term: constant in `ω`, finite by `IsRegular`
    rw [MeasureTheory.lintegral_const, measure_univ, mul_one,
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    refine ENNReal.mul_lt_top (by simp) ?_
    refine lt_of_le_of_lt (MeasureTheory.setLIntegral_mono' measurableSet_Icc
      fun s _ => ?_) (hReg.2.2.2.2.1 T' hT')
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i' => ∑ j', (‖coeffs.σ s 0 i' j'‖₊ : ℝ≥0∞) ^ 2)
      (fun _ _ => by simp) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' => (‖coeffs.σ s 0 i j'‖₊ : ℝ≥0∞) ^ 2)
      (fun _ _ => by simp) (Finset.mem_univ j)
  · -- the state term: the frozen process's horizon bound
    have hconst : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          ENNReal.ofReal (2 * L ^ 2) * ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ENNReal.ofReal (2 * L ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T',
            ∑ i', (‖Z s ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
      fun ω => MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [lintegral_congr hconst,
      MeasureTheory.lintegral_const_mul' _ _
        (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 * L ^ 2) ≠ ⊤)]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact hZsq T'
end LevyStochCalc.Ito.Picard


