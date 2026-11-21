-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F000
-- name    : LevyStochCalc_BSDEJ_PicardContractionNorm_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:16:27.510578+00:00
-- url     : https://prove2.me/theorems/464ee849-b8d8-407a-b294-9a6aee1efd4e
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardContractionNorm
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardContractionNorm. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardItoLevy_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentBackward_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentBackward_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponentially weighted norm of a triple

The exponentially weighted `L²` norm `wNorm` of a triple `(Y, Z, U)` over a horizon `[0, T]`
weights the squared value, the squared diffusion coordinates and the marked energy of the jump
integrand by `e^{βs}` and integrates them over the horizon and the sample space. Its integrand at
a sample point and a time is the pointwise energy density `density`; the norm is finite when the
value, the diffusion coordinates and the jump integrand have finite energy on the horizon, and it
is then the real integral over the horizon of the weighted sample energy density.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Norm

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {d : ℕ}

/-- The pointwise energy density of a triple `(Y, Z, U)`: the squared value, the sum of the
squared diffusion coordinates and the marked energy of the jump integrand. -/
noncomputable def density (ν : Measure E) (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ))
    (U : ℝ → Ω → E → ℝ) (ω : Ω) (s : ℝ) : ℝ≥0∞ :=
  (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 + ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
/-- The exponentially weighted `L²` norm of a triple `(Y, Z, U)` over the horizon `[0, T]`, with
weight `e^{βs}`. -/
noncomputable def wNorm (P : Measure Ω) (ν : Measure E) (β T : ℝ) (Y : ℝ → Ω → ℝ)
    (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (β * s)) *
    ((‖Y s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2
      + ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
variable {P : Measure Ω} {ν : Measure E} {β T : ℝ}

/-- The weighted norm is the weighted integral of the pointwise energy density. -/
theorem wNorm_eq_lintegral_density {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} :
    wNorm P ν β T Y Z U = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (Real.exp (β * s)) * density ν Y Z U ω s ∂volume ∂P := rfl
/-- Triples agreeing on the horizon have the same weighted norm. -/
theorem wNorm_congr_Icc {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)}
    {U₁ U₂ : ℝ → Ω → E → ℝ} (hY : ∀ s ∈ Set.Icc (0 : ℝ) T, Y₁ s = Y₂ s)
    (hZ : ∀ s ∈ Set.Icc (0 : ℝ) T, Z₁ s = Z₂ s) (hU : ∀ s ∈ Set.Icc (0 : ℝ) T, U₁ s = U₂ s) :
    wNorm P ν β T Y₁ Z₁ U₁ = wNorm P ν β T Y₂ Z₂ U₂ := by
  refine lintegral_congr fun ω => ?_
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [hY s hs, hZ s hs, hU s hs]
/-- Freezing the two value processes at the horizon does not change the weighted norm of the
difference of two triples. -/
theorem wNorm_clampT_sub_eq {Y₁ Y₂ : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} :
    wNorm P ν β T (fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω) Z U
      = wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) Z U :=
  wNorm_congr_Icc (fun s hs => by simp only [clampT_apply, min_eq_left hs.2])
    (fun _ _ => rfl) (fun _ _ => rfl)
variable [SigmaFinite ν]

/-- The squared value of a process, jointly in the sample point and the time. -/
theorem measurable_uncurry_sq_value {Y : ℝ → Ω → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω)) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => (‖Y s ω‖₊ : ℝ≥0∞) ^ 2) :=
  hYm.nnnorm.coe_nnreal_ennreal.pow_const 2
/-- The marked energy density of a jump integrand, jointly in the sample point and the time. -/
theorem measurable_uncurry_sq_jump {U : ℝ → Ω → E → ℝ}
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) :=
  ((hUm.nnnorm.coe_nnreal_ennreal.pow_const 2).comp (by fun_prop :
    Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
      (ν := ν)
/-- The pointwise energy density of a triple, jointly in the sample point and the time. -/
theorem measurable_uncurry_density {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    Measurable (Function.uncurry (density ν Y Z U)) :=
  ((measurable_uncurry_sq_value hYm).add
    (Finset.measurable_sum _ fun j _ => measurable_uncurry_sq_value (hZm j))).add
      (measurable_uncurry_sq_jump hUm)
/-- The sample energy density of a triple is measurable in time. -/
theorem measurable_lintegral_density [SFinite P] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    Measurable fun s : ℝ => ∫⁻ ω, density ν Y Z U ω s ∂P :=
  Measurable.lintegral_prod_left' (measurable_uncurry_density hYm hZm hUm)
omit [SigmaFinite ν] in
/-- At each time, the sample energy density splits into the energy of the value, the energies of
the diffusion coordinates and the marked energy of the jump integrand. -/
theorem lintegral_density_slice_eq {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) (s : ℝ) :
    ∫⁻ ω, density ν Y Z U ω s ∂P
      = (∫⁻ ω, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) + (∑ j, ∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P := by
  classical
  have hA : Measurable fun ω : Ω => (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 :=
    (measurable_uncurry_sq_value hYm).comp (measurable_id.prodMk measurable_const)
  have hB : ∀ j : Fin d, Measurable fun ω : Ω => (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 := fun j =>
    (measurable_uncurry_sq_value (hZm j)).comp (measurable_id.prodMk measurable_const)
  have h12 : Measurable fun ω : Ω => (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 :=
    hA.add (Finset.measurable_sum _ fun j _ => hB j)
  simp only [density]
  rw [lintegral_add_left h12, lintegral_add_left hA, lintegral_finsetSum _ fun j _ => hB j]
end Norm

end LevyStochCalc.BSDEJ.Solves


