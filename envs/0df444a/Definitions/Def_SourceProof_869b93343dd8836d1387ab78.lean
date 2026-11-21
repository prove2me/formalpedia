-- Prove2me | Definitions.Def_SourceProof_869b93343dd8836d1387ab78
-- name    : SourceProof_869b93343dd8836d1387ab78
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:22:19.248867+00:00
-- url     : https://prove2.me/theorems/fbabc5a4-5b96-40ed-a4b8-07d52b23178f
-- title:
--   LevyStochCalc source module: SourceProof_869b93343dd8836d1387ab78
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.lintegral_density_eq` comes from the `LevyStochCalc.BSDEJ.PicardContractionNorm` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F000

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

variable {P : Measure Ω} {ν : Measure E} {β T : ℝ}

variable [SigmaFinite ν]

omit [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_869b93343dd8836d1387ab78 [SFinite P] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, density ν Y Z U ω s ∂volume ∂P
      = Brownian.Ito.energy P T (fun ω s => Y s ω)
        + (∑ j, Brownian.Ito.energy P T (fun ω s => Z s ω j))
        + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) := by
  classical
  have hA := LevyStochCalc.BSDEJ.Solves.measurable_uncurry_sq_value hYm
  have hB : ∀ j : Fin d, Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2) := fun j => LevyStochCalc.BSDEJ.Solves.measurable_uncurry_sq_value (hZm j)
  have hA' : ∀ ω : Ω, Measurable fun s : ℝ => (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 := fun ω =>
    hA.comp (measurable_const.prodMk measurable_id)
  have hB' : ∀ (j : Fin d) (ω : Ω), Measurable fun s : ℝ => (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 :=
    fun j ω => (hB j).comp (measurable_const.prodMk measurable_id)
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, LevyStochCalc.BSDEJ.Solves.density ν Y Z U ω s ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + (∑ j, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume := by
    intro ω
    have h12 : Measurable fun s : ℝ =>
        (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 :=
      (hA' ω).add (Finset.measurable_sum _ fun j _ => hB' j ω)
    simp only [LevyStochCalc.BSDEJ.Solves.density]
    rw [lintegral_add_left h12, lintegral_add_left (hA' ω),
      lintegral_finsetSum _ fun j _ => hB' j ω]
  have hoA : Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume := hA.lintegral_prod_right'
  have hoB : ∀ j : Fin d, Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun j => (hB j).lintegral_prod_right'
  have ho12 : Measurable fun ω : Ω => (∫⁻ s in Set.Icc (0 : ℝ) T, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      + ∑ j, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    hoA.add (Finset.measurable_sum _ fun j _ => hoB j)
  rw [lintegral_congr hinner, lintegral_add_left ho12, lintegral_add_left hoA,
    lintegral_finsetSum _ fun j _ => hoB j]
  rfl
end Norm

end LevyStochCalc.BSDEJ.Solves


