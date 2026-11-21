-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PRPBrownian_F000
-- name    : LevyStochCalc_Brownian_PRPBrownian_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:23:08.696686+00:00
-- url     : https://prove2.me/theorems/d3b936d0-9c9f-4848-8d66-0a8982225ede
-- title:
--   Source declarations: LevyStochCalc.Brownian.PRPBrownian
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PRPBrownian. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_SortedGrid_F001
import Definitions.Def_LevyStochCalc_Brownian_CylinderCharacters_F000
import Definitions.Def_LevyStochCalc_Brownian_PRPMultidim_F000
import Definitions.Def_LevyStochCalc_Probability_AugmentationMeasurable_F000
import Definitions.Def_SourceProof_527e9e3b2fcbd8b1a9548140
import Definitions.Def_SourceProof_8ff28f8ca301aab034421e84

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The orthogonal complement of the Brownian Itô integrals

Sorting the times of a finite family of coordinate values into an increasing grid turns a
cylinder character of a multidimensional Brownian motion into a character of the values along a
grid, so a square-integrable weight of mean zero orthogonal to every coordinate's Itô integrals
is orthogonal to every cylinder character. A weight measurable for the natural filtration at a
time `T` is therefore almost everywhere zero.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The values of a multidimensional Brownian motion at the nonpositive times of a finite family
of (coordinate, time) pairs vanish almost surely. -/
theorem ae_forall_eq_zero_of_nonpos (W : Multidim.MultidimBrownianMotion P d) {T : ℝ}
    (F : Finset (Fin d × Set.Iic T)) :
    ∀ᵐ ω ∂P, ∀ p ∈ F, (p.2 : ℝ) ≤ 0 → (W.W p.1).W (p.2 : ℝ) ω = 0 := by
  rw [Filter.eventually_all_finset]
  intro p _
  rcases lt_or_ge ((p.2 : ℝ)) 0 with h | h
  · filter_upwards [(W.W p.1).negative_zero _ h] with ω hω _
    exact hω
  · filter_upwards [(W.W p.1).initial_zero] with ω hω hle
    rw [le_antisymm hle h]
    exact hω
/-- **Cylinder characters.** A square-integrable weight of mean zero, orthogonal to every
coordinate's Itô integrals, is orthogonal to every character of a finite family of coordinate
values. -/
theorem pairing_char_cylinder_eq_zero (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) {T : ℝ} (F : Finset (Fin d × Set.Iic T)) (w : F → ℝ) :
    ∫ ω, Complex.exp (((∑ p : F, (W.W p.1.1).W (p.1.2 : ℝ) ω * w p : ℝ) : ℂ) * Complex.I)
      * Z ω ∂P = 0 := by
  have hlt : ∀ k, k < (Analysis.posTimes F).card →
      Analysis.sortedGrid (Analysis.posTimes F) k
        < Analysis.sortedGrid (Analysis.posTimes F) (k + 1) := fun k hk =>
    Analysis.sortedGrid_lt_succ _ (fun _ hx => Analysis.pos_of_mem_posTimes hx) hk
  have hkey := _root_.Prove2MeSourceProof.h_8ff28f8ca301aab034421e84 W ℱ hℱi hℱB hℱ0 hnull
    (τ := Analysis.sortedGrid (Analysis.posTimes F))
    (Analysis.sortedGrid_zero (Analysis.posTimes F)) hZm hZ2 hperp hZ0
    (fun k i => Analysis.weightAt F w (Analysis.sortedGrid (Analysis.posTimes F) k) i)
    (Analysis.posTimes F).card hlt
  refine Eq.trans (integral_congr_ae ?_) hkey
  filter_upwards [ae_forall_eq_zero_of_nonpos W F] with ω hω
  have heq : (∑ p : F, (W.W p.1.1).W (p.1.2 : ℝ) ω * w p)
      = ∑ i, ∑ k ∈ Finset.Ico 1 ((Analysis.posTimes F).card + 1),
          Analysis.weightAt F w (Analysis.sortedGrid (Analysis.posTimes F) k) i
            * (W.W i).W (Analysis.sortedGrid (Analysis.posTimes F) k) ω :=
    _root_.Prove2MeSourceProof.h_527e9e3b2fcbd8b1a9548140 F w (fun i t => (W.W i).W t ω)
      (fun p hp => hω p.1 p.2 hp) (Finset.Subset.refl _)
      fun _ hx => Analysis.pos_of_mem_posTimes hx
  rw [heq, mul_comm]
/-- **The orthogonal complement of the Brownian Itô integrals is trivial.** A square-integrable
weight of mean zero, measurable for the natural filtration of a multidimensional Brownian motion
at a time `T` and orthogonal to every coordinate's Itô integrals, vanishes almost everywhere. -/
theorem ae_eq_zero_of_perpItoIntegrals (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) {T : ℝ}
    (hZT : StronglyMeasurable[W.naturalFiltration T] Z) :
    Z =ᵐ[P] 0 :=
  Multidim.MultidimBrownianMotion.ae_eq_zero_of_integral_char_cylinder W T
    (hZ2.integrable (by norm_num)) hZT
    fun F w => pairing_char_cylinder_eq_zero W ℱ hℱi hℱB hℱ0 hnull hZm hZ2 hperp hZ0 F w
end LevyStochCalc.Brownian.Ito


