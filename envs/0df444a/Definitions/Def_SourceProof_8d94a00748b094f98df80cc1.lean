-- Prove2me | Definitions.Def_SourceProof_8d94a00748b094f98df80cc1
-- name    : SourceProof_8d94a00748b094f98df80cc1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:59:42.211941+00:00
-- url     : https://prove2.me/theorems/718fe3c9-57b7-4c8e-8c41-7a1c799ab6cc
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Martingale_SquareCompensator_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated square of a square-integrable martingale

For a square-integrable martingale `M` and an adapted integrable process `A`, the process
`M² − A` is a martingale as soon as the increments satisfy the set-level identity
`∫_B (M_t − M_s)² = ∫_B (A_t − A_s)` for every `s ≤ t` and every `B ∈ ℱ_s`: the cross term
`∫_B M_s M_t` equals `∫_B M_s²` by the martingale property, so the identity says exactly that
`∫_B (M_t² − A_t) = ∫_B (M_s² − A_s)`.
-/

open MeasureTheory Filter

namespace LevyStochCalc.Martingale

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {μ : Measure Ω} [IsFiniteMeasure μ] {M A : ι → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_8d94a00748b094f98df80cc1 (hM : Martingale M ℱ μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hA : StronglyAdapted ℱ A) (hAint : ∀ t, Integrable (A t) μ)
    (h : ∀ s t, s ≤ t → ∀ B, MeasurableSet[ℱ s] B →
      ∫ ω in B, (M t ω - M s ω) ^ 2 ∂μ = ∫ ω in B, (A t ω - A s ω) ∂μ) :
    Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ := by
  refine ⟨fun t => ((hM.stronglyAdapted t).pow 2).sub (hA t), fun s t hst => ?_⟩
  have hm : ℱ s ≤ mΩ := ℱ.le s
  have hint : ∀ u, Integrable (fun ω => (M u ω) ^ 2 - A u ω) μ := fun u =>
    (hM2 u).integrable_sq.sub (hAint u)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hint t)
    (fun B _ _ => (hint s).integrableOn) (fun B hB _ => ?_)
    (((hM.stronglyAdapted s).pow 2).sub (hA s)).aestronglyMeasurable).symm
  have ht2 : IntegrableOn (fun ω => (M t ω) ^ 2) B μ := (hM2 t).integrable_sq.integrableOn
  have hs2 : IntegrableOn (fun ω => (M s ω) ^ 2) B μ := (hM2 s).integrable_sq.integrableOn
  have hAt : IntegrableOn (A t) B μ := (hAint t).integrableOn
  have hAs : IntegrableOn (A s) B μ := (hAint s).integrableOn
  have key := h s t hst B hB
  rw [LevyStochCalc.Martingale.setIntegral_increment_sq hM hM2 hst hB, integral_sub hAt hAs] at key
  rw [integral_sub ht2 hAt, integral_sub hs2 hAs]
  linarith
end LevyStochCalc.Martingale


