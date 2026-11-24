-- Prove2me | Definitions.Def_SourceProof_be0b26cebaa157c758248f0a
-- name    : SourceProof_be0b26cebaa157c758248f0a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:37.457408+00:00
-- url     : https://prove2.me/theorems/d047c092-ebee-4ce1-afc0-765f3d3bc0c8
-- title:
--   StochLean source theorem: MeasureTheory.martingale_of_tendstoInMeasure_uniformIntegrable

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Coordinatewise probability limits of uniformly integrable martingales

Uniform integrability is required across the approximating sequence at each
fixed time, not uniformly over the whole time axis.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω T : Type*} [Preorder T] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration T mΩ}
  [SigmaFiniteFiltration P F] {X : ℕ → T → Ω → ℝ} {Y : T → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_be0b26cebaa157c758248f0a
    (hX : ∀ n, Martingale (X n) F P) (ha : StronglyAdapted F Y)
    (hui : ∀ t, UniformIntegrable (fun n ↦ X n t) 1 P)
    (hu : ∀ t, TendstoInMeasure P (fun n ↦ X n t) atTop (Y t)) : Martingale Y F P := by
  have hi (t : T) : Integrable (Y t) P := (hui t).integrable_of_tendstoInMeasure (hu t)
  have hLp (t : T) : Tendsto (fun n ↦ eLpNorm (X n t - Y t) 1 P) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl (by simp) (hui t).1
      (memLp_one_iff_integrable.mpr (hi t)) (hui t).2.1 (hu t)
  refine ⟨ha, fun s t hst ↦ ?_⟩
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hi t)
    (fun _ _ _ ↦ (hi s).integrableOn) ?_ (ha s).aestronglyMeasurable
  intro A hA _
  have hs := tendsto_setIntegral_of_L1' (Y s) (hi s).aestronglyMeasurable
    (Eventually.of_forall (fun n ↦ (hX n).integrable s)) (hLp s) A
  have ht := tendsto_setIntegral_of_L1' (Y t) (hi t).aestronglyMeasurable
    (Eventually.of_forall (fun n ↦ (hX n).integrable t)) (hLp t) A
  have heq (n : ℕ) : (∫ ω in A, X n s ω ∂P) = ∫ ω in A, X n t ω ∂P :=
    (hX n).setIntegral_eq hst hA
  exact tendsto_nhds_unique hs (ht.congr' (Eventually.of_forall fun n ↦ (heq n).symm))
end MeasureTheory


