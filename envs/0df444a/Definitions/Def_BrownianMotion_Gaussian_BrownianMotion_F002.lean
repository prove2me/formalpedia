-- Prove2me | Definitions.Def_BrownianMotion_Gaussian_BrownianMotion_F002
-- name    : BrownianMotion_Gaussian_BrownianMotion_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:04:32.050618+00:00
-- url     : https://prove2.me/theorems/00bc7954-d728-418b-a664-5c1f5353dd24
-- title:
--   Source declarations: BrownianMotion.Gaussian.BrownianMotion
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Gaussian.BrownianMotion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Gaussian_BrownianMotion_F001
import Definitions.Def_SourceProof_e7c6965306a3c071166977c4

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Brownian motion

-/

@[expose] public section

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

namespace Finset

/-! ### Indexing the elements of a finset in order -/

variable [LinearOrder T] (I : Finset T)

section Bot

variable [Bot T]

end Bot

end Finset

namespace ProbabilityTheory

section Increments

/-! ### Independent increments -/

end Increments

section IsPreBrownianReal

variable (X : ℝ≥0 → Ω → ℝ)

variable {X} {P : Measure Ω}

end IsPreBrownianReal

section IsBrownianReal

variable (X : ℝ≥0 → Ω → ℝ)

variable {X}

end IsBrownianReal

-- for blueprint

-- for blueprint

section Measure

section ContinuousMap.MeasurableSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma ContinuousMap.measurableSpace_eq_iSup_comap_eval
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    (inferInstance : MeasurableSpace C(X, Y))
      = ⨆ a : X, (inferInstance : MeasurableSpace Y).comap fun b ↦ b a := by
  simp_rw [BorelSpace.measurable_eq, _root_.Prove2MeSourceProof.h_e7c6965306a3c071166977c4]
lemma ContinuousMap.measurable_iff_eval {α : Type*} [MeasurableSpace α]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (g : α → C(X, Y)) :
    Measurable g ↔ ∀ (x : X), Measurable fun (a : α) ↦ g a x := by
  suffices Measurable[_, ⨆ a : X, (inferInstance : MeasurableSpace Y).comap fun b ↦ b a] g ↔
      ∀ (x : X), Measurable fun (a : α) ↦ g a x by
    convert this
    exact ContinuousMap.measurableSpace_eq_iSup_comap_eval
  simp_rw [measurable_iff_comap_le, MeasurableSpace.comap_iSup, iSup_le_iff,
    MeasurableSpace.comap_comp, Function.comp_def]
end ContinuousMap.MeasurableSpace

def MeasurableEquiv.continuousMap : {f : ℝ≥0 → ℝ // Continuous f} ≃ᵐ C(ℝ≥0, ℝ) where
  toFun := fun f ↦ ContinuousMap.mk f.1 f.2
  invFun := fun f ↦ ⟨f, f.continuous⟩
  left_inv f := rfl
  right_inv f := rfl
  measurable_toFun := by
    simp only [Equiv.coe_fn_mk]
    rw [ContinuousMap.measurable_iff_eval]
    intro x
    simp only [ContinuousMap.coe_mk]
    revert x
    rw [← measurable_pi_iff]
    exact measurable_subtype_coe
  measurable_invFun := by
    simp only [Equiv.coe_fn_symm_mk]
    refine Measurable.subtype_mk ?_
    rw [measurable_pi_iff]
    exact fun _ ↦ Continuous.measurable (by fun_prop)
noncomputable
def wienerMeasure : Measure C(ℝ≥0, ℝ) := wienerMeasureAux.map MeasurableEquiv.continuousMap
end Measure

end ProbabilityTheory


