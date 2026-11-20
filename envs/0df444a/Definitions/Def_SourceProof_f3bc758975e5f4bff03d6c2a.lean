-- Prove2me | Definitions.Def_SourceProof_f3bc758975e5f4bff03d6c2a
-- name    : SourceProof_f3bc758975e5f4bff03d6c2a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:34:24.283019+00:00
-- url     : https://prove2.me/theorems/0c9c493d-9bce-44ba-8521-f41f203117cb
-- title:
--   LevyStochCalc source module: SourceProof_f3bc758975e5f4bff03d6c2a
-- statement:
--   The original source theorem `MeasureTheory.isProjectiveLimit_projectiveLimit` comes from the `KolmogorovExtension4.KolmogorovExtension` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_KolmogorovExtension4_KolmogorovExtension_F000

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

@[expose] public section

open Set

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (Π j : J, α j)}

section InnerRegular

variable [∀ i, TopologicalSpace (α i)] [∀ i, OpensMeasurableSpace (α i)]
  [∀ i, SecondCountableTopology (α i)] [∀ I, IsFiniteMeasure (P I)]

local notation "Js" => measurableCylinders.finset

local notation "As" => measurableCylinders.set

end InnerRegular

section Polish

variable [∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)]
  [∀ i, PolishSpace (α i)] [∀ I, IsFiniteMeasure (P I)]


theorem _root_.Prove2MeSourceProof.h_f3bc758975e5f4bff03d6c2a (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveLimit (projectiveLimit P hP) P := by
  intro J
  ext s hs
  rw [Measure.map_apply _ hs]
  swap; · exact J.measurable_restrict
  have h_mem : J.restrict ⁻¹' s ∈ measurableCylinders α :=
    (mem_measurableCylinders _).mpr ⟨J, s, hs, rfl⟩
  calc
    (MeasureTheory.projectiveLimit P hP) (J.restrict ⁻¹' s) =
        (projectiveFamilyContent hP) (J.restrict ⁻¹' s) := by
      exact AddContent.measure_eq (projectiveFamilyContent hP)
        isSetSemiring_measurableCylinders
        generateFrom_measurableCylinders.symm
        (MeasureTheory.projectiveFamilyContent_iUnion_le_sum hP) h_mem
    _ = (P J) s := projectiveFamilyContent_congr hP (_ ⁻¹' _) rfl hs
end Polish

end MeasureTheory


