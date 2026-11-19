-- Prove2me | Definitions.Def_SourceProof_2f392b324cd7c71a924efcc1
-- name    : SourceProof_2f392b324cd7c71a924efcc1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:55:36.509997+00:00
-- url     : https://prove2.me/theorems/a6a3033c-7296-4ba7-ae3f-f4ab4911ca78
-- title:
--   LevyStochCalc source proof: isCompactSystem_closedCompactCylinders
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_KolmogorovExtension4_CompactSystem_F000

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

@[expose] public section

open Set MeasureTheory

section definition

variable {α : Type*} {p : Set α → Prop} {C : ℕ → Set α}

end definition

section ClosedCompactCylinders

/-! We prove that the `closedCompactCylinders` are a compact system. -/

variable {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {s : ℕ → Set (Π i, α i)}

local notation "Js" => closedCompactCylinders.finset
local notation "As" => closedCompactCylinders.set

section AllProj

end AllProj

section projCylinder

end projCylinder

section piCylinderSet

end piCylinderSet


theorem _root_.Prove2MeSourceProof.h_2f392b324cd7c71a924efcc1 : IsCompactSystem (closedCompactCylinders α) := by
  by_cases hα : ∀ i, Nonempty (α i)
  swap
  · have : IsEmpty (Π i, α i) := isEmpty_pi.mpr (by simpa using hα)
    refine fun s hs h ↦ ⟨0, ?_⟩
    simp only [dissipate_zero_nat]
    refine Set.eq_empty_of_isEmpty _
  refine IsCompactSystem.of_nonempty_iInter fun s hs h_nonempty ↦ ?_
  have h' n : (dissipate (projCylinder hs) n).Nonempty := by
    simp_rw [dissipate, ← preimage_projCylinder hs, ← preimage_iInter] at h_nonempty
    exact nonempty_of_nonempty_preimage (h_nonempty n)
  have h_non := nonempty_iInter_projCylinder hs (fun n ↦ ?_) h'
  swap
  · specialize h' n
    contrapose! h'
    refine Set.eq_empty_of_subset_empty ((dissipate_subset le_rfl).trans_eq ?_)
    contrapose! h'
    rwa [nonempty_projCylinder_iff] at h'
  simp_rw [← preimage_projCylinder hs, ← preimage_iInter]
  rwa [(surjective_proj_allProj hs).nonempty_preimage]
end ClosedCompactCylinders


