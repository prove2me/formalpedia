-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_archTypeFamily_mem_archCutSubmodule_of_mem_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c1440318-2685-5fd9-8ef4-7e40beedefc4

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_archTypeFamily_mem_archCutSubmodule_of_mem_isCuspConstituent

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

namespace Ws47
namespace C7

def juxt (t₁ t₂ : ArchTypeFamily ℚ) : ArchTypeFamily ℚ where
  card := fun w => t₁.card w + t₂.card w
  rep := fun w => Fin.append (t₁.rep w) (t₂.rep w)

theorem archCutSubmodule_le_juxt_left (t₁ t₂ : ArchTypeFamily ℚ) :
    archCutSubmodule ℚ t₁ ≤ archCutSubmodule ℚ (juxt t₁ t₂) := by
  intro f hf
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  have hle : (⨆ i, archTypeSubmoduleAt ℚ w (t₁.rep w i)) ≤ ⨆ j, archTypeSubmoduleAt ℚ w ((juxt t₁ t₂).rep w j) := by
    refine iSup_le fun i => ?_
    have : archTypeSubmoduleAt ℚ w (t₁.rep w i) = archTypeSubmoduleAt ℚ w ((juxt t₁ t₂).rep w (Fin.castAdd (t₂.card w) i)) := by
      simp only [juxt, Fin.append_left]
    rw [this]
    exact le_iSup (fun j => archTypeSubmoduleAt ℚ w ((juxt t₁ t₂).rep w j)) _
  exact hle (hf w)

theorem archCutSubmodule_le_juxt_right (t₁ t₂ : ArchTypeFamily ℚ) :
    archCutSubmodule ℚ t₂ ≤ archCutSubmodule ℚ (juxt t₁ t₂) := by
  intro f hf
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  have hle : (⨆ i, archTypeSubmoduleAt ℚ w (t₂.rep w i)) ≤ ⨆ j, archTypeSubmoduleAt ℚ w ((juxt t₁ t₂).rep w j) := by
    refine iSup_le fun i => ?_
    have : archTypeSubmoduleAt ℚ w (t₂.rep w i) = archTypeSubmoduleAt ℚ w ((juxt t₁ t₂).rep w (Fin.natAdd (t₁.card w) i)) := by
      simp only [juxt, Fin.append_right]
    rw [this]
    exact le_iSup (fun j => archTypeSubmoduleAt ℚ w ((juxt t₁ t₂).rep w j)) _
  exact hle (hf w)

end Ws47.C7

open Ws47.C7 in
theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφV : φ ∈ V) :
    ∃ tys : ArchTypeFamily ℚ, φ ∈ archCutSubmodule ℚ tys := by
  classical
  have hmem : φ ∈ CuspidalConstituent.cuspKFiniteSubmodule ℚ (productionPinsGeneral ℚ) ξ := hV.1.le hφV
  unfold CuspidalConstituent.cuspKFiniteSubmodule at hmem
  refine Submodule.span_induction (p := fun ψ _ => ∃ tys : ArchTypeFamily ℚ, ψ ∈ archCutSubmodule ℚ tys) ?_ ?_ ?_ ?_ hmem
  · rintro ψ ⟨-, -, tys, hψ⟩
    exact ⟨tys, hψ⟩
  · exact ⟨ArchTypeFamily.ofChar ℚ fun v => archWeightCharAt (isReal_infinitePlace_rat v) 0, Submodule.zero_mem _⟩
  · rintro ψ₁ ψ₂ - - ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
    exact ⟨juxt t₁ t₂, Submodule.add_mem _ (archCutSubmodule_le_juxt_left t₁ t₂ h₁) (archCutSubmodule_le_juxt_right t₁ t₂ h₂)⟩
  · rintro a ψ - ⟨t, h⟩
    exact ⟨t, Submodule.smul_mem _ a h⟩

end S_AutomorphicForm_CuspidalConstituent_exists_archTypeFamily_mem_archCutSubmodule_of_mem_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_archTypeFamily_mem_archCutSubmodule_of_mem_isCuspConstituent (solution)
