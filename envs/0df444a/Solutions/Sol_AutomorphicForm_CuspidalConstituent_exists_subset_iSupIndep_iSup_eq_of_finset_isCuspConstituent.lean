-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/df19ad08-e80b-5ef4-b1e1-d41a5bae0df1

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
p2m_open "AutomorphicForm.CuspidalConstituent P2MW.S_AutomorphicForm_CuspidalConstituent_exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent.AutomorphicForm.CuspidalConstituent"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rightConv_add_left CarrierPins AdelicGL2 continuous_and_hasCompactSupport_of_isFactorizableTestFn"
namespace CuspidalConstituent
p2m_export "AutomorphicForm.CuspidalConstituent" "rightTranslate_add cuspKFiniteSubmodule IsCuspSubrep IsCuspConstituent isCuspSubrep_bot"
namespace DirectRefineProof
p2m_open "AutomorphicForm.CuspidalConstituent AutomorphicForm"

variable (F : Type) [Field F] [NumberField F] {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}

theorem continuous_of_mem_cuspKFiniteSubmodule {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, hc, -⟩
    exact hc
  · exact continuous_const
  · intro u w _ _ hu hw
    exact hu.add hw
  · intro c u _ hu
    exact hu.const_smul c

theorem isCuspSubrep_inf {V W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hV : IsCuspSubrep F pins ξ V) (hW : IsCuspSubrep F pins ξ W) : IsCuspSubrep F pins ξ (V ⊓ W) where
  le := inf_le_left.trans hV.le
  rightTranslate_fin_mem g hg φ hφ :=
    ⟨hV.rightTranslate_fin_mem g hg φ hφ.1, hW.rightTranslate_fin_mem g hg φ hφ.2⟩
  rightTranslate_arch_mem w k φ hφ :=
    ⟨hV.rightTranslate_arch_mem w k φ hφ.1, hW.rightTranslate_arch_mem w k φ hφ.2⟩
  rightConv_mem f tys hf hbi φ hφ :=
    ⟨hV.rightConv_mem f tys hf hbi φ hφ.1, hW.rightConv_mem f tys hf hbi φ hφ.2⟩

theorem isCuspSubrep_sup {V W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hV : IsCuspSubrep F pins ξ V) (hW : IsCuspSubrep F pins ξ W) : IsCuspSubrep F pins ξ (V ⊔ W) where
  le := sup_le hV.le hW.le
  rightTranslate_fin_mem g hg φ hφ := by
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hφ
    rw [rightTranslate_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hV.rightTranslate_fin_mem g hg v hv))
      (Submodule.mem_sup_right (hW.rightTranslate_fin_mem g hg w hw))
  rightTranslate_arch_mem pl k φ hφ := by
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hφ
    rw [rightTranslate_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hV.rightTranslate_arch_mem pl k v hv))
      (Submodule.mem_sup_right (hW.rightTranslate_arch_mem pl k w hw))
  rightConv_mem f tys hf hbi φ hφ := by
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hφ
    obtain ⟨hfc, hfK⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
    rw [rightConv_add_left F (continuous_of_mem_cuspKFiniteSubmodule F (hV.le hv))
      (continuous_of_mem_cuspKFiniteSubmodule F (hW.le hw)) hfc hfK]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hV.rightConv_mem f tys hf hbi v hv))
      (Submodule.mem_sup_right (hW.rightConv_mem f tys hf hbi w hw))

theorem isCuspSubrep_sSup_finset (𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h : ∀ W ∈ 𝒲, IsCuspSubrep F pins ξ W) :
    IsCuspSubrep F pins ξ (sSup (↑𝒲 : Set (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))) := by
  classical
  induction 𝒲 using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, sSup_empty]
    exact isCuspSubrep_bot F pins ξ
  | @insert a s ha ih =>
    rw [Finset.coe_insert, sSup_insert]
    exact isCuspSubrep_sup F (h a (Finset.mem_insert_self a s)) (ih fun W hW => h W (Finset.mem_insert_of_mem hW))

theorem inf_eq_bot_or_le {V S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hV : IsCuspConstituent F pins ξ V) (hS : IsCuspSubrep F pins ξ S) : V ⊓ S = ⊥ ∨ V ≤ S := by
  rcases hV.2.2 (V ⊓ S) (isCuspSubrep_inf F hV.1 hS) inf_le_left with h | h
  · exact Or.inl h
  · exact Or.inr (inf_eq_left.mp h)

theorem main (𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h𝒱 : ∀ V ∈ 𝒱, IsCuspConstituent F pins ξ V) :
    ∃ 𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)), 𝒲 ⊆ 𝒱 ∧
      sSupIndep (↑𝒲 : Set (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) ∧
      sSup (↑𝒲 : Set (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) = sSup (↑𝒱 : Set (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) := by
  classical
  induction 𝒱 using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by rw [Finset.coe_empty]; exact sSupIndep_empty, rfl⟩
  | @insert V 𝒱 hV ih =>
    obtain ⟨𝒲, h𝒲𝒱, hind, hsup⟩ := ih fun W hW => h𝒱 W (Finset.mem_insert_of_mem hW)
    have hVc : IsCuspConstituent F pins ξ V := h𝒱 V (Finset.mem_insert_self V 𝒱)
    have hSrep : IsCuspSubrep F pins ξ (sSup (↑𝒲 : Set (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))) :=
      isCuspSubrep_sSup_finset F 𝒲 fun W hW => (h𝒱 W (Finset.mem_insert_of_mem (h𝒲𝒱 hW))).1
    rcases inf_eq_bot_or_le F hVc hSrep with hbot | hle
    ·
      refine ⟨insert V 𝒲, Finset.insert_subset_insert V h𝒲𝒱, ?_, ?_⟩
      · intro a ha
        rw [Finset.coe_insert] at ha ⊢
        rcases Set.mem_insert_iff.mp ha with rfl | haW
        ·
          refine (disjoint_iff.mpr hbot).mono_right (sSup_le_sSup (Set.diff_subset_iff.mpr ?_))
          intro x hx
          simpa using hx
        ·
          have hD : Disjoint a (sSup ((↑𝒲 : Set (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) \ {a})) := hind haW
          have hle' : a ⊔ sSup ((↑𝒲 : Set (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) \ {a})
              ≤ sSup (↑𝒲 : Set (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) :=
            sup_le (le_sSup haW) (sSup_le_sSup Set.diff_subset)
          have hchase : Disjoint a (V ⊔ sSup ((↑𝒲 : Set (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) \ {a})) := by
            rw [Submodule.disjoint_def] at hD ⊢
            intro x hxa hx
            obtain ⟨v, hv, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
            have hv' : v ∈ V ⊓ sSup (↑𝒲 : Set (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) := by
              refine ⟨hv, hle' ?_⟩
              have hvd : v = (v + d) - d := (add_sub_cancel_right v d).symm
              rw [hvd]
              exact Submodule.sub_mem _ (Submodule.mem_sup_left hxa) (Submodule.mem_sup_right hd)
            rw [hbot] at hv'
            have hv0 : v = 0 := (Submodule.mem_bot ℂ).mp hv'
            rw [hv0, zero_add] at hxa ⊢
            exact hD d hxa hd
          refine hchase.mono_right ?_
          rw [← sSup_insert]
          refine sSup_le_sSup ?_
          rintro x ⟨hx1, hx2⟩
          rcases Set.mem_insert_iff.mp hx1 with rfl | hx𝒲
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ ⟨hx𝒲, hx2⟩
      · rw [Finset.coe_insert, Finset.coe_insert, sSup_insert, sSup_insert, hsup]
    ·
      refine ⟨𝒲, h𝒲𝒱.trans (Finset.subset_insert V 𝒱), hind, ?_⟩
      rw [Finset.coe_insert, sSup_insert, hsup]
      exact (sup_eq_right.mpr (hle.trans hsup.le)).symm

end AutomorphicForm.CuspidalConstituent.DirectRefineProof

open AutomorphicForm.CuspidalConstituent.DirectRefineProof in
theorem solution
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h𝒱 : ∀ V ∈ 𝒱, IsCuspConstituent F pins ξ V) :
    ∃ 𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)), 𝒲 ⊆ 𝒱 ∧
      iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) ∧
      (⨆ W ∈ 𝒲, W) = ⨆ V ∈ 𝒱, V := by
  obtain ⟨𝒲, h𝒲𝒱, hind, hsup⟩ := main F 𝒱 h𝒱
  refine ⟨𝒲, h𝒲𝒱, ?_, ?_⟩
  · exact (sSupIndep_iff _).mp hind
  · rw [sSup_eq_iSup, sSup_eq_iSup] at hsup
    exact hsup

end S_AutomorphicForm_CuspidalConstituent_exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent (solution)
