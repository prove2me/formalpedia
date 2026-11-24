-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:25:26.621429+00:00
-- url     : https://prove2.me/theorems/aa62959a-bf2a-4e7b-8490-52d2ae3e862b
-- title:
--   Remove Iso Blowups
-- statement:
--   Definitions and structural lemmas for Remove Iso Blowups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_isIso_of_top
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_iso_hom_comp
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_blowupMorphism_eq_transitionMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_isBlowupAlongIdealSheaf_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_transitionMap_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups
variable {X : Scheme.{u}}
theorem isIso_transitionMap_refl (s : SequenceOfBlowups X) {i : ℕ} (h : i ≤ i) :
    IsIso (s.transitionMap h) := by
  have he : (homOfLE h : i ⟶ i).op = 𝟙 (Opposite.op i) := rfl
  have hid : s.transitionMap h = 𝟙 (s.schemeAt i) := by
    rw [SequenceOfBlowups.transitionMap_def, he]
    exact s.tower.map_id (Opposite.op i)
  rw [hid]
  infer_instance
theorem isIso_transitionMap_of_center_eq_top (s : SequenceOfBlowups X) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ s.length) (h : ∀ i, a ≤ i → i < b → s.center i = ⊤) :
    IsIso (s.transitionMap hab) := by
  revert hb h
  induction b, hab using Nat.le_induction with
  | base =>
    intro _ _
    exact isIso_transitionMap_refl s _
  | succ b hab ih =>
    intro hb h
    have hbl : b ≤ s.length := le_trans (Nat.le_succ b) hb
    have hlt : b < s.length := lt_of_lt_of_le (Nat.lt_succ_self b) hb
    have hcen : s.center b = ⊤ := h b hab (Nat.lt_succ_self b)
    have : IsIso (s.transitionMap hab) :=
      ih hbl fun i hi hib => h i hi (Nat.lt_succ_of_lt hib)
    have hB : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc b) (s.center b) := s.isBlowupAlongIdealSheaf_blowupMorphism b hlt
    rw [hcen] at hB
    have : IsIso (s.transitionMap (Nat.le_succ b)) := by
      have h4 := hB.isIso_of_top
      rw [s.blowupMorphism_eq_transitionMap b] at h4
      exact h4
    have h3 : IsIso (s.transitionMap (Nat.le_succ b) ≫ s.transitionMap hab) := inferInstance
    rw [s.transitionMap_trans hab (Nat.le_succ b)] at h3
    exact h3
theorem exists_le_center_ne_top_or_length_le (s : SequenceOfBlowups X) (a : ℕ) :
    ∃ i, a ≤ i ∧ (s.center i ≠ ⊤ ∨ s.length ≤ i) :=
  ⟨max a s.length, le_max_left _ _, Or.inr (le_max_right _ _)⟩
noncomputable def nextNontrivialIndex (s : SequenceOfBlowups X) (a : ℕ) : ℕ :=
  @Nat.find _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a)
theorem nextNontrivialIndex_spec (s : SequenceOfBlowups X) (a : ℕ) :
    a ≤ s.nextNontrivialIndex a ∧ (s.center (s.nextNontrivialIndex a) ≠ ⊤ ∨ s.length ≤ s.nextNontrivialIndex a) :=
  @Nat.find_spec _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a)
theorem le_nextNontrivialIndex (s : SequenceOfBlowups X) (a : ℕ) : a ≤ s.nextNontrivialIndex a :=
  (s.nextNontrivialIndex_spec a).1
theorem nextNontrivialIndex_le (s : SequenceOfBlowups X) {a i : ℕ} (hi : a ≤ i)
    (h : s.center i ≠ ⊤ ∨ s.length ≤ i) : s.nextNontrivialIndex a ≤ i :=
  @Nat.find_min' _ (fun _ => Classical.propDecidable _) (s.exists_le_center_ne_top_or_length_le a) i ⟨hi, h⟩
theorem nextNontrivialIndex_le_length (s : SequenceOfBlowups X) {a : ℕ} (h : a ≤ s.length) :
    s.nextNontrivialIndex a ≤ s.length :=
  s.nextNontrivialIndex_le h (Or.inr le_rfl)
theorem center_eq_top_of_lt_nextNontrivialIndex (s : SequenceOfBlowups X) {a i : ℕ} (hai : a ≤ i)
    (h : i < s.nextNontrivialIndex a) : s.center i = ⊤ := by
  by_contra hc
  exact absurd (s.nextNontrivialIndex_le hai (Or.inl hc)) (not_le.mpr h)
noncomputable def nontrivialIndex (s : SequenceOfBlowups X) (j : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (s.nextNontrivialIndex 0) (fun _ ih => s.nextNontrivialIndex (ih + 1)) j
@[simp] theorem nontrivialIndex_succ (s : SequenceOfBlowups X) (j : ℕ) :
    s.nontrivialIndex (j + 1) = s.nextNontrivialIndex (s.nontrivialIndex j + 1) := rfl
theorem nontrivialIndex_lt_succ (s : SequenceOfBlowups X) (j : ℕ) : s.nontrivialIndex j < s.nontrivialIndex (j + 1) := by
  have h := s.le_nextNontrivialIndex (s.nontrivialIndex j + 1)
  rw [nontrivialIndex_succ]
  exact h
theorem succ_le_nontrivialIndex_succ (s : SequenceOfBlowups X) (j : ℕ) :
    s.nontrivialIndex j + 1 ≤ s.nontrivialIndex (j + 1) :=
  s.nontrivialIndex_lt_succ j
theorem nontrivialIndex_strictMono (s : SequenceOfBlowups X) : StrictMono s.nontrivialIndex :=
  strictMono_nat_of_lt_succ s.nontrivialIndex_lt_succ
theorem nontrivialIndex_monotone (s : SequenceOfBlowups X) : Monotone s.nontrivialIndex :=
  s.nontrivialIndex_strictMono.monotone
theorem le_nontrivialIndex (s : SequenceOfBlowups X) (j : ℕ) : j ≤ s.nontrivialIndex j :=
  s.nontrivialIndex_strictMono.le_apply
theorem center_eq_top_of_lt_nontrivialIndex_zero (s : SequenceOfBlowups X) {i : ℕ} (h : i < s.nontrivialIndex 0) :
    s.center i = ⊤ :=
  s.center_eq_top_of_lt_nextNontrivialIndex (Nat.zero_le i) h
theorem center_eq_top_of_nontrivialIndex_lt (s : SequenceOfBlowups X) {i j : ℕ} (h1 : s.nontrivialIndex j < i)
    (h2 : i < s.nontrivialIndex (j + 1)) : s.center i = ⊤ :=
  s.center_eq_top_of_lt_nextNontrivialIndex h1 h2
theorem exists_length_le_nontrivialIndex (s : SequenceOfBlowups X) : ∃ j, s.length ≤ s.nontrivialIndex j :=
  ⟨s.length, s.le_nontrivialIndex s.length⟩
noncomputable def lengthWithoutIsoBlowups (s : SequenceOfBlowups X) : ℕ :=
  @Nat.find _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex
theorem length_le_nontrivialIndex_lengthWithoutIsoBlowups (s : SequenceOfBlowups X) :
    s.length ≤ s.nontrivialIndex s.lengthWithoutIsoBlowups :=
  @Nat.find_spec _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex
theorem nontrivialIndex_le_length_of_forall_lt (s : SequenceOfBlowups X) (j : ℕ)
    (h : ∀ i, i < j → s.nontrivialIndex i < s.length) : s.nontrivialIndex j ≤ s.length := by
  cases j with
  | zero =>
      show s.nextNontrivialIndex 0 ≤ s.length
      exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  | succ j =>
      have hj : s.nontrivialIndex j < s.length := h j (Nat.lt_succ_self j)
      show s.nextNontrivialIndex (s.nontrivialIndex j + 1) ≤ s.length
      exact s.nextNontrivialIndex_le_length hj
theorem nontrivialIndex_lengthWithoutIsoBlowups (s : SequenceOfBlowups X) : s.nontrivialIndex s.lengthWithoutIsoBlowups = s.length := by
  refine le_antisymm (nontrivialIndex_le_length_of_forall_lt s s.lengthWithoutIsoBlowups ?_)
    s.length_le_nontrivialIndex_lengthWithoutIsoBlowups
  intro i hi
  have hmin := @Nat.find_min _ (fun _ => Classical.propDecidable _)
    s.exists_length_le_nontrivialIndex i hi
  exact not_le.mp hmin
theorem nontrivialIndex_lt_length (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    s.nontrivialIndex j < s.length := by
  have h' : ¬ (s.length ≤ s.nontrivialIndex j) :=
    @Nat.find_min _ (fun _ => Classical.propDecidable _) s.exists_length_le_nontrivialIndex j h
  exact not_le.mp h'
theorem nontrivialIndex_le_length (s : SequenceOfBlowups X) {j : ℕ} (h : j ≤ s.lengthWithoutIsoBlowups) :
    s.nontrivialIndex j ≤ s.length := by
  cases j with
  | zero => exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  | succ i =>
    have hi : i < s.lengthWithoutIsoBlowups := lt_of_lt_of_le (Nat.lt_succ_self i) h
    have hlt : s.nontrivialIndex i + 1 ≤ s.length := s.nontrivialIndex_lt_length hi
    exact s.nextNontrivialIndex_le_length hlt
theorem isIso_transitionMap_nontrivialIndex_zero (s : SequenceOfBlowups X) :
    IsIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0))) := by
  refine s.isIso_transitionMap_of_center_eq_top (Nat.zero_le (s.nontrivialIndex 0)) ?_ ?_
  · exact s.nextNontrivialIndex_le_length (Nat.zero_le _)
  · intro i _ hi
    exact s.center_eq_top_of_lt_nontrivialIndex_zero hi
theorem isIso_transitionMap_nontrivialIndex_succ (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    IsIso (s.transitionMap (s.succ_le_nontrivialIndex_succ j)) := by
  refine s.isIso_transitionMap_of_center_eq_top (s.succ_le_nontrivialIndex_succ j)
    (s.nontrivialIndex_le_length (Nat.succ_le_of_lt h)) ?_
  intro i hi hib
  exact s.center_eq_top_of_nontrivialIndex_lt (Nat.lt_of_succ_le hi) hib
noncomputable def objNontrivialIndexZeroIso (s : SequenceOfBlowups X) : s.schemeAt (s.nontrivialIndex 0) ≅ X :=
  haveI : IsIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0))) := s.isIso_transitionMap_nontrivialIndex_zero
  (asIso (s.transitionMap (Nat.zero_le (s.nontrivialIndex 0)))).trans s.isoZero
noncomputable def towerWithoutIsoBlowups (s : SequenceOfBlowups X) : ℕᵒᵖ ⥤ Scheme.{u} :=
  (Monotone.functor s.nontrivialIndex_monotone).op ⋙ s.tower
theorem isBlowupAlongIdealSheaf_towerWithoutIsoBlowups_map (s : SequenceOfBlowups X) (i : ℕ) (hi : i < s.lengthWithoutIsoBlowups) :
    Blowup.IsBlowupAlongIdealSheaf (s.towerWithoutIsoBlowups.map (homOfLE (Nat.le_succ i)).op) (s.center (s.nontrivialIndex i)) := by
  have : IsIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i)) := s.isIso_transitionMap_nontrivialIndex_succ hi
  have hB : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc (s.nontrivialIndex i)) (s.center (s.nontrivialIndex i)) :=
    s.isBlowupAlongIdealSheaf_blowupMorphism (s.nontrivialIndex i) (s.nontrivialIndex_lt_length hi)
  have hcomp := hB.iso_hom_comp (asIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i)))
  have heq : (asIso (s.transitionMap (s.succ_le_nontrivialIndex_succ i))).hom ≫ s.transitionMapSucc (s.nontrivialIndex i)
      = s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ i)) := by
    rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
    exact s.transitionMap_trans (Nat.le_succ (s.nontrivialIndex i)) (s.succ_le_nontrivialIndex_succ i)
  rw [heq] at hcomp
  show Blowup.IsBlowupAlongIdealSheaf (s.transitionMap (s.nontrivialIndex_monotone (Nat.le_succ i))) (s.center (s.nontrivialIndex i))
  exact hcomp
noncomputable def withoutIsoBlowups (s : SequenceOfBlowups X) : SequenceOfBlowups X where
  length := s.lengthWithoutIsoBlowups
  tower := s.towerWithoutIsoBlowups
  isoZero := s.objNontrivialIndexZeroIso
  center := fun j => s.center (s.nontrivialIndex j)
  isBlowup := s.isBlowupAlongIdealSheaf_towerWithoutIsoBlowups_map
theorem withoutIsoBlowups_lastObj (s : SequenceOfBlowups X) : s.withoutIsoBlowups.lastObj = s.lastObj :=
  congrArg s.schemeAt s.nontrivialIndex_lengthWithoutIsoBlowups
end SequenceOfBlowups
end FunctorialResolution.EmbeddedResolution


