-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IsoBlowupRemoval
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IsoBlowupRemoval
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:29:37.639049+00:00
-- url     : https://prove2.me/theorems/321d79f2-cdda-4313-8601-c7a4a015d1c8
-- title:
--   Iso Blowup Removal
-- statement:
--   Definitions and structural lemmas for Iso Blowup Removal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IsoBlowupRemoval.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsStrictPullbackBlowupSeq_center_eq_top_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsStrictPullbackBlowupSeq_length_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_center_nextNontrivialIndex_ne_top_or_length_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_objNontrivialIndexZeroIso_hom
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_isoObjZero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_schemeAt
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_projectionToBase_of_isPullback_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_transitionMap_of_isPullback_blowupMorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_schemeAt


set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups
theorem nextNontrivialIndex_le_of_center_eq_top_iff {X' X : Scheme.{u}} (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) (hlen : t.length = s.length)
    (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤)) (a : ℕ) :
    t.nextNontrivialIndex a ≤ s.nextNontrivialIndex a := by
  refine t.nextNontrivialIndex_le (s.le_nextNontrivialIndex a) ?_
  rcases s.center_nextNontrivialIndex_ne_top_or_length_le a with hd | hd
  · by_cases hlt : s.nextNontrivialIndex a < s.length
    · exact Or.inl fun hc => hd ((hcen _ hlt).mp hc)
    · exact Or.inr (by omega)
  · exact Or.inr (by omega)
theorem nextNontrivialIndex_congr {X' X : Scheme.{u}} (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
    (hlen : t.length = s.length)
    (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤)) (a : ℕ) :
    t.nextNontrivialIndex a = s.nextNontrivialIndex a :=
  le_antisymm (nextNontrivialIndex_le_of_center_eq_top_iff t s hlen hcen a)
    (nextNontrivialIndex_le_of_center_eq_top_iff s t hlen.symm (fun i hi => (hcen i (by omega)).symm) a)
theorem nontrivialIndex_congr {X' X : Scheme.{u}} (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
    (hlen : t.length = s.length)
    (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤)) (j : ℕ) :
    t.nontrivialIndex j = s.nontrivialIndex j := by
  induction j with
  | zero =>
      rw [nontrivialIndex_zero, nontrivialIndex_zero]
      exact nextNontrivialIndex_congr t s hlen hcen 0
  | succ j ih =>
      rw [nontrivialIndex_succ, nontrivialIndex_succ, ih]
      exact nextNontrivialIndex_congr t s hlen hcen _
theorem lengthWithoutIsoBlowups_le_of_center_eq_top_iff {X' X : Scheme.{u}} (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) (hlen : t.length = s.length)
    (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤)) :
    t.lengthWithoutIsoBlowups ≤ s.lengthWithoutIsoBlowups := by
  by_contra hc
  have hc' : s.lengthWithoutIsoBlowups < t.lengthWithoutIsoBlowups := not_le.mp hc
  have h1 : t.nontrivialIndex s.lengthWithoutIsoBlowups < t.length := t.nontrivialIndex_lt_length hc'
  have h2 : s.nontrivialIndex s.lengthWithoutIsoBlowups = s.length := s.nontrivialIndex_lengthWithoutIsoBlowups
  have h3 := nontrivialIndex_congr t s hlen hcen s.lengthWithoutIsoBlowups
  omega
theorem lengthWithoutIsoBlowups_congr {X' X : Scheme.{u}} (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
    (hlen : t.length = s.length)
    (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤)) :
    t.lengthWithoutIsoBlowups = s.lengthWithoutIsoBlowups :=
  le_antisymm (lengthWithoutIsoBlowups_le_of_center_eq_top_iff t s hlen hcen)
    (lengthWithoutIsoBlowups_le_of_center_eq_top_iff s t hlen.symm (fun i hi => (hcen i (by omega)).symm))
theorem eqToHom_comp_transitionMap {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b a' b' : ℕ}
    (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b') :
    eqToHom (congrArg s.schemeAt hb) ≫ s.transitionMap h' = s.transitionMap h ≫ eqToHom (congrArg s.schemeAt ha) := by
  subst ha
  subst hb
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
theorem eqToHom_comp_projectionToBase {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg s.schemeAt h) ≫ s.projectionToBase b = s.projectionToBase a := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
end SequenceOfBlowups
theorem isPullback_eqToHom_right {P Y X Z X' Z' : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (hX : X = X') (hZ : Z = Z') {f' : X' ⟶ Z'}
    (hf : eqToHom hX ≫ f' = f ≫ eqToHom hZ) :
    IsPullback (fst ≫ eqToHom hX) snd f' (g ≫ eqToHom hZ) := by
  subst hX
  subst hZ
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hf ⊢
  rw [hf]
  exact h
theorem center_eq_comap_comp_eqToHom {X' X : Scheme.{u}} (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) {a b : ℕ} (hab : a = b) (f : t.schemeAt a ⟶ s.schemeAt a)
    (hf : t.center a = (s.center a).comap f) :
    t.center a = (s.center b).comap (f ≫ eqToHom (congrArg s.schemeAt hab)) := by
  subst hab
  simp only [eqToHom_refl, Category.comp_id]
  exact hf
theorem IsStrictPullbackBlowupSeq.withoutIsoBlowups {X' X : Scheme.{u}} {g : X' ⟶ X}
    [AlgebraicGeometry.Surjective g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) :
    IsStrictPullbackBlowupSeq g t.withoutIsoBlowups s.withoutIsoBlowups := by
  have hiff : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤) :=
    fun i hi => h.center_eq_top_iff i hi
  have hlen : t.length = s.length := h.length_eq
  have hret : ∀ j : ℕ, t.nontrivialIndex j = s.nontrivialIndex j := SequenceOfBlowups.nontrivialIndex_congr t s hlen hiff
  have hplen : t.lengthWithoutIsoBlowups = s.lengthWithoutIsoBlowups := SequenceOfBlowups.lengthWithoutIsoBlowups_congr t s hlen hiff
  unfold IsStrictPullbackBlowupSeq at h ⊢
  obtain ⟨-, σ, hzero, hstep, hcen⟩ := h
  have hstruct := isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length σ hzero hstep
  have hdown := isPullback_transitionMap_of_isPullback_blowupMorphism t s t.length σ hstep
  have h1 : (σ (t.nontrivialIndex 0) (t.nontrivialIndex_le_length (Nat.zero_le _)) ≫
        eqToHom (congrArg s.schemeAt (hret 0))) ≫ s.withoutIsoBlowups.isoZero.hom
      = t.withoutIsoBlowups.isoZero.hom ≫ g := by
    rw [s.withoutIsoBlowups_isoObjZero, t.withoutIsoBlowups_isoObjZero, s.objNontrivialIndexZeroIso_hom, t.objNontrivialIndexZeroIso_hom,
      Category.assoc, SequenceOfBlowups.eqToHom_comp_projectionToBase s (hret 0)]
    exact (hstruct (t.nontrivialIndex 0) (t.nontrivialIndex_le_length (Nat.zero_le _))).w
  have h2 : ∀ j : ℕ, ∀ hj : j < t.withoutIsoBlowups.length,
      IsPullback
        (σ (t.nontrivialIndex (j + 1)) (t.nontrivialIndex_le_length hj) ≫
          eqToHom (congrArg s.schemeAt (hret (j + 1))))
        (t.withoutIsoBlowups.transitionMapSucc j) (s.withoutIsoBlowups.transitionMapSucc j)
        (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)) ≫
          eqToHom (congrArg s.schemeAt (hret j))) := by
    intro j hj
    rw [t.withoutIsoBlowups_blowupMorphism, s.withoutIsoBlowups_blowupMorphism]
    exact isPullback_eqToHom_right
      (hdown (t.nontrivialIndex j) (t.nontrivialIndex (j + 1)) (t.nontrivialIndex_monotone (Nat.le_succ j))
        (t.nontrivialIndex_le_length hj))
      (congrArg s.schemeAt (hret (j + 1))) (congrArg s.schemeAt (hret j))
      (SequenceOfBlowups.eqToHom_comp_transitionMap s (hret j) (hret (j + 1))
        (t.nontrivialIndex_monotone (Nat.le_succ j)) (s.nontrivialIndex_monotone (Nat.le_succ j)))
  have h3 : ∀ j : ℕ, ∀ hj : j < t.withoutIsoBlowups.length,
      t.withoutIsoBlowups.center j = (s.withoutIsoBlowups.center j).comap
        (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)) ≫
          eqToHom (congrArg s.schemeAt (hret j))) := by
    intro j hj
    exact center_eq_comap_comp_eqToHom t s (hret j)
      (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)))
      (hcen (t.nontrivialIndex j) (t.nontrivialIndex_lt_length hj))
  exact ⟨hplen, fun j hj => σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length hj) ≫
    eqToHom (congrArg s.schemeAt (hret j)), h1, h2, h3⟩
end FunctorialResolution.EmbeddedResolution


