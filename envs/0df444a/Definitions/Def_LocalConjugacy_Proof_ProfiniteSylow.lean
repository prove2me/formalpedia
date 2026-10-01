-- Prove2me | Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
-- name    : LocalConjugacy_Proof_ProfiniteSylow
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:13:46.005729+00:00
-- url     : https://prove2.me/theorems/9bc390d4-7eae-45df-99e3-015390d1b1c3
-- title:
--   Finite-quotient Sylow inverse systems
-- statement:
--   The finite quotient subgroups and transition homomorphisms, their compatibility, and the associated inverse-system functor used to construct profinite Sylow subgroups.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]

theorem profinite_closed_subgroup (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    Profinite H := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  exact ⟨⟩









namespace FiniteSylowSystem
open CategoryTheory

def transition {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (G ⧸ U.toSubgroup) →* (G ⧸ V.toSubgroup) :=
  QuotientGroup.map U.toSubgroup V.toSubgroup (MonoidHom.id G) h



theorem transition_surjective {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    Function.Surjective (transition h) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup y
  exact ⟨QuotientGroup.mk' U.toSubgroup x, rfl⟩

@[simp] theorem transition_refl (U : OpenNormalSubgroup G) :
    transition (le_refl U) = MonoidHom.id _ := QuotientGroup.map_id _

@[simp] theorem transition_comp {U V W : OpenNormalSubgroup G} (h : U ≤ V) (k : V ≤ W) :
    (transition k).comp (transition h) = transition (h.trans k) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup x
  rfl

noncomputable def functor (p : ℕ) [Fact p.Prime] : OpenNormalSubgroup G ⥤ Type u where
  obj U := Sylow p (G ⧸ U.toSubgroup)
  map h := TypeCat.ofHom (fun P => Sylow.mapSurjective (transition_surjective (leOfHom h)) P)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro P
    apply Sylow.ext
    change (P : Subgroup _).map (transition (le_refl U)) = (P : Subgroup _)
    simp only [transition_refl, Subgroup.map_id]
  map_comp {U V W} h k := by
    apply ConcreteCategory.hom_ext
    intro P
    apply Sylow.ext
    change (P : Subgroup _).map (transition ((leOfHom h).trans (leOfHom k))) =
      ((P : Subgroup _).map (transition (leOfHom h))).map (transition (leOfHom k))
    rw [Subgroup.map_map, transition_comp]



variable {p : ℕ} [Fact p.Prime]
variable (P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup))
variable (hP : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (P U).mapSurjective (transition_surjective h) = P V)

def subgroup : Subgroup G :=
  ⨅ U : OpenNormalSubgroup G, (P U : Subgroup _).comap (QuotientGroup.mk' U.toSubgroup)





include hP







end FiniteSylowSystem





























end LocalConjugacy

end LocalConjugacy.Proof

end


