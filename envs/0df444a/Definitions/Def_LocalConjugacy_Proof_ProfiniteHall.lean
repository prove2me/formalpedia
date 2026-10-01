-- Prove2me | Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
-- name    : LocalConjugacy_Proof_ProfiniteHall
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:27:54.757975+00:00
-- url     : https://prove2.me/theorems/a7c68a0b-d8b6-4ecb-a096-6d9d897beacb
-- title:
--   Inverse systems for profinite Hall subgroups
-- statement:
--   Finite upper Hall subgroups with compatible transition maps, their normality and Hall properties, and the associated inverse-system functor.
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
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

namespace FiniteSubgroupSystem
open FiniteSylowSystem
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
variable (S : (U : OpenNormalSubgroup G) → Subgroup (G ⧸ U.toSubgroup))
variable (hS : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (S U).map (transition h) = S V)

def subgroup : Subgroup G :=
  ⨅ U : OpenNormalSubgroup G, (S U : Subgroup _).comap (QuotientGroup.mk' U.toSubgroup)

theorem mem_subgroup (x : G) :
    x ∈ subgroup S ↔ ∀ U, QuotientGroup.mk' U.toSubgroup x ∈ S U := by
  simp only [subgroup, Subgroup.mem_iInf, Subgroup.mem_comap]



include hS








end FiniteSubgroupSystem

section ProfiniteHall
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
open FiniteSylowSystem
open scoped Pointwise







noncomputable def finiteUpperHall (hG : Prosupersolvable G) (n : ℕ)
    (U : OpenNormalSubgroup G) : Subgroup (G ⧸ U.toSubgroup) :=
  (supersolvable_exists_normalHall (hG U) n).choose

instance finiteUpperHall_normal (hG : Prosupersolvable G) (n : ℕ)
    (U : OpenNormalSubgroup G) : (finiteUpperHall hG n U).Normal :=
  (supersolvable_exists_normalHall (hG U) n).choose_spec.1

theorem finiteUpperHall_hall (hG : Prosupersolvable G) (n : ℕ)
    (U : OpenNormalSubgroup G) : IsHall {p | n < p} (finiteUpperHall hG n U) :=
  (supersolvable_exists_normalHall (hG U) n).choose_spec.2

theorem finiteUpperHall_transition (hG : Prosupersolvable G) (n : ℕ)
    (U V : OpenNormalSubgroup G) (h : U ≤ V) :
    (finiteUpperHall hG n U).map (transition h) = finiteUpperHall hG n V := by
  letI := (inferInstance : (finiteUpperHall hG n U).Normal).map
    (transition h) (transition_surjective h)
  exact ((finiteUpperHall_hall hG n U).map_surjective
    (transition h) (transition_surjective h)).eq_of_normal (finiteUpperHall_hall hG n V)

noncomputable def upperHall (hG : Prosupersolvable G) (n : ℕ) : Subgroup G :=
  FiniteSubgroupSystem.subgroup (finiteUpperHall hG n)

instance upperHall_normal (hG : Prosupersolvable G) (n : ℕ) : (upperHall hG n).Normal := by
  constructor
  intro x hx g
  apply (FiniteSubgroupSystem.mem_subgroup _ _).mpr
  intro U
  have hxU := (FiniteSubgroupSystem.mem_subgroup _ _).mp hx U
  simpa only [map_mul, map_inv] using
    (inferInstance : (finiteUpperHall hG n U).Normal).conj_mem _ hxU
      (QuotientGroup.mk' U.toSubgroup g)



namespace HallComplementSystem
open CategoryTheory
variable (hG : Prosupersolvable G) (n : ℕ) (P : Subgroup G)

def obj (U : OpenNormalSubgroup G) :=
  {Q : Subgroup (G ⧸ U.toSubgroup) //
    (finiteUpperHall hG n U).IsComplement' Q ∧ IsHall {r | r ≤ n} Q ∧
      P.map (QuotientGroup.mk' U.toSubgroup) ≤ Q}

def map {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (Q : obj hG n P U) : obj hG n P V := by
  refine ⟨Q.val.map (transition h), ?_, ?_, ?_⟩
  · have hh := complement_map_of_disjoint Q.property.1 (transition h) (transition_surjective h)
      (disjoint_of_cutoff_primes ((finiteUpperHall_hall hG n U).1.map (transition h))
        (Q.property.2.1.1.map (transition h)))
    rwa [finiteUpperHall_transition] at hh
  · exact Q.property.2.1.map_surjective (transition h) (transition_surjective h)
  · have hπ : (transition h).comp (QuotientGroup.mk' U.toSubgroup) =
        QuotientGroup.mk' V.toSubgroup := rfl
    rw [← hπ, ← Subgroup.map_map]
    exact Subgroup.map_mono Q.property.2.2

def functor : OpenNormalSubgroup G ⥤ Type _ where
  obj := obj hG n P
  map h := TypeCat.ofHom (map hG n P (leOfHom h))
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro Q
    apply Subtype.ext
    change Q.val.map (transition (le_refl U)) = Q.val
    rw [transition_refl, Subgroup.map_id]
  map_comp {U V W} h k := by
    apply ConcreteCategory.hom_ext
    intro Q
    apply Subtype.ext
    change Q.val.map (transition ((leOfHom h).trans (leOfHom k))) =
      (Q.val.map (transition (leOfHom h))).map (transition (leOfHom k))
    rw [Subgroup.map_map, transition_comp]



end HallComplementSystem



end ProfiniteHall
end LocalConjugacy

end LocalConjugacy.Proof

end


