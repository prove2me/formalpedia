-- Prove2me | solution 1 for AlgebraicGeometry.surjective_of_closedPoints_subset_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fcd1de96-7f9f-56d0-b444-1d7c26a86200

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_surjective_of_closedPoints_subset_range

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_surjective_of_closedPoints_subset_range.AlgebraicGeometry Topology"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Hom Scheme.Hom.isLocallyConstructible_image QuasiCompact Scheme LocallyOfFinitePresentation"
namespace SurjClosedPoints
p2m_open "AlgebraicGeometry"

section TopLemmas

variable {X : Type*} [TopologicalSpace X]

def FinLC (s : Set X) : Prop :=
  ∃ S : Set (Set X), S.Finite ∧ (∀ z ∈ S, IsLocallyClosed z) ∧ s = ⋃₀ S

theorem FinLC.of_isLocallyClosed {s : Set X} (hs : IsLocallyClosed s) : FinLC s :=
  ⟨{s}, Set.finite_singleton s, by simpa using hs, by simp⟩

theorem FinLC.union {s t : Set X} (hs : FinLC s) (ht : FinLC t) : FinLC (s ∪ t) := by
  obtain ⟨S, hSf, hSl, rfl⟩ := hs
  obtain ⟨T, hTf, hTl, rfl⟩ := ht
  refine ⟨S ∪ T, hSf.union hTf, ?_, (Set.sUnion_union S T).symm⟩
  rintro z (hz | hz)
  exacts [hSl z hz, hTl z hz]

theorem FinLC.inter {s t : Set X} (hs : FinLC s) (ht : FinLC t) : FinLC (s ∩ t) := by
  obtain ⟨S, hSf, hSl, rfl⟩ := hs
  obtain ⟨T, hTf, hTl, rfl⟩ := ht
  refine ⟨Set.image2 (· ∩ ·) S T, hSf.image2 _ hTf, ?_, ?_⟩
  · rintro z ⟨a, ha, b, hb, rfl⟩
    exact (hSl a ha).inter (hTl b hb)
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_image2, exists_exists_and_exists_and_eq_and]
    constructor
    · rintro ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩
      exact ⟨a, ha, b, hb, hxa, hxb⟩
    · rintro ⟨a, ha, b, hb, hxa, hxb⟩
      exact ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩

theorem finLC_and_compl_of_isConstructible {s : Set X} (hs : IsConstructible s) :
    FinLC s ∧ FinLC sᶜ := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    exact ⟨.of_isLocallyClosed hU.isLocallyClosed, .of_isLocallyClosed hU.isClosed_compl.isLocallyClosed⟩
  | union s _ t _ hs ht =>
    refine ⟨hs.1.union ht.1, ?_⟩
    rw [Set.compl_union]
    exact hs.2.inter ht.2
  | compl s _ hs =>
    rw [compl_compl]
    exact ⟨hs.2, hs.1⟩

theorem nonempty_inter_closedPoints_of_isConstructible [JacobsonSpace X] {s : Set X}
    (hs : IsConstructible s) (hne : s.Nonempty) : (s ∩ closedPoints X).Nonempty := by
  obtain ⟨S, -, hSl, rfl⟩ := (finLC_and_compl_of_isConstructible hs).1
  obtain ⟨x, z, hz, hxz⟩ := hne
  obtain ⟨y, hyz, hyc⟩ := nonempty_inter_closedPoints ⟨x, hxz⟩ (hSl z hz)
  exact ⟨y, ⟨z, hz, hyz⟩, hyc⟩

theorem nonempty_inter_closedPoints_of_isLocallyConstructible [JacobsonSpace X] {s : Set X}
    (hs : IsLocallyConstructible s) (hne : s.Nonempty) : (s ∩ closedPoints X).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, hUx, hUo, hUc⟩ := hs x
  haveI : JacobsonSpace U := .of_isOpenEmbedding hUo.isOpenEmbedding_subtypeVal
  have hxU : x ∈ U := mem_of_mem_nhds hUx
  obtain ⟨y, hys, hyc⟩ :=
    nonempty_inter_closedPoints_of_isConstructible hUc ⟨⟨x, hxU⟩, show (⟨x, hxU⟩ : U).1 ∈ s from hx⟩
  refine ⟨y.1, hys, ?_⟩
  have := hUo.isOpenEmbedding_subtypeVal.preimage_closedPoints (X := U) (Y := X)
  rw [← this] at hyc
  exact hyc

end TopLemmas

theorem isLocallyConstructible_compl {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsLocallyConstructible s) : IsLocallyConstructible sᶜ := by
  intro x
  obtain ⟨U, hUx, hUo, hUc⟩ := hs x
  refine ⟨U, hUx, hUo, ?_⟩
  have e : (Subtype.val ⁻¹' sᶜ : Set U) = (Subtype.val ⁻¹' s : Set U)ᶜ := by
    ext y; simp
  rw [e]
  exact hUc.compl

theorem surjective_of_closedPoints_subset_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [JacobsonSpace Y]
    (h : closedPoints Y ⊆ Set.range f.base) : Surjective f := by
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hlc : IsLocallyConstructible (Set.range f.base) := by
    simpa [Set.image_univ] using f.isLocallyConstructible_image (s := Set.univ) (by simp)
  have hne : ((Set.range f.base)ᶜ).Nonempty := ⟨y, hy⟩
  obtain ⟨z, hz, hzc⟩ :=
    nonempty_inter_closedPoints_of_isLocallyConstructible (isLocallyConstructible_compl hlc) hne
  exact hz (h hzc)

end AlgebraicGeometry.SurjClosedPoints

open AlgebraicGeometry.SurjClosedPoints in
theorem solution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [JacobsonSpace Y]
    (h : closedPoints Y ⊆ Set.range f.base) : Surjective f :=
  surjective_of_closedPoints_subset_range f h

end S_AlgebraicGeometry_surjective_of_closedPoints_subset_range
end P2MW
export P2MW.S_AlgebraicGeometry_surjective_of_closedPoints_subset_range (solution)
