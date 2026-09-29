-- Prove2me | solution 1 for AlgebraicGeometry.exists_opens_nonempty_subset_image_of_apply_genericPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f939c467-880d-596a-93cc-5365595436ae

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_opens_nonempty_subset_image_of_apply_genericPoint_eq

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Topology

universe u

namespace C1Sol

open Topology

theorem exists_open_of_isConstructible_of_genericPoint_mem {Y : Type u} [TopologicalSpace Y] [QuasiSober Y] [IrreducibleSpace Y]
    {s : Set Y} (hs : IsConstructible s) (hξ : genericPoint Y ∈ s) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧ V ⊆ s := by
  have hgen : ∀ W : Set Y, IsOpen W → W.Nonempty → genericPoint Y ∈ W := fun W hW hne =>
    ((genericPoint_spec Y).mem_open_set_iff hW).mpr (by simpa using hne)
  revert hξ
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    intro hξ
    have hV0 : V = ∅ := by
      by_contra hne
      exact hξ.2 (hgen V hV.1 (Set.nonempty_iff_ne_empty.mpr hne))
    refine ⟨U, hU.1, ⟨_, hξ.1⟩, ?_⟩
    rw [hV0, Set.diff_empty]
  | sup s _ t _ hs' ht' =>
    rintro (h | h)
    · obtain ⟨V, hV, hne, hsub⟩ := hs' h
      exact ⟨V, hV, hne, hsub.trans Set.subset_union_left⟩
    · obtain ⟨V, hV, hne, hsub⟩ := ht' h
      exact ⟨V, hV, hne, hsub.trans Set.subset_union_right⟩

end C1Sol

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace ↥Y] [QuasiSeparatedSpace ↥Y] [IrreducibleSpace ↥X] [IrreducibleSpace ↥Y]
    (hdom : f.base (genericPoint ↥X) = genericPoint ↥Y)
    (U : X.Opens) (hU : (U : Set ↥X).Nonempty) :
    ∃ V : Y.Opens, (V : Set ↥Y).Nonempty ∧ (V : Set ↥Y) ⊆ f.base '' (U : Set ↥X) := by
  classical
  obtain ⟨x, hx⟩ := hU

  obtain ⟨_, ⟨U'', hU'aff, rfl⟩, hxU', hU'U⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  let U' : X.Opens := U''
  haveI : IsAffine U' := hU'aff
  change x ∈ (U' : Set ↥X) at hxU'
  change (U' : Set ↥X) ⊆ U at hU'U

  have hT : IsConstructible ((U'.ι ≫ f).base '' Set.univ) :=
    (U'.ι ≫ f).isConstructible_image (IsCompact.isConstructible isCompact_univ isOpen_univ)

  have hξX : genericPoint ↥X ∈ (U' : Set ↥X) :=
    ((genericPoint_spec ↥X).mem_open_set_iff U'.isOpen).mpr (by simpa using ⟨x, hxU'⟩)
  have hξ : genericPoint ↥Y ∈ (U'.ι ≫ f).base '' Set.univ := by
    refine ⟨⟨genericPoint ↥X, hξX⟩, Set.mem_univ _, ?_⟩
    rw [← hdom]
    rfl
  obtain ⟨V, hV, hne, hsub⟩ := C1Sol.exists_open_of_isConstructible_of_genericPoint_mem hT hξ
  refine ⟨⟨V, hV⟩, hne, hsub.trans ?_⟩
  rintro y ⟨z, -, rfl⟩
  exact ⟨z.1, hU'U z.2, rfl⟩

end S_AlgebraicGeometry_exists_opens_nonempty_subset_image_of_apply_genericPoint_eq
end P2MW
export P2MW.S_AlgebraicGeometry_exists_opens_nonempty_subset_image_of_apply_genericPoint_eq (solution)
