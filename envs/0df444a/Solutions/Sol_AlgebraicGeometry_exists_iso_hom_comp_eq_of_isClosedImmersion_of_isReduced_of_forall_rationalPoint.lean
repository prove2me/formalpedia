-- Prove2me | solution 1 for AlgebraicGeometry.exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f5bb030c-27b0-5583-afd7-ebd83f253079

import Mathlib
import Theorems.Thm_AlgebraicGeometry_eq_of_isClosed_of_forall_rationalPoint_mem_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace C3

open TopologicalSpace

theorem ker_eq_vanishingIdeal {T Y : Scheme.{0}} (g : T ⟶ Y) [IsReduced T] :
    g.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range g.base)) := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot (X := T), ← Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 2
  simp [Set.image_univ]

theorem exists_comp_eq_iff_range_subset {Z T Y : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsReduced Z]
    (g : T ⟶ Y) [IsReduced T] :
    (∃ l : T ⟶ Z, l ≫ i = g) ↔ Set.range g.base ⊆ Set.range i.base := by
  constructor
  · rintro ⟨l, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨l.base t, rfl⟩
  · intro H
    have hk : i.ker ≤ g.ker := by
      rw [ker_eq_vanishingIdeal i, ker_eq_vanishingIdeal g]
      exact Scheme.IdealSheafData.vanishingIdeal_antimono (Closeds.gi.gc.monotone_l H)
    exact ⟨IsClosedImmersion.lift i g hk, IsClosedImmersion.lift_fac i g hk⟩

end C3

theorem solution
    {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    {Z₁ Z₂ : Scheme.{0}} (i₁ : Z₁ ⟶ Y) (i₂ : Z₂ ⟶ Y) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsReduced Z₁] [IsReduced Z₂]
    (h : ∀ y : Spec (CommRingCat.of k) ⟶ Y, y ≫ f = 𝟙 _ →
      ((∃ z : Spec (CommRingCat.of k) ⟶ Z₁, z ≫ i₁ = y) ↔ (∃ z : Spec (CommRingCat.of k) ⟶ Z₂, z ≫ i₂ = y))) :
    ∃ e : Z₁ ≅ Z₂, e.hom ≫ i₂ = i₁ := by
  classical

  have hc₁ : IsClosed (Set.range i₁.base) := i₁.isClosedEmbedding.isClosed_range
  have hc₂ : IsClosed (Set.range i₂.base) := i₂.isClosedEmbedding.isClosed_range

  have hpt : ∀ {Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] [IsReduced Z] (y : Spec (CommRingCat.of k) ⟶ Y),
      (∃ z : Spec (CommRingCat.of k) ⟶ Z, z ≫ i = y) ↔ y.base (IsLocalRing.closedPoint k) ∈ Set.range i.base := by
    intro Z i _ _ y
    rw [C3.exists_comp_eq_iff_range_subset i y]
    constructor
    · intro H; exact H ⟨_, rfl⟩
    · rintro H _ ⟨t, rfl⟩
      rw [Subsingleton.elim t (IsLocalRing.closedPoint k)]
      exact H

  have hS : Set.range i₁.base = Set.range i₂.base :=
    AlgebraicGeometry.eq_of_isClosed_of_forall_rationalPoint_mem_iff f hc₁ hc₂ fun y hy => by
      rw [← hpt i₁ y, ← hpt i₂ y]
      exact h y hy

  have hker : i₂.ker = i₁.ker := by
    rw [C3.ker_eq_vanishingIdeal i₁, C3.ker_eq_vanishingIdeal i₂, hS]
  haveI := IsClosedImmersion.isIso_lift i₂ i₁ hker
  exact ⟨asIso (IsClosedImmersion.lift i₂ i₁ hker.le), IsClosedImmersion.lift_fac i₂ i₁ hker.le⟩

end S_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint
end P2MW
export P2MW.S_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_isReduced_of_forall_rationalPoint (solution)
