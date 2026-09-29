-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5b49687a-31da-5502-940e-4def94345a89

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace C2E5

theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩ with hI

  haveI : IrreducibleSpace I.subscheme := by
    have h : IsIrreducible ((I.support : TopologicalSpace.Closeds X) : Set X) := by
      rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact hZ'
    exact Subtype.irreducibleSpace h

  have hred : ∀ U : X.affineOpens, _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) := fun U => by
    rw [← Ideal.isRadical_iff_quotient_reduced, hI, Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  haveI : ∀ U, IsReduced (I.subschemeCover.openCover.X U) := fun U => by
    haveI := hred U
    exact inferInstanceAs (IsReduced (Spec (.of (Γ(X, U.1) ⧸ I.ideal U))))
  haveI : IsReduced I.subscheme := IsReduced.of_openCover (X := I.subscheme) I.subschemeCover.openCover
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2.solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [IsProper t]
    (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z) (U : X.Opens) (hZU : Z ⊆ U) (g : Γ(X, U)) :
    Z ⊆ X.basicOpen g ∨ Disjoint Z (X.basicOpen g) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩ with hI
  haveI : IsIntegral I.subscheme := isIntegral_subscheme_vanishingIdeal Z hZ hZ'

  have hrange : Set.range I.subschemeι.base = Z := by
    change Set.range I.subschemeι = Z
    rw [Scheme.IdealSheafData.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl

  haveI : UniversallyClosed (I.subschemeι ≫ t) := inferInstance
  have hF : IsField Γ(I.subscheme, ⊤) := isField_of_universallyClosed k (I.subschemeι ≫ t)

  have hpre : I.subschemeι ⁻¹ᵁ U = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    show I.subschemeι.base z ∈ U
    exact hZU (hrange ▸ Set.mem_range_self z)
  have hF' : IsField Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) := by rw [hpre]; exact hF
  letI := hF'.toField

  have key : I.subschemeι ⁻¹ᵁ X.basicOpen g = I.subscheme.basicOpen (I.subschemeι.app U g) :=
    Scheme.preimage_basicOpen I.subschemeι g
  by_cases h0 : I.subschemeι.app U g = 0
  · right
    rw [Set.disjoint_left]
    rintro z hz hzg
    obtain ⟨z', rfl⟩ : z ∈ Set.range I.subschemeι.base := hrange ▸ hz
    have : z' ∈ I.subschemeι ⁻¹ᵁ X.basicOpen g := hzg
    rw [key, h0, Scheme.basicOpen_zero] at this
    exact this
  · left
    intro z hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range I.subschemeι.base := hrange ▸ hz
    show z' ∈ I.subschemeι ⁻¹ᵁ X.basicOpen g
    rw [key, I.subscheme.basicOpen_of_isUnit (isUnit_iff_ne_zero.mpr h0), hpre]
    trivial

end C2E5

end S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2 (solution)
