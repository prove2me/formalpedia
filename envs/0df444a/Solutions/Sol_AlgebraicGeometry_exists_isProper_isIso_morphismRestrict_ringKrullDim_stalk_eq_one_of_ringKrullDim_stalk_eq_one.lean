-- Prove2me | solution 1 for AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/305d3a6f-f70b-5a68-b0f7-b3de3e7a60de

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
import Theorems.Thm_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
import Theorems.Thm_AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom
import Theorems.Thm_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType fX] [QuasiCompact fX] [IsIntegral Y] [IsProper fY]
    (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (hα : α ≫ fY = U.ι ≫ fX) (hdom : DenseRange α.base)
    (z : X) (hzU : z ∈ U) (hz₁ : ringKrullDim (X.presheaf.stalk z) = 1)
    (hzn : IsIntegrallyClosed (X.presheaf.stalk z))
    (hnd : ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩)) ≠ 0) :
    ∃ (Y' : Scheme.{u}) (fY' : Y' ⟶ Spec (.of k)) (_ : IsIntegral Y') (_ : IsProper fY')
      (β : Y' ⟶ Y) (_ : β ≫ fY = fY') (W : Y.Opens) (_ : Dense (W : Set ↥Y)) (_ : IsIso (β ∣_ W))
      (U' : X.Opens) (hU' : U' ≤ U) (hzU' : z ∈ U')
      (α' : (U' : Scheme.{u}) ⟶ Y') (_ : α' ≫ β = X.homOfLE hU' ≫ α),
      ringKrullDim (Y'.presheaf.stalk (α'.base ⟨z, hzU'⟩)) = 1 := by

  obtain ⟨O, hO, ℓ₀, hℓ₀, d, hd, g, hgO, hind, φ, hφloc, hφ⟩ :=
    AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one fX fY U α hα hdom z hzU hz₁ hzn hnd

  haveI : LocallyOfFiniteType fY := inferInstance
  obtain ⟨Y', β, W, s, ℓ, y', hY'i, hβ, hWne, hs, hsβ, hsr, hℓβ, hℓy', hdim⟩ :=
    AlgebraicGeometry.exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField k fY O hO ℓ₀ hℓ₀ d hd
      g hgO hind
  haveI := hY'i; haveI := hβ; haveI := hs

  haveI hβW : IsIso (β ∣_ W) := AlgebraicGeometry.isIso_morphismRestrict_of_isOpenImmersion_of_range_eq β W s hsβ hsr

  haveI : LocallyOfFiniteType β := inferInstance
  haveI : X.IsGermInjectiveAt z := inferInstance
  haveI : IsLocalHom φ.hom := hφloc
  obtain ⟨U', hU', hzU', α', hα'β, hα'z⟩ :=
    AlgebraicGeometry.exists_opens_comp_eq_base_eq_of_isLocalHom U α z hzU β ℓ₀ ℓ hℓβ φ hφ

  refine ⟨Y', β ≫ fY, hY'i, inferInstance, β, rfl, W, ?_, hβW, U', hU', hzU', α', hα'β, ?_⟩
  · exact W.2.dense hWne
  · rw [hα'z, hℓy']; exact hdim

end S_AlgebraicGeometry_exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one (solution)
