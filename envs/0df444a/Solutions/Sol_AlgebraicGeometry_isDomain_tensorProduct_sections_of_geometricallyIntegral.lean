-- Prove2me | solution 1 for AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/61252206-ebc1-5d9e-8d4b-7028032edf32

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace NoncritGeom

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (U : C.Opens) (hU : IsAffineOpen U) (K : Type u) [Field K] [Algebra R K]

theorem ι_comp_eq :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    U.ι ≫ c = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(C, U))) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have h1 : hU.fromSpec ≫ c = Spec.map (c.appLE ⊤ U le_top) ≫ (isAffineOpen_top (Spec (.of R))).fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top _) hU le_top).symm
  have h2 : (isAffineOpen_top (Spec (CommRingCat.of R))).fromSpec = Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have h3 : (CommRingCat.ofHom (algebraMap R Γ(C, U))) = (Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top := rfl
  rw [h3, Spec.map_comp, ← h2, ← h1, ← Category.assoc, IsAffineOpen.isoSpec_hom hU,
    ← IsAffineOpen.isoSpec_inv_ι hU, ← Category.assoc, ← IsAffineOpen.isoSpec_hom hU, Iso.hom_inv_id,
    Category.id_comp]

noncomputable def preimageIso :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (↑((pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ U) : Scheme.{u}) ≅
      Spec (.of (Γ(C, U) ⊗[R] K)) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  (pullbackRestrictIsoRestrict (pullback.fst c g) U).symm
    ≪≫ pullbackSymmetry _ _
    ≪≫ pullbackRightPullbackFstIso c g U.ι
    ≪≫ asIso (pullback.map (U.ι ≫ c) g (Spec.map (CommRingCat.ofHom (algebraMap R Γ(C, U)))) g
          hU.isoSpec.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ι_comp_eq c U hU]) (by simp))
    ≪≫ pullbackSpecIso R Γ(C, U) K

include hU in
private theorem _root_.NoncritGeom.isDomain (hne : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Nontrivial (K ⊗[R] Γ(C, U)))
    [GeometricallyIntegral c] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    IsDomain (K ⊗[R] Γ(C, U)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  haveI : IsIntegral (pullback c g) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c g)
  let U' : (pullback c g).Opens := (pullback.fst c g) ⁻¹ᵁ U
  let e : (↑U' : Scheme.{u}) ≅ Spec (.of (Γ(C, U) ⊗[R] K)) := preimageIso c U hU K

  haveI := hne
  haveI : Nontrivial (Γ(C, U) ⊗[R] K) := (Algebra.TensorProduct.comm R Γ(C, U) K).toEquiv.nontrivial
  haveI : Nonempty (Spec (CommRingCat.of (Γ(C, U) ⊗[R] K))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Γ(C, U) ⊗[R] K)))
  haveI : Nonempty U' := ⟨e.inv.base (Classical.arbitrary _)⟩
  haveI : IsIntegral (↑U' : Scheme.{u}) := inferInstance
  haveI : IsIntegral (Spec (CommRingCat.of (Γ(C, U) ⊗[R] K))) := IsIntegral.of_isIso e.hom
  haveI : IsDomain Γ(Spec (CommRingCat.of (Γ(C, U) ⊗[R] K)), ⊤) := inferInstance
  haveI : IsDomain (Γ(C, U) ⊗[R] K) :=
    MulEquiv.isDomain Γ(Spec (CommRingCat.of (Γ(C, U) ⊗[R] K)), ⊤)
      (Scheme.ΓSpecIso (.of (Γ(C, U) ⊗[R] K))).commRingCatIsoToRingEquiv.symm.toMulEquiv
  exact MulEquiv.isDomain (Γ(C, U) ⊗[R] K) (Algebra.TensorProduct.comm R K Γ(C, U)).toMulEquiv

p2m_export "NoncritGeom" "isDomain"
end NoncritGeom

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [GeometricallyIntegral c] (U : C.Opens) (hU : IsAffineOpen U)
    (K : Type u) [Field K] [Algebra R K]
    (hne : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Nontrivial (K ⊗[R] Γ(C, U))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    IsDomain (K ⊗[R] Γ(C, U)) :=
  NoncritGeom.isDomain c U hU K hne

end S_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral (solution)
