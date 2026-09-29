-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.IsUniversal.geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1478ee46-16f9-5aa8-a21d-bfaefbe42f47

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap
import Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base
import Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension.smooth SmoothOfRelativeDimension geometrically_iff_of_isClosedUnderIsomorphisms GeometricallyConnected.comp Scheme Smooth UniversallyOpen IsSeparated GeometricallyConnected geometrically RelEffCartierDiv.IsUniversal RelEffCartierDiv fibrePowOver fibrePowOver.toBase RelEffCartierDiv.IsUniversal.exists_sumMap GeometricallyConnected.of_comp_of_surjective"
p2m_open "AlgebraicGeometry"

namespace GeometricallyConnected p2m_export "AlgebraicGeometry.GeometricallyConnected" "comp of_comp_of_surjective" end GeometricallyConnected
p2m_open_scoped "AlgebraicGeometry.GeometricallyConnected" in

theorem GeometricallyConnected.id (X : Scheme.{u}) : GeometricallyConnected (𝟙 X) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ k ↦ ?_⟩
  rw [(pullback.snd (𝟙 X) k).homeomorph.connectedSpace_iff]
  infer_instance

theorem isMultiplicative_geometricallyConnected_inf_universallyOpen :
    (@GeometricallyConnected ⊓ @UniversallyOpen : MorphismProperty Scheme.{u}).IsMultiplicative where
  id_mem X := ⟨GeometricallyConnected.id X, inferInstance⟩
  comp_mem f g hf hg := by
    obtain ⟨hf₁, hf₂⟩ := hf
    obtain ⟨hg₁, hg₂⟩ := hg
    exact ⟨GeometricallyConnected.comp f g, inferInstance⟩

end AlgebraicGeometry

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyConnected f] {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S}
    {Duniv : RelEffCartierDiv f r y} (hU : Duniv.IsUniversal) : GeometricallyConnected y := by
  obtain ⟨σ, hσ, -, -, -, -, hsurj, -⟩ := hU.exists_sumMap
  have : Smooth f := SmoothOfRelativeDimension.smooth (n := 1) (f := f)
  have : UniversallyOpen f := inferInstance
  have := isMultiplicative_geometricallyConnected_inf_universallyOpen.{u}
  have hGC : (@GeometricallyConnected ⊓ @UniversallyOpen : MorphismProperty Scheme.{u})
      (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @GeometricallyConnected ⊓ @UniversallyOpen)
      (fun _ : Fin r ↦ 𝒞) (fun _ ↦ f) fun _ ↦ ⟨‹_›, ‹_›⟩
  have : GeometricallyConnected (σ ≫ y) := by rw [hσ]; exact hGC.1
  exact GeometricallyConnected.of_comp_of_surjective σ y

end S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected (solution)
