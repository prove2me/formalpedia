-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.IsUniversal.isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/53e69326-7183-5c95-80a9-87730e2693ea

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap
import Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base
import Theorems.Thm_AlgebraicGeometry_IsSeparated_of_comp_of_universallyClosed_of_surjective
import Theorems.Thm_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f]
    [IsLocallyNoetherian S] {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S}
    {Duniv : RelEffCartierDiv f r y} (hU : Duniv.IsUniversal) : IsProper y := by
  obtain ⟨σ, hσ, -, hfin, hflat, -, hsurj, -⟩ := hU.exists_sumMap
  have hp : IsProper (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @IsProper) (fun _ : Fin r ↦ 𝒞) (fun _ ↦ f)
      fun _ ↦ inferInstance
  have : IsProper (σ ≫ y) := by rw [hσ]; exact hp
  exact @IsProper.mk _ _ y (IsSeparated.of_comp_of_universallyClosed_of_surjective σ y)
    (UniversallyClosed.of_comp_surjective σ y)
    (LocallyOfFiniteType.of_comp_of_isFinite_of_flat_of_surjective σ y)

end S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_isProper (solution)
