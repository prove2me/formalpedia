-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_eq_pullbackUnitIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1e958683-bf8d-5d02-b997-8065fa284404

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_eq_pullbackUnitIso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pullbackTensorUnitObjIso f = Scheme.Modules.pullbackUnitIso f := by
  refine Iso.ext ?_
  apply AlgebraicGeometry.Scheme.Modules.pullback_hom_ext
  intro U s

  let r : Γ(Y, U) := AlgebraicGeometry.Scheme.Modules.ofUnitSection U s
  have hs : s = r • AlgebraicGeometry.Scheme.Modules.unitSection U :=
    (AlgebraicGeometry.Scheme.Modules.smul_unitSection r).symm

  have lhs : (AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ U)
        (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection f s)
      = (f.app U r : Γ(X, f ⁻¹ᵁ U)) := by
    rw [hs, AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_smul, AlgebraicGeometry.Scheme.Modules.Hom.app_smul,
      AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2,
      AlgebraicGeometry.Scheme.Modules.smul_unitSection]

  have rhs : (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
        (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection f s)
      = (f.app U r : Γ(X, f ⁻¹ᵁ U)) :=
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2 f U r
  exact lhs.trans rhs.symm

end S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_eq_pullbackUnitIso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_eq_pullbackUnitIso (solution)
