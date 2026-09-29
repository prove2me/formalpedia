-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/52a7eb01-a00f-511f-a930-fc718b793e66

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.dual Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.IsInvertible.dual_monoidalV2"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules Modules.IsInvertible Modules.dual Modules.pullbackTensorUnitObjIso Modules.IsInvertible.dual_monoidalV2"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback IsInvertible dual pullbackTensorUnitObjIso IsInvertible.dual_monoidalV2"
namespace InverseUnique
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

noncomputable def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

end AlgebraicGeometry.Scheme.Modules.InverseUnique

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.InverseUnique in
theorem solution
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Modules.dual L) ≅
      AlgebraicGeometry.Scheme.Modules.dual ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L)) := by
  obtain ⟨eL⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hL).2
  obtain ⟨e'⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 (hL.pullback f)).2

  let e : (Scheme.Modules.pullback f).obj L ⊗ (Scheme.Modules.pullback f).obj (Scheme.Modules.dual L) ≅
      𝟙_ X.Modules :=
    Functor.Monoidal.μIso (Scheme.Modules.pullback f) L (Scheme.Modules.dual L) ≪≫
      (Scheme.Modules.pullback f).mapIso eL ≪≫ Scheme.Modules.pullbackTensorUnitObjIso f
  exact ⟨inverseUnique e e'⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2 (solution)
