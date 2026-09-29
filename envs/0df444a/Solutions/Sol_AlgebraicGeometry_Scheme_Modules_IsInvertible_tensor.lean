-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a559a20f-8165-56e4-8922-61731d4b3e9b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Modules.pullbackCongr Modules Opens homOfLE_ι restrict Modules.pullbackComp Modules.IsInvertible Modules.pullbackUnitIso"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback pullbackCongr restrict pullbackComp IsInvertible pullbackUnitIso tensor pullbackTensorObjIso"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

noncomputable def trivializationOfLE {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (L : X.Modules)
    (e : (Modules.pullback U.ι).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    (Modules.pullback V.ι).obj L ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
  (Modules.pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    ((Modules.pullbackComp (X.homOfLE h) U.ι).symm).app L ≪≫
    (Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor.AlgebraicGeometry.Scheme.Modules in
theorem solution {X : AlgebraicGeometry.Scheme.{u}}
    {L M : X.Modules} (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (L ⊗ M) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.1 x
  obtain ⟨U', hxU', ⟨eU'⟩⟩ := hM.1 x
  refine ⟨U ⊓ U', ⟨hxU, hxU'⟩, ⟨?_⟩⟩
  exact pullbackTensorObjIso (U ⊓ U').ι L M ≪≫
    (trivializationOfLE inf_le_left L eU ⊗ᵢ trivializationOfLE inf_le_right M eU') ≪≫
    λ_ (𝟙_ _)

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor (solution)
