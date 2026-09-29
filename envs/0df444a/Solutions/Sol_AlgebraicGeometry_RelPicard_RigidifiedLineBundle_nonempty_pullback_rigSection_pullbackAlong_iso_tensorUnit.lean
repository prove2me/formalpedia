-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/02b8aa5c-757f-5463-bcb3-26fa8e554c3e

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

theorem solution
    {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))))
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    Nonempty ((Scheme.Modules.pullback (rigSection c t P)).obj (N.pullbackAlong ⟨t, Category.comp_id t⟩).L ≅
      𝟙_ T.Modules) := by
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k
    ((Scheme.Modules.pullback (rigSection c (𝟙 _) P)).obj N.L) (N.isInvertible.pullback _)
  exact ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c P ⟨t, Category.comp_id t⟩)).app N.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N.L).symm ≪≫
    (Scheme.Modules.pullback t).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso t⟩

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit (solution)
