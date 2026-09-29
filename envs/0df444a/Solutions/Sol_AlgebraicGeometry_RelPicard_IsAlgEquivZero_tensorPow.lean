-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsAlgEquivZero.tensorPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/91aa4761-d69d-5bcf-a1f4-7641a643e806

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard"

namespace AezTensorPow

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard"

private theorem _root_.AezTensorPow.unit {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) :
    IsAlgEquivZero a (𝟙_ A.Modules) := by
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    SheafOfModules.unit (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf,
    Scheme.Modules.isInvertible_unit _, ⟨𝟙 _, Category.comp_id _⟩, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm

p2m_export "AezTensorPow" "unit"
theorem main {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)} {L : A.Modules}
    (hL : IsAlgEquivZero a L) (n : ℕ) : IsAlgEquivZero a (L.tensorPow n) := by
  induction n with
  | zero => exact unit a
  | succ n ih =>
    rw [Scheme.Modules.tensorPow_succ]
    exact ih.tensor hL

end AezTensorPow

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard in
theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)} {L : A.Modules}
    (hL : IsAlgEquivZero a L) (n : ℕ) : IsAlgEquivZero a (L.tensorPow n) :=
  AezTensorPow.main hL n

end S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow (solution)
