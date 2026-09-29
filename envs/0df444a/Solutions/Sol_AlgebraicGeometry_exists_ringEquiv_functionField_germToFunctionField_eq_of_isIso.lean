-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/06f5b03e-06b0-50fe-b323-b966fb8ba7e5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsIso f] :
    ∃ ι : Y.functionField ≃+* X.functionField,
      ∀ (V : Y.Opens) [Nonempty (V : Scheme.{u})] [Nonempty ((f ⁻¹ᵁ V : X.Opens) : Scheme.{u})] (t : Γ(Y, V)),
        ι (Y.germToFunctionField V t) = X.germToFunctionField (f ⁻¹ᵁ V) (f.app V t) := by
  have hgen : f.base (genericPoint X) = genericPoint Y := genericPoint_eq_of_isOpenImmersion f
  let e₁ : Y.presheaf.stalk (genericPoint Y) ≅ Y.presheaf.stalk (f.base (genericPoint X)) :=
    Y.presheaf.stalkCongr (.of_eq hgen.symm)
  let e₂ : Y.presheaf.stalk (f.base (genericPoint X)) ≅ X.presheaf.stalk (genericPoint X) :=
    asIso (f.stalkMap (genericPoint X))
  refine ⟨(e₁ ≪≫ e₂).commRingCatIsoToRingEquiv, ?_⟩
  intro V _ _ t
  have hmem : f.base (genericPoint X) ∈ V := by
    rw [hgen]
    exact ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty (V : Scheme.{u})›)
  change (e₁ ≪≫ e₂).hom (Y.presheaf.germ V (genericPoint Y) _ t) = X.presheaf.germ (f ⁻¹ᵁ V) (genericPoint X) _ (f.app V t)
  simp only [Iso.trans_hom, CommRingCat.comp_apply, e₁, e₂, asIso_hom]
  have h1 : (Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom (Y.presheaf.germ V (genericPoint Y)
      (((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty (V : Scheme.{u})›)) t) =
      Y.presheaf.germ V (f.base (genericPoint X)) hmem t := by
    simp only [TopCat.Presheaf.stalkCongr_hom]
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rw [h1, Scheme.Hom.germ_stalkMap_apply]

#print axioms solution

end S_AlgebraicGeometry_exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso (solution)
