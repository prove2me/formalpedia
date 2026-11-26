-- Prove2me | Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
-- name    : ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:10:02.691305+00:00
-- url     : https://prove2.me/theorems/73352dd6-eb86-56ce-95e2-e6402e2eb372
-- title:
--   Forgetful functors from commutative algebras preserve filtered colimits
-- statement:
--   The forgetful functors from commutative $R$-algebras to commutative rings, to $R$-algebras and to types, and from $R$-algebras to $R$-modules, preserve filtered colimits.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Category/CommAlgCat/Limits.lean (declarations kept unchanged, unused ones removed).

import Mathlib
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u

open CategoryTheory Limits
open scoped MonoidalCategory

namespace CommAlgCat

variable {R : Type u} [CommRing R]

-- `AI generated`


-- `forget₂ (CommAlgCat R) CommRingCat` preserves filtered colimits because it factors as
-- `(commAlgCatEquivUnder R).functor ⋙ Under.forget R`, where the equivalence preserves all
-- colimits and `Under.forget` preserves connected (hence filtered) colimits.
instance preservesFilteredColimitsOfSize_forget_commRingCat :
    PreservesFilteredColimitsOfSize.{u, u} (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) where
  preserves_filtered_colimits J _ _ := by
    have : IsConnected J := IsFiltered.isConnected J
    exact (inferInstance :
      PreservesColimitsOfShape J
        ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
          Under.forget (CommRingCat.of R)))

instance preservesFilteredColimitsOfSize_forget (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize.{u, u} (forget (CommAlgCat.{u} R)) :=
  HasForget₂.forget_comp (C := CommAlgCat.{u} R) (D := CommRingCat.{u}) ▸
    (Limits.comp_preservesFilteredColimits
        (forget₂ (CommAlgCat.{u} R) CommRingCat.{u})
        (forget CommRingCat.{u}) : PreservesFilteredColimitsOfSize.{u, u} _)

instance preservesFilteredColimitsOfSize_forget_algCat (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize.{u, u} (forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R)) where
  preserves_filtered_colimits J _ _ := by
    have h : forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget (AlgCat.{u} R) =
        forget (CommAlgCat.{u} R) := HasForget₂.forget_comp
    have : HasColimitsOfShape J (AlgCat.{u} R) :=
      { has_colimit := fun F ↦ ⟨_, AlgCat.FilteredColimits.colimitCoconeIsColimit F⟩ }
    have : PreservesColimitsOfShape J (forget (AlgCat.{u} R)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : ReflectsColimitsOfShape J (forget (AlgCat.{u} R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms (J := J) (G := forget (AlgCat.{u} R))
    have hpres : PreservesColimitsOfShape J (forget (CommAlgCat.{u} R)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : PreservesColimitsOfShape J
        (forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget (AlgCat.{u} R)) :=
      h.symm ▸ hpres
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R)) (forget (AlgCat.{u} R))


instance AlgCat.preservesFilteredColimitsOfSize_forget_moduleCat (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize.{u, u} (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) where
  preserves_filtered_colimits J _ _ := by
    have h : forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ⋙ forget (ModuleCat.{u} R) =
        forget (AlgCat.{u} R) := HasForget₂.forget_comp
    have : PreservesColimitsOfShape J (forget (ModuleCat.{u} R)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : ReflectsColimitsOfShape J (forget (ModuleCat.{u} R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms (J := J) (G := forget (ModuleCat.{u} R))
    have hpres : PreservesColimitsOfShape J (forget (AlgCat.{u} R)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : PreservesColimitsOfShape J
        (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ⋙ forget (ModuleCat.{u} R)) :=
      h.symm ▸ hpres
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) (forget (ModuleCat.{u} R))

end CommAlgCat


