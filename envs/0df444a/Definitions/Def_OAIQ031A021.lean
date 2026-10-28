-- Prove2me | Definitions.Def_OAIQ031A021
-- name    : OAIQ031A021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:57:19.262703+00:00
-- url     : https://prove2.me/theorems/7d784707-6c31-4e13-8bd1-7894b10a6cf0
-- title:
--   Definitions bundle OAIQ031A021 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 5 definitions and 5 theorems. The definitions and types are `OAI.ArExplicit.gradedConjugate`, `OAI.ArExplicit.negativeShiftIso`, `OAI.ArExplicit.shiftedNegativeHomEquiv`, `OAI.ArExplicit.shiftedNegativeIso`, `OAI.ArExplicit.twoTwistLinear`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_GradedConjugate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/GradedConjugate.lean), [`AuslanderReiten_Coordinates_ShiftedCoordinateProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ShiftedCoordinateProducts.lean), [`AuslanderReiten_Coordinates_ShiftedInverse`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ShiftedInverse.lean), [`AuslanderReiten_Coordinates_ShiftedObjectCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ShiftedObjectCoordinates.lean), [`AuslanderReiten_Coordinates_TwoTwistLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TwoTwistLinear.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A041` and `OAIQ031A042`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ShiftedObjectCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y : C} (n : ℤ) (e : X ≅ Y⟦n⟧)

def negativeShiftIso : Y ≅ X⟦-n⟧ :=
  ((CategoryTheory.shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).app Y).symm ≪≫
    (CategoryTheory.shiftFunctor C (-n)).mapIso e.symm

def shiftedNegativeIso (a : ℤ) : Y⟦a⟧ ≅ X⟦a-n⟧ :=
  (CategoryTheory.shiftFunctor C a).mapIso (negativeShiftIso n e) ≪≫
    (CategoryTheory.shiftFunctorAdd' C (-n) a (a-n) (by omega)).symm.app X

variable (k : Type w) [CommRing k] [Preadditive C] [Linear k C]

def shiftedNegativeHomEquiv (S : C) (a : ℤ) :
    (S ⟶ Y⟦a⟧) ≃ₗ[k] (S ⟶ X⟦a-n⟧) :=
  Linear.homCongr k (Iso.refl S) (shiftedNegativeIso n e a)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ShiftedCoordinateProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y S : C} (n : ℤ) (e : X ≅ Y⟦n⟧)

theorem shiftedNegativeIso_comp (a : ℤ) (v : S ⟶ Y⟦a⟧) :
    v ≫ (shiftedNegativeIso n e a).hom =
      ShiftedHom.comp v (negativeShiftIso n e).hom (by omega : -n+a=a-n) := by
  simp only [shiftedNegativeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, ShiftedHom.comp]

variable (k : Type w) [CommRing k] [Preadditive C] [Linear k C]

theorem shiftedNegativeHomEquiv_comp (a : ℤ) (v : S ⟶ Y⟦a⟧) :
    shiftedNegativeHomEquiv n e k S a v =
      ShiftedHom.comp v (negativeShiftIso n e).hom (by omega : -n+a=a-n) := by
  simpa only [shiftedNegativeHomEquiv, Linear.homCongr_apply, Iso.refl_inv,
    Category.id_comp] using shiftedNegativeIso_comp n e a v

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ShiftedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y : C} (n : ℤ) (e : X ≅ Y⟦n⟧)

theorem negativeShiftIso_comp_hom :
    ShiftedHom.comp (negativeShiftIso n e).hom e.hom (by omega : n + -n = 0) =
      ShiftedHom.mk₀ (0:ℤ) rfl (𝟙 Y) := by
  simp only [negativeShiftIso, ShiftedHom.comp, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp [shiftFunctorCompIsoId, ShiftedHom.mk₀, shiftFunctorZero']

theorem hom_comp_negativeShiftIso :
    ShiftedHom.comp e.hom (negativeShiftIso n e).hom (by omega : -n+n=0) =
      ShiftedHom.mk₀ (0:ℤ) rfl (𝟙 X) := by
  apply (cancel_mono ((CategoryTheory.shiftFunctor C (0:ℤ)).map e.hom ≫
    (shiftFunctorAdd' C n 0 n (add_zero n)).inv.app Y)).mp
  change ShiftedHom.comp (ShiftedHom.comp e.hom (negativeShiftIso n e).hom _) e.hom _ =
    ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl (𝟙 X)) e.hom _
  rw [ShiftedHom.comp_assoc e.hom (negativeShiftIso n e).hom e.hom
    (by omega : -n+n=0) (by omega : n + -n=0) (by omega : n + -n+n=n), negativeShiftIso_comp_hom,
    ShiftedHom.comp_mk₀_id, ShiftedHom.mk₀_id_comp]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_GradedConjugate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y Z S : C} (n m d : ℤ) (h : -n+m=d)
variable (e : X ≅ Y⟦n⟧) (f : X ≅ Z⟦m⟧) (c : Z ⟶ Y)

def gradedConjugate : X ⟶ X⟦d⟧ :=
  ShiftedHom.comp f.hom
    (ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
      (by omega : -n+0= -n)) h

theorem gradedConjugate_comp_hom :
    ShiftedHom.comp (gradedConjugate n m d h e f c) e.hom (by omega : n+d=m) =
      ShiftedHom.comp f.hom (ShiftedHom.mk₀ (0:ℤ) rfl c) (by omega : 0+m=m) := by
  unfold gradedConjugate
  rw [ShiftedHom.comp_assoc f.hom
    (ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
      (by omega : -n+0= -n)) e.hom h (by omega : n+ -n=0) (by omega : n+ -n+m=m)]
  rw [ShiftedHom.comp_assoc (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom e.hom
    (by omega : -n+0= -n) (by omega : n+ -n=0) (by omega : n+ -n+0=0),
    negativeShiftIso_comp_hom, ShiftedHom.comp_mk₀_id]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TwoTwistLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

def twoTwistLinear (a b : k) : (V × V) →ₗ[k] V × V where
  toFun x := (a • x.1 + x.2, b • x.1 + x.2)
  map_add' x y := by ext <;> simp [smul_add] <;> abel
  map_smul' r x := by ext <;> simp [smul_add, smul_comm a r, smul_comm b r]

end ArExplicit

end

end OAI
end


