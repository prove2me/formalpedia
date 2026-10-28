-- Prove2me | Definitions.Def_OAIQ031A008
-- name    : OAIQ031A008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:58:44.882216+00:00
-- url     : https://prove2.me/theorems/9fe0f8f4-6e79-44ff-864b-4466e71515de
-- title:
--   Definitions bundle OAIQ031A008 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 4 definitions, 1 inductive type or structure, 2 instances and 5 theorems. The definitions and types are `OAI.ArExplicit.InductionBimodule`, `OAI.ArExplicit.ResolutionProducts.conjugate`, `OAI.ArExplicit.ResolutionProducts.endExt`, `OAI.ArExplicit.ResolutionProducts.resolutionIso`, `OAI.ArExplicit.totalHomotopyEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_BaseAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/BaseAlgebra.lean), [`AuslanderReiten_Bar_ModuleBarSuffix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarSuffix.lean), [`AuslanderReiten_Homology_BifunctorHomotopyEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/BifunctorHomotopyEquiv.lean), [`AuslanderReiten_Homology_CochainNatTensorSigns`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/CochainNatTensorSigns.lean), [`AuslanderReiten_Modules_InductionBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/InductionBimodule.lean), [`AuslanderReiten_Modules_ModuleRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/ModuleRestriction.lean), [`AuslanderReiten_Resolutions_ResolutionProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionProducts.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A032`, `OAIQ031A033`, `OAIQ031A034` and `OAIQ031A047`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A000

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_BaseAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace BaseAlgebra

variable {k : Type*} (q : k)

variable [CommRing k]

open Letter

theorem fourfold_product :
    ((basisVector q u * basisVector q t) * basisVector q u) * basisVector q t =
      (q * (1 + q)) • basisVector q z := by
  ext coordinate
  cases coordinate <;> simp [product]
  ring

end BaseAlgebra
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarSuffix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

variable [CharP k 2]

theorem double_zero_p1 {V : Type u} [AddCommGroup V] [Module k V] (x : V) : x + x = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [← two_smul k x, htwo, zero_smul]

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_BifunctorHomotopyEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c : ComplexShape ℕ} [TotalComplexShape c c c]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (P : HomologicalComplex C₁ c) (Q : HomologicalComplex C₂ c),
    HasMapBifunctor P Q F c]

theorem totalMap_id (P : HomologicalComplex C₁ c) (Q : HomologicalComplex C₂ c) :
    mapBifunctorMap (𝟙 P) (𝟙 Q) F c = 𝟙 _ := by
  ext n : 1
  apply mapBifunctor.hom_ext
  intro i j h
  simp

theorem totalMap_comp {P P' P'' : HomologicalComplex C₁ c}
    {Q Q' Q'' : HomologicalComplex C₂ c} (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    mapBifunctorMap f g F c ≫
      mapBifunctorMap f' g' F c =
    mapBifunctorMap (f ≫ f') (g ≫ g') F c := by
  ext n : 1
  apply mapBifunctor.hom_ext
  intro i j h
  simp only [comp_f, Category.assoc, ι_mapBifunctorMap_assoc, ι_mapBifunctorMap,
    Functor.map_comp, NatTrans.comp_app]
  simp only [NatTrans.naturality_assoc]

def totalHomotopyEquiv {P P' : HomologicalComplex C₁ c} {Q Q' : HomologicalComplex C₂ c}
    (e : HomotopyEquiv P P') (f : HomotopyEquiv Q Q') :
    HomotopyEquiv (mapBifunctor P Q F c)
      (mapBifunctor P' Q' F c) where
  hom := mapBifunctorMap e.hom f.hom F c
  inv := mapBifunctorMap e.inv f.inv F c
  homotopyHomInvId :=
    (Homotopy.ofEq (totalMap_comp F e.hom e.inv f.hom f.inv)).trans
      ((mapBifunctorMapHomotopy₁ e.homotopyHomInvId (f.hom ≫ f.inv) F
        c).trans
        ((mapBifunctorMapHomotopy₂ (𝟙 P) f.homotopyHomInvId F
          c).trans (Homotopy.ofEq (totalMap_id F P Q))))
  homotopyInvHomId :=
    (Homotopy.ofEq (totalMap_comp F e.inv e.hom f.inv f.hom)).trans
      ((mapBifunctorMapHomotopy₁ e.homotopyInvHomId (f.inv ≫ f.hom) F
        c).trans
        ((mapBifunctorMapHomotopy₂ (𝟙 P') f.homotopyInvHomId F
          c).trans (Homotopy.ofEq (totalMap_id F P' Q'))))

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_CochainNatTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

instance cochainNatTensorSigns : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (i : Multiplicative ℕ) => (-1 : ℤˣ)^i.toAdd)
    (fun i j => pow_add (-1 : ℤˣ) i.toAdd j.toAdd)
  rel_add p q r (h : p+1=q) := by change (p+r)+1=q+r; omega
  add_rel p q r (h : p+1=q) := by change (r+p)+1=r+q; omega
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ)^(p+1) = -(-1 : ℤˣ)^p
    exact (pow_succ (-1 : ℤˣ) p).trans (by simp)

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_InductionBimodule
attribute [-instance] _root_.OAI.ArExplicit.cochainNatTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

@[ext] structure InductionBimodule {k R S : Type*} [CommRing k] [Ring R] [Ring S]
    [Algebra k R] [Algebra k S] (ι : R →ₐ[k] S) where
  value : S

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_ModuleRestriction
attribute [-instance] _root_.OAI.ArExplicit.cochainNatTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
namespace ArExplicit.ModuleRestriction
universe v u u'
variable {R : Type u} {S : Type u'} [Ring R] [Ring S] (f : R →+* S)

theorem map_exact (s : ShortComplex (ModuleCat.{v} S)) (h : s.Exact) :
    (s.map (ModuleCat.restrictScalars f)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

noncomputable instance preservesHomology : (ModuleCat.restrictScalars.{v} f).PreservesHomology :=
  ((Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 1 2).mp (map_exact f)

end ArExplicit.ModuleRestriction

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.cochainNatTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

def conjugate {X Y : DerivedCategory C} (e : X ≅ Y) {n : ℤ}
    (f : ShiftedHom X X n) : ShiftedHom Y Y n :=
  e.inv ≫ f ≫ (CategoryTheory.shiftFunctor (DerivedCategory C) n).map e.hom

def resolutionIso {X : C} (P : ProjectiveResolution X) :
    DerivedCategory.Q.obj P.cochainComplex ≅ (DerivedCategory.singleFunctor C 0).obj X :=
  asIso (DerivedCategory.Q.map P.π') ≪≫ (DerivedCategory.singleFunctorIsoCompQ C 0).symm.app X

variable [HasExt.{v} C]

def endExt {X : C} (P : ProjectiveResolution X) {n : ℕ}
    (x : Cocycle P.cochainComplex P.cochainComplex (n : ℤ)) : Ext X X n :=
  Ext.homEquiv.symm (conjugate (resolutionIso P)
    (ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q))

end ArExplicit.ResolutionProducts

end

end OAI
end


