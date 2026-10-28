-- Prove2me | Definitions.Def_OAIQ031A014
-- name    : OAIQ031A014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:56:27.166986+00:00
-- url     : https://prove2.me/theorems/500bf8cd-6e60-44c8-8f2e-1e130e57fa94
-- title:
--   Definitions bundle OAIQ031A014 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 6 definitions and 9 theorems. The definitions and types are `OAI.ArExplicit.ConeCokernel.Left`, `OAI.ArExplicit.ResolutionProducts.mapExtendIso`, `OAI.ArExplicit.ResolutionProducts.mapExtendXIso`, `OAI.ArExplicit.ResolutionProducts.mapResolution`, `OAI.ArExplicit.ResolutionProducts.mapResolutionCochainIso`, `OAI.ArExplicit.ResolutionProducts.mappedResolutionCocycle`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_CompleteFunctorRawEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteFunctorRawEndpoint.lean), [`AuslanderReiten_Complete_CompleteTailExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailExt.lean), [`AuslanderReiten_Cones_ConeCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeCokernel.lean), [`AuslanderReiten_Coordinates_MapExtend`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/MapExtend.lean), [`AuslanderReiten_Resolutions_MapResolutionCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/MapResolutionCochain.lean), [`AuslanderReiten_Resolutions_MapResolutionExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/MapResolutionExt.lean), [`AuslanderReiten_Resolutions_ProjectiveResolutionFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ProjectiveResolutionFunctor.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A036`, `OAIQ031A038` and `OAIQ031A040`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ProjectiveResolutionFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [F.PreservesProjectiveObjects]
variable {X : C} (P : ProjectiveResolution X)

def mapResolution : ProjectiveResolution (F.obj X) where
  complex := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  projective n := F.projective_obj_of_projective (P.projective n)
  π := (F.mapHomologicalComplex (.down ℕ)).map P.π ≫
    (singleMapHomologicalComplex F (.down ℕ) 0).hom.app X
  quasiIso := by infer_instance

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_MapExtend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory Category Limits ZeroObject HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

def mapExtendXIso (K : HomologicalComplex C c) : ∀ i : Option ι,
    extend.X ((F.mapHomologicalComplex c).obj K) i ≅ F.obj (extend.X K i)
  | some _ => Iso.refl _
  | none => (F.mapZeroObject).symm

theorem mapExtendXIso_d (K : HomologicalComplex C c) (i j : Option ι) :
    (mapExtendXIso F K i).hom ≫ F.map (extend.d K i j) =
      extend.d ((F.mapHomologicalComplex c).obj K) i j ≫
        (mapExtendXIso F K j).hom := by
  cases i with
  | none => exact (isZero_zero D).eq_of_src _ _
  | some i =>
    cases j with
    | none =>
      change (𝟙 (F.obj (K.X i))) ≫ F.map (0 : K.X i ⟶ (0 : C)) =
        (0 : F.obj (K.X i) ⟶ (0 : D)) ≫ (F.mapZeroObject).inv
      simp
    | some j =>
      change (𝟙 (F.obj (K.X i))) ≫ F.map (K.d i j) =
        F.map (K.d i j) ≫ (𝟙 (F.obj (K.X j)))
      simp

def mapExtendIso (K : HomologicalComplex C c) (e : c.Embedding c') :
    ((F.mapHomologicalComplex c).obj K).extend e ≅
      (F.mapHomologicalComplex c').obj (K.extend e) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => mapExtendXIso F K (e.r i))
    (fun i j _ => mapExtendXIso_d F K (e.r i) (e.r j))

theorem mapExtendXIso_hom_XIso (K : HomologicalComplex C c) {i : Option ι} {j : ι}
    (h : i = some j) :
    (mapExtendXIso F K i).hom ≫ F.map (extend.XIso K h).hom =
      (extend.XIso ((F.mapHomologicalComplex c).obj K) h).hom := by
  subst i
  change 𝟙 (F.obj (K.X j)) ≫ F.map (𝟙 (K.X j)) = 𝟙 (F.obj (K.X j))
  simp

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_MapResolutionCochain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory Category Limits ZeroObject HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [F.PreservesProjectiveObjects]
variable {X : C} (P : ProjectiveResolution X)

omit [Abelian C] [Abelian D] [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] in
theorem map_composite_cancel {U V W Z : C} {U' Z' : D}
    (a : U' ⟶ F.obj U) (b : U ⟶ V) (f : V ⟶ W) (e : W ≅ Z) (t : F.obj W ⟶ Z') :
    a ≫ F.map (b ≫ f ≫ e.hom) ≫ (F.map e.inv ≫ t) =
      (a ≫ F.map b) ≫ F.map f ≫ t := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc e.hom e.inv t, e.hom_inv_id, F.map_id, id_comp]

def mapResolutionCochainIso : (mapResolution F P).cochainComplex ≅
    (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex :=
  mapExtendIso F P.complex ComplexShape.embeddingDownNat

theorem mapResolutionCochainIso_coordinate (n : ℤ) (j : ℕ) (h : -(j : ℤ) = n) :
    (mapResolutionCochainIso F P).hom.f n ≫ F.map (P.cochainComplexXIso n j h).hom =
      ((mapResolution F P).cochainComplexXIso n j h).hom :=
  mapExtendXIso_hom_XIso F P.complex (ComplexShape.embeddingDownNat.r_eq_some h)

theorem mapResolution_π_zero : (mapResolution F P).π.f 0 = F.map (P.π.f 0) := by
  change F.map (P.π.f 0) ≫ ((singleMapHomologicalComplex F (.down ℕ) 0).hom.app X).f 0 = _
  rw [singleMapHomologicalComplex_hom_app_self]
  change F.map (P.π.f 0) ≫ (F.map (𝟙 X) ≫ 𝟙 (F.obj X)) = _
  simp

theorem mapResolutionCochainIso_π :
    (mapResolutionCochainIso F P).hom ≫
      (F.mapHomologicalComplex (.up ℤ)).map P.π' ≫
        (F.mapCochainComplexSingleFunctor 0).hom.app X = (mapResolution F P).π' := by
  apply to_single_hom_ext
  change (mapResolutionCochainIso F P).hom.f 0 ≫ F.map (P.π'.f 0) ≫
    ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app X).f 0 = (mapResolution F P).π'.f 0
  rw [P.π'_f_zero,
    (mapResolution F P).π'_f_zero, mapResolution_π_zero,
    singleMapHomologicalComplex_hom_app_self]
  have he := map_composite_cancel F ((mapResolutionCochainIso F P).hom.f 0)
    (P.cochainComplexXIso 0 0 (by simp)).hom (show P.complex.X 0 ⟶ X from P.π.f 0)
    (singleObjXSelf (.up ℤ) 0 X).symm (singleObjXSelf (.up ℤ) 0 (F.obj X)).inv
  exact he.trans (congrArg (fun a => a ≫ F.map (P.π.f 0) ≫
    (singleObjXSelf (.up ℤ) 0 (F.obj X)).inv) (mapResolutionCochainIso_coordinate F P 0 0 (by simp)))

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_MapResolutionExt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Localization
open CochainComplex CochainComplex.HomComplex HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F : C ⥤ D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
  [CategoryTheory.Limits.PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X Y : C} (P : ProjectiveResolution X) {n : ℕ}

def mappedResolutionCocycle
    (x : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    Cocycle (mapResolution F P).cochainComplex
      ((CochainComplex.singleFunctor D 0).obj (F.obj Y)) (n : ℤ) :=
  Cocycle.equivHomShift ((mapResolutionCochainIso F P).hom ≫
    ShiftedHom.map (Cocycle.equivHomShift.symm x) (F.mapHomologicalComplex (.up ℤ)) ≫
      ((F.mapCochainComplexSingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧')

theorem precomp_extOfCocycle
    (x : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    (SmallShiftedHom.mk₀ (quasiIso C (.up ℤ)) 0 rfl P.π').comp
      (P.extEquivCohomologyClass.symm (CohomologyClass.mk x)) (add_zero (n : ℤ)) =
        SmallShiftedHom.mk (quasiIso C (.up ℤ)) (Cocycle.equivHomShift.symm x) := by
  have hπ : quasiIso C (.up ℤ) P.π' := by rw [mem_quasiIso_iff]; infer_instance
  change (SmallShiftedHom.precompEquiv P.π' hπ)
    ((SmallShiftedHom.precompEquiv P.π' hπ).symm
      (CohomologyClass.equivOfIsKProjective (CohomologyClass.mk x))) = _
  rw [Equiv.apply_symm_apply]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteFunctorRawEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]

theorem raw_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {K₀ P₀ X X' : C} {FK₀ FP₀ Y Y' : D}
    (t : P₀ ≅ K₀) (s : FP₀ ≅ FK₀) (u : FK₀ ≅ F.obj K₀)
    (e : X ≅ X') (d : Y ≅ Y') (E : Y ≅ F.obj X)
    (p : P₀ ⟶ X) (q : K₀ ⟶ X') (p' : FP₀ ⟶ Y) (q' : FK₀ ⟶ Y')
    (h : p ≫ e.hom = t.hom ≫ q) (h' : p' ≫ d.hom = s.hom ≫ q')
    (hE : (s.hom ≫ u.hom ≫ F.map t.inv) ≫ F.map p = p' ≫ E.hom) :
    u.hom ≫ F.map q = q' ≫ d.inv ≫ E.hom ≫ F.map e.hom := by
  apply (cancel_epi s.hom).1
  calc
    s.hom ≫ u.hom ≫ F.map q =
        ((s.hom ≫ u.hom ≫ F.map t.inv) ≫ F.map p) ≫ F.map e.hom := by
      simp only [Category.assoc, ← F.map_comp, h, t.inv_hom_id_assoc]
    _ = (p' ≫ E.hom) ≫ F.map e.hom := congrArg (fun z => z ≫ F.map e.hom) hE
    _ = s.hom ≫ q' ≫ d.inv ≫ E.hom ≫ F.map e.hom := by
      have hp : p' = s.hom ≫ q' ≫ d.inv := by
        rw [← Category.assoc, ← h']
        simp
      rw [hp]
      simp only [Category.assoc]

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailExt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R S : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
  [Ring S] [Algebra k S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S)

theorem augmented_square {A B X : ModuleCat.{u} R}
    {A' B' X' : ModuleCat.{u} S} (a : A' ⟶ B') (b : A ⟶ B)
    (u : A' ⟶ F.obj A) (v : B' ⟶ F.obj B)
    (π : B ⟶ X) (π' : B' ⟶ X') (e : X' ≅ F.obj X)
    (hab : a ≫ v = u ≫ F.map b) (hπ : v ≫ F.map π = π' ≫ e.hom) :
    a ≫ π' = (u ≫ F.map (b ≫ π)) ≫ e.inv := by
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [← hπ, ← Category.assoc, hab, Category.assoc, ← F.map_comp]

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeCokernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

variable {R M N E : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup E] [Module R E]

namespace ConeCokernel

variable {Q₀ Q₁ P₀ P₁ P₂ : Type*}
variable [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup Q₁] [Module R Q₁]
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₂] [Module R P₂]
variable (dQ : Q₁ →ₗ[R] Q₀) (dP : P₁ →ₗ[R] P₀) (f : P₁ →ₗ[R] Q₀)

abbrev Left := Q₀ ⧸ LinearMap.range dQ

end ConeCokernel
end ArExplicit

end

end OAI
end


