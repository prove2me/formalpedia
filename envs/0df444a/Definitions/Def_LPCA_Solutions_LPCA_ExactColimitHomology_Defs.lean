-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
-- name    : LPCA_Solutions_LPCA_ExactColimitHomology_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:20:13.583691+00:00
-- url     : https://prove2.me/theorems/0371f2a9-6b6b-49bf-9fa3-1db1e3d7b17f
-- title:
--   Homology comparison under an explicit exact-colimit hypothesis
-- statement:
--   For a ring S and a small index category J, the comparison assumes HasExactColimitsOfShape J (ModuleCat S). Under this explicit hypothesis, the colimit of degree-q homology is isomorphic to degree-q homology of the colimit of nonnegative cochain complexes. In the coproduct application, ModuleCat AB4 supplies the hypothesis; no unrestricted colimit-exactness claim is made.
--
--   The included constructions and necessary compatibility results are:
--
--   - Homology commutes with an actual exact colimit of module complexes. The exactness hypothesis is explicit and is supplied by AB4 for coproducts.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_ExactColimitHomology.lean, selected declarations in lines 19–70; source SHA-256 f8e21f6a3af960019022f2609c82aaa782658a5943646e02f376f850a3d1e2ee; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable (S : Type u) [Ring S]
variable {J : Type u} [SmallCategory J]
variable [HasExactColimitsOfShape J (ModuleCat.{u} S)]

noncomputable def exactDiagramEvaluationHomologyIso
    (A : ShortComplex (J ⥤ ModuleCat.{u} S)) :
    (ShortComplex.functorEquivalence J (ModuleCat.{u} S)).functor.obj A ⋙
        ShortComplex.homologyFunctor (ModuleCat.{u} S) ≅ A.homology :=
  NatIso.ofComponents
    (fun n => A.mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj n)) (by
      intro n m f
      change ShortComplex.homologyMap (A.mapNatTrans ((evaluation J (ModuleCat.{u} S)).map f)) ≫
          (A.mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj m)).hom =
        (A.mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj n)).hom ≫ A.homology.map f
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp)

noncomputable def exactColimitShortComplexHomologyIso
    (A : ShortComplex (J ⥤ ModuleCat.{u} S)) :
    colimit A.homology ≅ (A.map (colim : (J ⥤ ModuleCat.{u} S) ⥤ ModuleCat.{u} S)).homology :=
  (A.mapHomologyIso (colim : (J ⥤ ModuleCat.{u} S) ⥤ ModuleCat.{u} S)).symm

set_option backward.isDefEq.respectTransparency false in
noncomputable def exactComplexDiagramEvaluationHomologyIso
    (D : J ⥤ CochainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) :
    D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q ≅
      ((ShortComplex.functorEquivalence J (ModuleCat.{u} S)).inverse.obj
        (D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q)).homology := by
  let P := D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q
  change P ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} S) ≅ _
  exact Functor.isoWhiskerRight
      ((ShortComplex.functorEquivalence J (ModuleCat.{u} S)).counitIso.app P).symm
      (ShortComplex.homologyFunctor (ModuleCat.{u} S)) ≪≫
    exactDiagramEvaluationHomologyIso S _

set_option backward.isDefEq.respectTransparency false in
noncomputable def exactPointwiseColimitShortComplexIso
    (D : J ⥤ CochainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) :
    (((ShortComplex.functorEquivalence J (ModuleCat.{u} S)).inverse.obj
      (D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q)).map
        (colim : (J ⥤ ModuleCat.{u} S) ⥤ ModuleCat.{u} S)) ≅
      ((HomologicalComplex.coconeOfHasColimitEval D).pt).sc q :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl) (by simp; rfl)

/-- Homology commutes with an actual exact colimit of module complexes.
The exactness hypothesis is explicit and is supplied by AB4 for coproducts. -/
noncomputable def exactColimitHomologyIso
    (D : J ⥤ CochainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) :
    colimit (D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q) ≅
      (colimit D).homology q :=
  HasColimit.isoOfNatIso (exactComplexDiagramEvaluationHomologyIso S D q) ≪≫
    exactColimitShortComplexHomologyIso S _ ≪≫
    (ShortComplex.homologyFunctor (ModuleCat.{u} S)).mapIso (exactPointwiseColimitShortComplexIso S D q) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q).mapIso
      (IsColimit.coconePointUniqueUpToIso
        (HomologicalComplex.isColimitCoconeOfHasColimitEval D) (colimit.isColimit D))

end LPCA


