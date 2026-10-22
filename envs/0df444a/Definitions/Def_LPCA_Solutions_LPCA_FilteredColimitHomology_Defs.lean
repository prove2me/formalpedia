-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
-- name    : LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:19:56.839038+00:00
-- url     : https://prove2.me/theorems/be940872-5885-48e4-b413-c38966cafcc2
-- title:
--   Sequential module colimits commute with cochain homology
-- statement:
--   For a ring S, a natural-number-indexed diagram of nonnegative cochain complexes of S-modules, and q a natural number, this bundle constructs the canonical isomorphism from the colimit of degree-q homology to degree-q homology of the colimit complex. Exactness of this sequential colimit is supplied by ModuleCat AB5. This does not assert that arbitrary colimits preserve homology.
--
--   The included constructions and necessary compatibility results are:
--
--   - Pointwise homology of a short complex of diagrams, with its actual transition maps, is the homology diagram.
--   - Exact filtered colimits commute with this actual short-complex homology. The filtered-colimit exactness comes from ModuleCat's AB5 instance.
--   - The short complex of pointwise colimits is the short complex of the explicit pointwise-colimit cochain complex, with the same differentials.
--   - Exact filtered colimits commute with actual cochain homology. This construction uses AB5 and the canonical termwise-colimit complex.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_FilteredColimitHomology.lean, selected declarations in lines 18–89; source SHA-256 ad20f5adfe790f1be33bdce94580bdbeb0a6c2eaf10921dc01d3deb397d87e90; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Limits

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable (S : Type u) [Ring S]

noncomputable local instance natColimitPreservesHomology :
    (colim : (ℕ ⥤ ModuleCat.{u} S) ⥤ ModuleCat.{u} S).PreservesHomology := by
  letI : AB5OfSize.{0, 0} (ModuleCat.{u} S) := AB5OfSize_of_univLE (ModuleCat.{u} S)
  infer_instance

/-- Pointwise homology of a short complex of diagrams, with its actual
transition maps, is the homology diagram. -/
noncomputable def shortComplexEvaluationHomologyIso
    (A : ShortComplex (ℕ ⥤ ModuleCat.{u} S)) :
    (ShortComplex.functorEquivalence ℕ (ModuleCat.{u} S)).functor.obj A ⋙
        ShortComplex.homologyFunctor (ModuleCat.{u} S) ≅ A.homology :=
  NatIso.ofComponents
    (fun n => A.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} S)).obj n)) (by
      intro n m f
      change ShortComplex.homologyMap (A.mapNatTrans ((evaluation ℕ (ModuleCat.{u} S)).map f)) ≫
          (A.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} S)).obj m)).hom =
        (A.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} S)).obj n)).hom ≫ A.homology.map f
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp)

/-- Exact filtered colimits commute with this actual short-complex homology.
The filtered-colimit exactness comes from ModuleCat's AB5 instance. -/
noncomputable def filteredColimitShortComplexHomologyIso
    (A : ShortComplex (ℕ ⥤ ModuleCat.{u} S)) :
    colimit A.homology ≅ (A.map (colim : (ℕ ⥤ ModuleCat.{u} S) ⥤ ModuleCat.{u} S)).homology :=
  (A.mapHomologyIso (colim : (ℕ ⥤ ModuleCat.{u} S) ⥤ ModuleCat.{u} S)).symm

theorem filteredColimitShortComplexHomologyIso_ι
    (A : ShortComplex (ℕ ⥤ ModuleCat.{u} S)) (n : ℕ) :
    colimit.ι A.homology n ≫ (filteredColimitShortComplexHomologyIso S A).hom =
      (A.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} S)).obj n)).inv ≫
        ShortComplex.homologyMap (A.mapNatTrans (colim.ι n)) := by
  change (colim.ι n).app A.homology ≫ (A.mapHomologyIso colim).inv = _
  rw [NatTrans.app_homology (colim.ι n) A]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
noncomputable def complexDiagramEvaluationHomologyIso
    (D : ℕ ⥤ CochainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) :
    D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q ≅
      ((ShortComplex.functorEquivalence ℕ (ModuleCat.{u} S)).inverse.obj
        (D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q)).homology := by
  let P := D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q
  change P ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} S) ≅ _
  exact Functor.isoWhiskerRight
      ((ShortComplex.functorEquivalence ℕ (ModuleCat.{u} S)).counitIso.app P).symm
      (ShortComplex.homologyFunctor (ModuleCat.{u} S)) ≪≫
    shortComplexEvaluationHomologyIso S _

set_option backward.isDefEq.respectTransparency false in
/-- The short complex of pointwise colimits is the short complex of the
explicit pointwise-colimit cochain complex, with the same differentials. -/
noncomputable def pointwiseColimitShortComplexIso
    (D : ℕ ⥤ CochainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) :
    (((ShortComplex.functorEquivalence ℕ (ModuleCat.{u} S)).inverse.obj
      (D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q)).map
        (colim : (ℕ ⥤ ModuleCat.{u} S) ⥤ ModuleCat.{u} S)) ≅
      ((HomologicalComplex.coconeOfHasColimitEval D).pt).sc q :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl) (by simp; rfl)

/-- Exact filtered colimits commute with actual cochain homology. This
construction uses AB5 and the canonical termwise-colimit complex. -/
noncomputable def filteredColimitHomologyIso
    (D : ℕ ⥤ CochainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) :
    colimit (D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q) ≅
      (colimit D).homology q :=
  HasColimit.isoOfNatIso (complexDiagramEvaluationHomologyIso S D q) ≪≫
    filteredColimitShortComplexHomologyIso S _ ≪≫
    (ShortComplex.homologyFunctor (ModuleCat.{u} S)).mapIso (pointwiseColimitShortComplexIso S D q) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q).mapIso
      (IsColimit.coconePointUniqueUpToIso
        (HomologicalComplex.isColimitCoconeOfHasColimitEval D) (colimit.isColimit D))

end LPCA


