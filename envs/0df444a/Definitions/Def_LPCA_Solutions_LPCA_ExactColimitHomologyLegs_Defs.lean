-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
-- name    : LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:20:55.922721+00:00
-- url     : https://prove2.me/theorems/0a04f7d5-f842-4745-a5ea-3a5673f2c2b0
-- title:
--   Cocone legs of the exact-colimit homology comparison
-- statement:
--   Under the explicit exact-colimit hypothesis for the module diagram shape, these identities describe the actual cocone legs of the homology comparison. They retain the given stage maps rather than choosing new inclusions.
--
--   The included constructions and necessary compatibility results are:
--
--   - The exact-colimit homology comparison retains the canonical cocone leg of every actual complex. This fixes its compatibility with degree inclusions.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_ExactColimitHomologyLegs.lean, selected declarations in lines 16–76; source SHA-256 a081a6dc9f73091aa7a8f1e52283969b5bdcfda722f33662307f62112caf71e7; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable (S : Type u) [Ring S]
variable {J : Type u} [SmallCategory J]
variable [HasExactColimitsOfShape J (ModuleCat.{u} S)]

@[reassoc] theorem exactColimitShortComplexHomologyIso_ι
    (A : ShortComplex (J ⥤ ModuleCat.{u} S)) (j : J) :
    colimit.ι A.homology j ≫ (exactColimitShortComplexHomologyIso S A).hom =
      (A.mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj j)).inv ≫
        ShortComplex.homologyMap (A.mapNatTrans (colim.ι j)) := by
  change (colim.ι j).app A.homology ≫ (A.mapHomologyIso colim).inv = _
  rw [NatTrans.app_homology (colim.ι j) A]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem exactColimitStageShortComplex
    (D : J ⥤ CochainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) (j : J) :
    ((ShortComplex.functorEquivalence J (ModuleCat.{u} S)).counitIso.app
        (D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q)).inv.app j ≫
      (((ShortComplex.functorEquivalence J (ModuleCat.{u} S)).inverse.obj
        (D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q)).mapNatTrans
          (colim.ι j)) ≫
      (exactPointwiseColimitShortComplexIso S D q).hom =
        (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q).map
          ((HomologicalComplex.coconeOfHasColimitEval D).ι.app j) := by
  ext <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The exact-colimit homology comparison retains the canonical cocone leg
of every actual complex. This fixes its compatibility with degree inclusions. -/
@[reassoc] theorem exactColimitHomologyIso_ι
    (D : J ⥤ CochainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) (j : J) :
    colimit.ι (D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q) j ≫
        (exactColimitHomologyIso S D q).hom =
      HomologicalComplex.homologyMap (colimit.ι D j) q := by
  let P := D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q
  let A := (ShortComplex.functorEquivalence J (ModuleCat.{u} S)).inverse.obj P
  let gamma := ((ShortComplex.functorEquivalence J (ModuleCat.{u} S)).counitIso.app P).inv.app j
  let alpha := IsColimit.coconePointUniqueUpToIso
    (HomologicalComplex.isColimitCoconeOfHasColimitEval D) (colimit.isColimit D)
  have he : (exactComplexDiagramEvaluationHomologyIso S D q).hom.app j =
      ShortComplex.homologyMap gamma ≫
        (A.mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj j)).hom := rfl
  simp only [exactColimitHomologyIso, Iso.trans_hom, Category.assoc]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc, exactColimitShortComplexHomologyIso_ι_assoc, he]
  change ShortComplex.homologyMap gamma ≫
      (A.mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj j)).hom ≫
      (A.mapHomologyIso ((evaluation J (ModuleCat.{u} S)).obj j)).inv ≫
      ShortComplex.homologyMap (A.mapNatTrans (colim.ι j)) ≫
      ShortComplex.homologyMap (exactPointwiseColimitShortComplexIso S D q).hom ≫
      HomologicalComplex.homologyMap alpha.hom q = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [← Category.assoc]
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  have hs : (gamma ≫ A.mapNatTrans (colim.ι j)) ≫
      (exactPointwiseColimitShortComplexIso S D q).hom =
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q).map
        ((HomologicalComplex.coconeOfHasColimitEval D).ι.app j) := by
    simpa only [Category.assoc] using exactColimitStageShortComplex S D q j
  rw [hs]
  change HomologicalComplex.homologyMap ((HomologicalComplex.coconeOfHasColimitEval D).ι.app j) q ≫
      HomologicalComplex.homologyMap alpha.hom q = _
  rw [← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun f => HomologicalComplex.homologyMap f q)
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (HomologicalComplex.isColimitCoconeOfHasColimitEval D) (colimit.isColimit D) j)

end LPCA


