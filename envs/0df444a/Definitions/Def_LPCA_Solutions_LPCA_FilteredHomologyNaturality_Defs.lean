-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
-- name    : LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:21:49.417643+00:00
-- url     : https://prove2.me/theorems/dfcd0e6e-78ff-4dde-a712-502e02da65ab
-- title:
--   Stage maps and naturality of the sequential homology comparison
-- statement:
--   These declarations identify each actual cocone leg of the sequential module-colimit homology comparison and prove compatibility with maps of the cochain-complex diagrams. The diagrams are indexed by natural numbers; their transitions need not be injective.
--
--   The included constructions and necessary compatibility results are:
--
--   - The original filtered-colimit comparison retains each actual stage map on homology. This specifies its compatibility with module maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_FilteredHomologyNaturality.lean, selected declarations in lines 15–90; source SHA-256 888a2848ce5078dd064df0aad7017ebf5470af7ff6b1601a080f4b8dd20aa4f7; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Limits
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

variable (S : Type u) [Ring S]

@[reassoc] theorem filteredColimitShortHomology_stage
    (A : ShortComplex (ℕ ⥤ ModuleCat.{u} S)) (n : ℕ) :
    colimit.ι A.homology n ≫ (filteredColimitShortComplexHomologyIso S A).hom =
      (A.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} S)).obj n)).inv ≫
        ShortComplex.homologyMap (A.mapNatTrans (colim.ι n)) :=
  filteredColimitShortComplexHomologyIso_ι S A n

theorem filteredColimitStageShortComplex
    (D : ℕ ⥤ CochainComplex (ModuleCat.{u} S) ℕ) (q n : ℕ) :
    ((ShortComplex.functorEquivalence ℕ (ModuleCat.{u} S)).counitIso.app
        (D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q)).inv.app n ≫
      (((ShortComplex.functorEquivalence ℕ (ModuleCat.{u} S)).inverse.obj
        (D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q)).mapNatTrans
          (colim.ι n)) ≫
      (pointwiseColimitShortComplexIso S D q).hom =
        (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q).map
          ((HomologicalComplex.coconeOfHasColimitEval D).ι.app n) := by
  ext <;> rfl

/-- The original filtered-colimit comparison retains each actual stage
map on homology. This specifies its compatibility with module maps. -/
@[reassoc] theorem filteredColimitHomologyIso_ι
    (D : ℕ ⥤ CochainComplex (ModuleCat.{u} S) ℕ) (q n : ℕ) :
    colimit.ι (D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q) n ≫
        (filteredColimitHomologyIso S D q).hom =
      HomologicalComplex.homologyMap (colimit.ι D n) q := by
  let P := D ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q
  let A := (ShortComplex.functorEquivalence ℕ (ModuleCat.{u} S)).inverse.obj P
  let gamma := ((ShortComplex.functorEquivalence ℕ (ModuleCat.{u} S)).counitIso.app P).inv.app n
  let alpha := IsColimit.coconePointUniqueUpToIso
    (HomologicalComplex.isColimitCoconeOfHasColimitEval D) (colimit.isColimit D)
  have he : (complexDiagramEvaluationHomologyIso S D q).hom.app n =
      ShortComplex.homologyMap gamma ≫
        (A.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} S)).obj n)).hom := rfl
  simp only [filteredColimitHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc, filteredColimitShortHomology_stage_assoc, he]
  change ShortComplex.homologyMap gamma ≫
      (A.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} S)).obj n)).hom ≫
      (A.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} S)).obj n)).inv ≫
      ShortComplex.homologyMap (A.mapNatTrans (colim.ι n)) ≫
      ShortComplex.homologyMap (pointwiseColimitShortComplexIso S D q).hom ≫
      HomologicalComplex.homologyMap alpha.hom q = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [← Category.assoc]
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  have hs : (gamma ≫ A.mapNatTrans (colim.ι n)) ≫
      (pointwiseColimitShortComplexIso S D q).hom =
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q).map
        ((HomologicalComplex.coconeOfHasColimitEval D).ι.app n) := by
    simpa only [Category.assoc] using filteredColimitStageShortComplex S D q n
  rw [hs]
  change HomologicalComplex.homologyMap ((HomologicalComplex.coconeOfHasColimitEval D).ι.app n) q ≫
      HomologicalComplex.homologyMap alpha.hom q = _
  rw [← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun f => HomologicalComplex.homologyMap f q)
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (HomologicalComplex.isColimitCoconeOfHasColimitEval D) (colimit.isColimit D) n)

@[reassoc] theorem filteredColimitHomologyIso_naturality
    {D E : ℕ ⥤ CochainComplex (ModuleCat.{u} S) ℕ} (f : D ⟶ E) (q : ℕ) :
    colim.map (whiskerRight f
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℕ) q)) ≫
        (filteredColimitHomologyIso S E q).hom =
      (filteredColimitHomologyIso S D q).hom ≫
        HomologicalComplex.homologyMap (colim.map f) q := by
  apply colimit.hom_ext
  intro n
  simp only [Category.assoc, colimit.ι_map_assoc,
    filteredColimitHomologyIso_ι_assoc, filteredColimitHomologyIso_ι]
  change HomologicalComplex.homologyMap (f.app n) q ≫
      HomologicalComplex.homologyMap (colimit.ι E n) q =
    HomologicalComplex.homologyMap (colimit.ι D n) q ≫
      HomologicalComplex.homologyMap (colim.map f) q
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun g => HomologicalComplex.homologyMap g q)
    (colimit.ι_map f n).symm

end LPCA


