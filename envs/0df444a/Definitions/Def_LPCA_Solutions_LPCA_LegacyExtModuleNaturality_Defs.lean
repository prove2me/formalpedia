-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LegacyExtModuleNaturality_Defs
-- name    : LPCA_Solutions_LPCA_LegacyExtModuleNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:52:57.594533+00:00
-- url     : https://prove2.me/theorems/f6238c81-1b41-4474-b3c8-6455c0ec2c63
-- title:
--   Naturality of legacy Ext under coefficient-module maps
-- statement:
--   For a commutative ring S, postcomposition by a supplied S-linear coefficient-module map acts covariantly on the actual resolution Hom cochain complex. The existing projective-resolution computation of legacy Ext commutes with that map. These are stagewise naturality statements, not a separate direct-limit construction.
--
--   The included constructions and necessary compatibility results are:
--
--   - Postcomposition on the resolution Hom cochain complex, covariant in its coefficient-module argument. The differential and all projective-resolution terms are the ones already used by Mathlib's legacy Ext construction.
--   - Naturality of the genuine projective-resolution computation of legacy Ext in its module argument. This does not choose new structure maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LegacyExtModuleNaturality.lean, selected declarations in lines 15–64; source SHA-256 073ada61105d2b45e4542b2c0a42bded08e55148dc98093360f5f96e662bf6d6; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

universe u

variable (S : Type u) [CommRing S]

/-- Postcomposition on the actual contravariant Hom complex in its
module argument. The differential and all projective-resolution terms are
the ones already used by Mathlib's legacy Ext construction. -/
noncomputable def linearYonedaModuleMap (A : ChainComplex (ModuleCat.{u} S) ℕ)
    {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    A.linearYonedaObj S M ⟶ A.linearYonedaObj S N :=
  (unopFunctor (ModuleCat.{u} S) (ComplexShape.down ℕ)).map
    (((NatTrans.mapHomologicalComplex
      ((linearYoneda S (ModuleCat.{u} S)).map f).rightOp
      (ComplexShape.down ℕ)).app A).op)



/-- Naturality of the genuine projective-resolution computation of legacy
Ext in its module argument. This does not choose new structure maps. -/
theorem legacyIsoExt_module_naturality {X : ModuleCat.{u} S}
    (P : ProjectiveResolution X) {M N : ModuleCat.{u} S} (f : M ⟶ N) (q : ℕ) :
    ((Ext S (ModuleCat.{u} S) q).obj (op X)).map f ≫ (P.isoExt q N).hom =
      (P.isoExt q M).hom ≫ homologyMap (linearYonedaModuleMap S P.complex f) q := by
  let F := ((linearYoneda S (ModuleCat.{u} S)).obj M).rightOp
  let G := ((linearYoneda S (ModuleCat.{u} S)).obj N).rightOp
  let α : G ⟶ F := ((linearYoneda S (ModuleCat.{u} S)).map f).rightOp
  let φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex
  have hn : (P.isoLeftDerivedObj G q).inv ≫ (NatTrans.leftDerived α q).app X =
      homologyMap φ q ≫ (P.isoLeftDerivedObj F q).inv := by
    rw [ProjectiveResolution.leftDerived_app_eq α P q]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have h := congrArg Quiver.Hom.unop hn
  simp only [unop_comp] at h
  have hu := homologyUnop_hom_naturality φ q
  have hφ : (unopFunctor (ModuleCat.{u} S) (ComplexShape.down ℕ)).map φ.op =
      linearYonedaModuleMap S P.complex f := rfl
  rw [hφ] at hu
  simp only [ProjectiveResolution.isoExt, Iso.trans_hom, Iso.symm_hom, Iso.unop_inv]
  change ((NatTrans.leftDerived α q).app X).unop ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  apply congrArg (fun g => (P.isoLeftDerivedObj F q).inv.unop ≫ g)
  change (homologyMap φ q).unop ≫
      (homologyUnop ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) q).inv =
    (homologyUnop ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) q).inv ≫
      homologyMap (linearYonedaModuleMap S P.complex f) q
  apply (cancel_epi
    (homologyUnop ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) q).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using
    congrArg (fun g => g ≫
      (homologyUnop ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) q).inv) hu.symm

end LPCA


