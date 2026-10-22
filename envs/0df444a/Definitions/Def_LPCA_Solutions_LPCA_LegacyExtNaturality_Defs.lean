-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
-- name    : LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:50:35.511864+00:00
-- url     : https://prove2.me/theorems/2dd01c52-c50a-4c79-974f-226f35fc2830
-- title:
--   Legacy Ext-stage naturality under coordinate-power transitions
-- statement:
--   This bundle supplies legacy Ext-stage naturality under coordinate-power transitions. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual contravariant Hom-complex map induced by the resolution lift.
--   - The existing legacy Ext-stage isomorphisms commute with the actual quotient-induced Ext transitions and the explicit lifted Hom-complex maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LegacyExtNaturality.lean, selected declarations in lines 12–88; source SHA-256 59aa82d8e95284fd4b3b6db800e5ff0e79c91314cd3b033fec9abd453e36a63d; source certificate Sapelo2 job 49172236.

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

namespace LPCA

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

universe u

set_option backward.isDefEq.respectTransparency false in
theorem homologyUnop_hom_naturality
    {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex Cᵒᵖ c} (φ : K ⟶ L) (q : ι) :
    homologyMap ((unopFunctor C c).map φ.op) q ≫ (K.homologyUnop q).hom =
      (L.homologyUnop q).hom ≫ (homologyMap φ q).unop := by
  have h := congrArg Quiver.Hom.unop
    (HomologicalComplex.homologyOp_hom_naturality ((unopFunctor C c).map φ.op) q)
  simp only [unop_comp, Quiver.Hom.unop_op] at h
  change (L.unop.homologyOp q).hom.unop ≫ (homologyMap φ q).unop =
    homologyMap ((unopFunctor C c).map φ.op) q ≫ (K.unop.homologyOp q).hom.unop at h
  exact h.symm

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- The actual contravariant Hom-complex map induced by the resolution lift. -/
noncomputable def coordinateKoszulYonedaTransition
    (rank : V ↪ ℕ) (n m : ℕ) (hnm : n ≤ m) (T : Finset V)
    (M : ModuleCat.{u} (MvPolynomial V k)) :
    (coordinateKoszulComplex k rank n T).linearYonedaObj (MvPolynomial V k) M ⟶
      (coordinateKoszulComplex k rank m T).linearYonedaObj (MvPolynomial V k) M := by
  let F := ((linearYoneda (MvPolynomial V k) (ModuleCat.{u} (MvPolynomial V k))).obj M).rightOp
  exact (unopFunctor (ModuleCat.{u} (MvPolynomial V k)) (ComplexShape.down ℕ)).map
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (coordinateKoszulTransitionMap k rank n m hnm T)).op)

set_option backward.isDefEq.respectTransparency false in
/-- The existing legacy Ext-stage isomorphisms commute with the actual
quotient-induced Ext transitions and the explicit lifted Hom-complex maps. -/
theorem coordinateKoszulExtIso_naturality
    (rank : V ↪ ℕ) (n m : ℕ) (hnm : n ≤ m) (T : Finset V) (q : ℕ)
    (M : ModuleCat.{u} (MvPolynomial V k)) :
    ((Ext (MvPolynomial V k) (ModuleCat.{u} (MvPolynomial V k)) q).map
        (ModuleCat.ofHom (coordinatePowerQuotientMap k n m hnm T)).op).app M ≫
          (coordinateKoszulExtIso k rank m T q M).hom =
      (coordinateKoszulExtIso k rank n T q M).hom ≫
        homologyMap (coordinateKoszulYonedaTransition k rank n m hnm T M) q := by
  let F := ((linearYoneda (MvPolynomial V k) (ModuleCat.{u} (MvPolynomial V k))).obj M).rightOp
  let f := ModuleCat.ofHom (coordinatePowerQuotientMap k n m hnm T)
  let φ := coordinateKoszulTransitionMap k rank n m hnm T
  have hcomm : φ.f 0 ≫ (coordinateKoszulResolution k rank n T).π.f 0 =
      (coordinateKoszulResolution k rank m T).π.f 0 ≫ f := by
    dsimp only [φ, coordinateKoszulTransitionMap, coordinateKoszulResolution, f]
    rw [coordinateKoszulAugmentationMap_zero, coordinateKoszulAugmentationMap_zero]
    apply ModuleCat.hom_ext
    exact coordinateKoszulTransition_augmentation k n m hnm T
  have h := congrArg Quiver.Hom.unop
    (ProjectiveResolution.isoLeftDerivedObj_inv_naturality f
      (coordinateKoszulResolution k rank m T) (coordinateKoszulResolution k rank n T)
        φ hcomm F q)
  have hu := homologyUnop_hom_naturality
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) q
  simp only [coordinateKoszulExtIso, ProjectiveResolution.isoExt, Iso.trans_hom,
    Iso.symm_hom, Iso.unop_inv]
  have h' : ((F.leftDerived q).map f).unop ≫
      ((coordinateKoszulResolution k rank m T).isoLeftDerivedObj F q).inv.unop =
        ((coordinateKoszulResolution k rank n T).isoLeftDerivedObj F q).inv.unop ≫
          (homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) q).unop := by
    simpa only [unop_comp, Functor.comp_map, HomologicalComplex.homologyFunctor] using h
  change ((F.leftDerived q).map f).unop ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc, h']
  simp only [Category.assoc]
  apply congrArg (fun g =>
    ((coordinateKoszulResolution k rank n T).isoLeftDerivedObj F q).inv.unop ≫ g)
  change (homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) q).unop ≫
      (homologyUnop ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (coordinateKoszulComplex k rank m T)) q).inv =
    (homologyUnop ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (coordinateKoszulComplex k rank n T)) q).inv ≫
        homologyMap ((unopFunctor (ModuleCat.{u} (MvPolynomial V k)) (ComplexShape.down ℕ)).map
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ).op) q
  apply (cancel_epi (homologyUnop ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (coordinateKoszulComplex k rank n T)) q).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using
    congrArg (fun g => g ≫ (homologyUnop ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (coordinateKoszulComplex k rank m T)) q).inv) hu.symm

end LPCA


