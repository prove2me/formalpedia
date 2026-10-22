-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
-- name    : LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:52:58.919964+00:00
-- url     : https://prove2.me/theorems/37c105e4-8a1a-4127-9f24-e80bea34a651
-- title:
--   Koszul Hom Diagram for localized persistent commutative algebra
-- statement:
--   This bundle supplies koszul Hom Diagram for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual resolutions form an inverse system with the explicit lifts.
--   - Apply the actual contravariant Hom construction to the inverse system.
--   - This is the actual legacy local-cohomology Ext diagram, evaluated at M and reindexed along the equivalence Nat -> Nat-op-op.
--   - Naturality upgrades the individual Ext computations to an actual isomorphism of diagrams, retaining all exponent transitions.
--   - The genuine legacy Ext diagram computes homology of the colimit of the actual Hom complexes; the Cech identification is still a further step.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_KoszulHomDiagram.lean, selected declarations in lines 16–106; source SHA-256 fec2d14791c655e78540124524003789845e05a6b90d3710380c6c56c6601b6f; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
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
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
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

namespace LPCA

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

theorem coordinateKoszulTransitionMap_self
    (rank : V ↪ ℕ) (n : ℕ) (T : Finset V) :
    coordinateKoszulTransitionMap k rank n n le_rfl T = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  exact coordinateKoszulTransition_self k n T p

theorem coordinateKoszulTransitionMap_comp
    (rank : V ↪ ℕ) (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) (T : Finset V) :
    coordinateKoszulTransitionMap k rank m l hml T ≫
        coordinateKoszulTransitionMap k rank n m hnm T =
      coordinateKoszulTransitionMap k rank n l (hnm.trans hml) T := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  exact coordinateKoszulTransition_comp k n m l hnm hml T p

/-- The actual resolutions form an inverse system with the explicit lifts. -/
noncomputable def coordinateKoszulResolutionDiagram (rank : V ↪ ℕ) (T : Finset V) :
    ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} (MvPolynomial V k)) ℕ where
  obj n := coordinateKoszulComplex k rank (unop n) T
  map f := coordinateKoszulTransitionMap k rank _ _ f.unop.down.down T
  map_id n := coordinateKoszulTransitionMap_self k rank (unop n) T
  map_comp f g := (coordinateKoszulTransitionMap_comp k rank _ _ _
    g.unop.down.down f.unop.down.down T).symm

/-- Apply the actual contravariant Hom construction to the inverse system. -/
noncomputable def coordinateKoszulYonedaDiagram
    (rank : V ↪ ℕ) (T : Finset V) (M : ModuleCat.{u} (MvPolynomial V k)) :
    ℕ ⥤ CochainComplex (ModuleCat.{u} (MvPolynomial V k)) ℕ := by
  let F := ((linearYoneda (MvPolynomial V k) (ModuleCat.{u} (MvPolynomial V k))).obj M).rightOp
  exact (opOpEquivalence ℕ).inverse ⋙ (coordinateKoszulResolutionDiagram k rank T).op ⋙
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).op ⋙
      unopFunctor (ModuleCat.{u} (MvPolynomial V k)) (ComplexShape.down ℕ)



@[simp] theorem coordinateKoszulYonedaDiagram_map
    (rank : V ↪ ℕ) (T : Finset V) (M : ModuleCat.{u} (MvPolynomial V k))
    {n m : ℕ} (f : n ⟶ m) :
    (coordinateKoszulYonedaDiagram k rank T M).map f =
      coordinateKoszulYonedaTransition k rank n m f.down.down T M := rfl

theorem coordinatePowerQuotientMap_ringModIdeals
    {n m : ℕ} (f : n ⟶ m) (T : Finset V) :
    (localCohomology.ringModIdeals (coordinatePowersDiagram k T)).map f.op =
      ModuleCat.ofHom (coordinatePowerQuotientMap k n m f.down.down T) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- This is the actual legacy local-cohomology Ext diagram, evaluated at M
and reindexed along the equivalence Nat -> Nat-op-op. -/
noncomputable def coordinateKoszulExtDiagram
    (T : Finset V) (q : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) :
    ℕ ⥤ ModuleCat.{u} (MvPolynomial V k) :=
  (opOpEquivalence ℕ).inverse ⋙ localCohomology.diagram (coordinatePowersDiagram k T) q ⋙
    (evaluation (ModuleCat.{u} (MvPolynomial V k)) (ModuleCat.{u} (MvPolynomial V k))).obj M

set_option backward.isDefEq.respectTransparency false in
/-- Naturality upgrades the individual Ext computations to an actual
isomorphism of diagrams, retaining all exponent transitions. -/
noncomputable def coordinateKoszulExtDiagramIso
    (rank : V ↪ ℕ) (T : Finset V) (q : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) :
    coordinateKoszulExtDiagram k T q M ≅
      coordinateKoszulYonedaDiagram k rank T M ⋙
        homologyFunctor (ModuleCat.{u} (MvPolynomial V k)) (ComplexShape.up ℕ) q :=
  NatIso.ofComponents (fun n => coordinateKoszulExtIso k rank n T q M) (by
    intro n m f
    change ((Ext (MvPolynomial V k) (ModuleCat.{u} (MvPolynomial V k)) q).map
        ((localCohomology.ringModIdeals (coordinatePowersDiagram k T)).map f.op).op).app M ≫
          (coordinateKoszulExtIso k rank m T q M).hom = _
    erw [coordinatePowerQuotientMap_ringModIdeals k f T]
    simpa only [Functor.comp_map, HomologicalComplex.homologyFunctor,
      coordinateKoszulYonedaDiagram_map] using
        coordinateKoszulExtIso_naturality k rank n m f.down.down T q M)

/-- The genuine legacy Ext diagram computes homology of the colimit of
the actual Hom complexes; the Cech identification is still a further step. -/
noncomputable def coordinateKoszulExtColimitIso
    (rank : V ↪ ℕ) (T : Finset V) (q : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) :
    colimit (coordinateKoszulExtDiagram k T q M) ≅
      (colimit (coordinateKoszulYonedaDiagram k rank T M)).homology q :=
  HasColimit.isoOfNatIso (coordinateKoszulExtDiagramIso k rank T q M) ≪≫
    filteredColimitHomologyIso (MvPolynomial V k) (coordinateKoszulYonedaDiagram k rank T M) q

end LPCA


