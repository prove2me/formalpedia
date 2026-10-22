-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
-- name    : LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:56:24.374827+00:00
-- url     : https://prove2.me/theorems/0fa5fe71-cb26-46bf-8ac0-8c7ab02a7e2d
-- title:
--   Hom Localization Columns for localized persistent commutative algebra
-- statement:
--   This bundle supplies hom Localization Columns for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The genuine Hom term diagram is the finite product of the genuine localization telescopes. The component maps are values on the free Koszul basis, followed only by the identity scalar-restriction equivalence.
--   - This is the actual termwise colimit universal property; it does not assume that coordinate multiplication is injective.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_HomLocalizationColumns.lean, selected declarations in lines 17–76; source SHA-256 f7fe80aba502352ef5fa241e12244545857f9ab2965afa9e6dc20cfc2980affe; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
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
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

theorem polynomialFaceMonomial_image (K : Complex V) (F : Finset V) :
    Ideal.Quotient.mk (srIdeal k K) (polynomialFaceMonomial k F) =
      invertedMonomial k K F := by
  simp only [polynomialFaceMonomial, invertedMonomial, variableClass, map_prod]

theorem polynomialFaceMonomial_smul (K : Complex V) (F : Finset V)
    (a : ℕ) (r : FaceRing k K) :
    polynomialFaceMonomial k F ^ a • r = invertedMonomial k K F ^ a * r := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  change Ideal.Quotient.mk (srIdeal k K) (polynomialFaceMonomial k F ^ a * p) = _
  rw [map_mul, map_pow, polynomialFaceMonomial_image]

/-- The genuine Hom term diagram is the finite product of the genuine
localization telescopes. The component maps are values on the free Koszul
basis, followed only by the identity scalar-restriction equivalence. -/
noncomputable def homLocalizationColumnsIso
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (p : ℕ) :
    coordinateKoszulYonedaDiagram k rank T
        (ModuleCat.of (MvPolynomial V k) (FaceRing k K)) ⋙
      HomologicalComplex.eval (ModuleCat.{u} (MvPolynomial V k)) (ComplexShape.up ℕ) p ≅
        finitePiDiagram (fun F : CechSlot T p => ambientLocalizationTelescope k K F.1) := by
  classical
  refine NatIso.ofComponents (fun n =>
    ((coordinateKoszulHomCoordinates k T p
      (ModuleCat.of (MvPolynomial V k) (FaceRing k K))).trans
        (LinearEquiv.piCongrRight fun _ : CechSlot T p =>
          (restrictedFaceRingIso k K).symm.toLinearEquiv)).toModuleIso) ?_
  intro n m f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  funext F
  change coordinateKoszulHomCoordinates k T p
    (ModuleCat.of (MvPolynomial V k) (FaceRing k K))
      (ModuleCat.ofHom (coordinateKoszulTransition k n m T p) ≫ a) F =
    invertedMonomial k K F.1 ^ (m - n) *
      coordinateKoszulHomCoordinates k T p
        (ModuleCat.of (MvPolynomial V k) (FaceRing k K)) a F
  rw [coordinateKoszulHomCoordinates_transition, polynomialFaceMonomial_smul]

noncomputable def homLocalizationTermCocone
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (p : ℕ) :
    Cocone (coordinateKoszulYonedaDiagram k rank T
        (ModuleCat.of (MvPolynomial V k) (FaceRing k K)) ⋙
      HomologicalComplex.eval (ModuleCat.{u} (MvPolynomial V k)) (ComplexShape.up ℕ) p) := by
  classical
  exact (Cocone.precompose (homLocalizationColumnsIso k rank K T p).hom).obj
    (finitePiCocone (fun F : CechSlot T p => ambientLocalizationTelescopeCocone k K F.1))

/-- This is the actual termwise colimit universal property; it does not
assume that coordinate multiplication is injective. -/
noncomputable def homLocalizationTermIsColimit
    (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) (p : ℕ) :
    IsColimit (homLocalizationTermCocone k rank K T p) := by
  classical
  exact (IsColimit.precomposeHomEquiv (homLocalizationColumnsIso k rank K T p)
    (finitePiCocone (fun F : CechSlot T p =>
      ambientLocalizationTelescopeCocone k K F.1))).symm
    (finitePiCoconeIsColimit _ (fun F : CechSlot T p =>
      ambientLocalizationTelescopeIsColimit k K F.1))



end LPCA


