-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
-- name    : LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T22:02:24.595448+00:00
-- url     : https://prove2.me/theorems/d1f2cf8e-5221-47d4-bfb9-0853b876f8c0
-- title:
--   Original Ext-colimit local cohomology and the actual Čech complex
-- statement:
--   This bundle supplies original Ext-colimit local cohomology and the actual Čech complex. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - A stage of the actual Koszul Hom diagram maps to the actual Cech complex by f_F -> f_F/x_F^(n+1), compatibly with the full differential.
--   - The Cech cocone is a colimit in the category of actual ambient-linear cochain complexes, by its termwise localization universal properties.
--   - The paper's unchanged Ext-colimit local cohomology is computed by the actual ungraded Cech complex, as a module over the ambient polynomial ring. Full integer grading is a separate compatibility theorem.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LocalCohomologyCechComparison.lean, selected declarations in lines 16–97; source SHA-256 157e449219ad796931389eb50f23189e0b02dd70cf45e4542a79f1f763629da6; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
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

theorem ambientCechComplex_d (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (p : ℕ) :
    (ambientCechComplex k rank K T).d p (p + 1) =
      ModuleCat.ofHom (ambientCechDifferential k rank K T p) :=
  CochainComplex.of_d
    (fun q => ModuleCat.of (MvPolynomial V k) (AmbientCechTerm k K T q))
    (fun q => ModuleCat.ofHom (ambientCechDifferential k rank K T q)) p

/-- A stage of the actual Koszul Hom diagram maps to the actual Cech
complex by f_F -> f_F/x_F^(n+1), compatibly with the full differential. -/
noncomputable def homLocalizationStage (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (n : ℕ) :
    (coordinateKoszulYonedaDiagram k rank T
      (ModuleCat.of (MvPolynomial V k) (FaceRing k K))).obj n ⟶
        ambientCechComplex k rank K T where
  f p := (homLocalizationTermCocone k rank K T p).ι.app n
  comm' := by
    intro p q hpq
    change p + 1 = q at hpq
    subst q
    change (homLocalizationTermCocone k rank K T p).ι.app n ≫
        (ambientCechComplex k rank K T).d p (p + 1) =
      ((coordinateKoszulComplex k rank n T).linearYonedaObj (MvPolynomial V k)
        (ModuleCat.of (MvPolynomial V k) (FaceRing k K))).d p (p + 1) ≫
          (homLocalizationTermCocone k rank K T (p + 1)).ι.app n
    rw [ambientCechComplex_d, ChainComplex.linearYonedaObj_d, coordinateKoszulComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change ambientCechDifferential k rank K T p
        (fun F => ambientFaceRingStage k K F.1 n
          (coordinateKoszulHomCoordinates k T p
            (ModuleCat.of (MvPolynomial V k) (FaceRing k K)) f F)) =
      fun G => ambientFaceRingStage k K G.1 n
        (coordinateKoszulHomCoordinates k T (p + 1)
          (ModuleCat.of (MvPolynomial V k) (FaceRing k K))
            (ModuleCat.ofHom (coordinateKoszulDifferential k rank n T p) ≫ f) G)
    rw [coordinateKoszulHomCoordinates_differential]
    exact ambientCechDifferential_stage k rank K T p n _

noncomputable def homLocalizationCocone (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) :
    Cocone (coordinateKoszulYonedaDiagram k rank T
      (ModuleCat.of (MvPolynomial V k) (FaceRing k K))) where
  pt := ambientCechComplex k rank K T
  ι := {
    app n := homLocalizationStage k rank K T n
    naturality n m f := by
      apply HomologicalComplex.Hom.ext
      funext p
      exact (homLocalizationTermCocone k rank K T p).w f }

/-- The Cech cocone is a colimit in the category of actual ambient-linear
cochain complexes, by its termwise localization universal properties. -/
noncomputable def homLocalizationIsColimit (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) : IsColimit (homLocalizationCocone k rank K T) :=
  HomologicalComplex.isColimitOfEval _ _
    (fun p => homLocalizationTermIsColimit k rank K T p)

noncomputable def koszulHomColimitCechIso (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) :
    colimit (coordinateKoszulYonedaDiagram k rank T
      (ModuleCat.of (MvPolynomial V k) (FaceRing k K))) ≅
        ambientCechComplex k rank K T :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (homLocalizationIsColimit k rank K T)

theorem koszulHomColimitCechIso_ι (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (n : ℕ) :
    colimit.ι (coordinateKoszulYonedaDiagram k rank T
        (ModuleCat.of (MvPolynomial V k) (FaceRing k K))) n ≫
      (koszulHomColimitCechIso k rank K T).hom = homLocalizationStage k rank K T n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n

/-- The paper's unchanged Ext-colimit local cohomology is computed by
the actual ungraded Cech complex, as a module over the ambient polynomial
ring. Full integer grading is a separate compatibility theorem. -/
noncomputable def supportCohomologyCechIso (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (q : ℕ) :
    supportCohomology k K T q ≅ (ambientCechComplex k rank K T).homology q :=
  supportCohomologyKoszulColimitIso k rank K T q ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} (MvPolynomial V k))
      (ComplexShape.up ℕ) q).mapIso (koszulHomColimitCechIso k rank K T)

end LPCA


