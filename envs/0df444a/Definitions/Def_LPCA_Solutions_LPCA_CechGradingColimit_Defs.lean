-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
-- name    : LPCA_Solutions_LPCA_CechGradingColimit_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:12:23.400116+00:00
-- url     : https://prove2.me/theorems/9e3cd4cf-af1f-469b-a64a-3b399249c4e8
-- title:
--   Čech Grading Colimit for localized persistent commutative algebra
-- statement:
--   This bundle supplies čech Grading Colimit for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The full actual Cech complex is the coproduct of its existing homogeneous subcomplexes, with precisely the actual degree inclusions as cocone maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CechGradingColimit.lean, selected declarations in lines 19–76; source SHA-256 873bee0ce5b2d0b4c95a1ea1e9ec06670ba506ace7bf5bf34b577af4a4dc517d; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MonoidAlgebra.Basic
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
import Definitions.Def_LPCA_Solutions_LPCA_AmbientFieldScalars_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDegreeSeparation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs
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

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule

noncomputable local instance (priority := 3000) cechColimitTermAddCommMonoid
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ) :
    AddCommMonoid (LocalizedCechTerm k K T a p) :=
  (localizedTermAddCommGroup k K T a p).toAddCommMonoid

noncomputable def cechDegreeDiagram (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) :
    Discrete (V → ℤ) ⥤ CochainComplex (ModuleCat.{u} k) ℕ :=
  Discrete.functor (fun a => localizedCechComplex k rank K T a)

noncomputable def cechDegreeCocone (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) :
    Cocone (cechDegreeDiagram k rank K T) where
  pt := ambientCechFieldComplex k rank K T
  ι := Discrete.natTrans (fun a => localizedCechDegreeInclusion k rank K T a.as)

noncomputable def cechDegreeTermIso (K : Complex V) (T : Finset V) (p : ℕ) :
    ModuleCat.of k (DirectSum (V → ℤ) (fun a => LocalizedCechTerm k K T a p)) ≅
      (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).obj
        (ModuleCat.of (MvPolynomial V k) (AmbientCechTerm k K T p)) :=
  (cechTermSumEquiv k K T p).toModuleIso ≪≫ (ambientCechTermFieldIso k K T p).symm

noncomputable def cechDegreeTermIsColimit (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (p : ℕ) :
    IsColimit ((HomologicalComplex.eval (ModuleCat.{u} k) (ComplexShape.up ℕ) p).mapCocone
      (cechDegreeCocone k rank K T)) := by
  classical
  let A : (V → ℤ) → ModuleCat.{u} k := fun a => ModuleCat.of k (LocalizedCechTerm k K T a p)
  let e : cechDegreeDiagram k rank K T ⋙
      HomologicalComplex.eval (ModuleCat.{u} k) (ComplexShape.up ℕ) p ≅
        Discrete.functor A := Discrete.natIso (fun _ => Iso.refl _)
  let c := (Cocone.precompose e.hom).obj (moduleDirectSumCocone k A)
  have hc : IsColimit c := (IsColimit.precomposeHomEquiv e _).symm
    (moduleDirectSumIsColimit k A)
  apply IsColimit.ofIsoColimit hc
  refine Cocone.ext (cechDegreeTermIso k K T p) ?_
  intro a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change cechTermSumEquiv k K T p
    (DirectSum.lof k (V → ℤ) (fun b => LocalizedCechTerm k K T b p) a.as y) =
      fun F => (y F).1
  exact cechTermSumEquiv_lof k K T p a.as y

/-- The full actual Cech complex is the coproduct of its existing homogeneous
subcomplexes, with precisely the actual degree inclusions as cocone maps. -/
noncomputable def cechDegreeIsColimit (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) :
    IsColimit (cechDegreeCocone k rank K T) :=
  HomologicalComplex.isColimitOfEval _ _ (fun p => cechDegreeTermIsColimit k rank K T p)

noncomputable def cechDegreeColimitIso (rank : V ↪ ℕ) (K : Complex V) (T : Finset V) :
    colimit (cechDegreeDiagram k rank K T) ≅ ambientCechFieldComplex k rank K T :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (cechDegreeIsColimit k rank K T)

theorem cechDegreeColimitIso_ι (rank : V ↪ ℕ) (K : Complex V)
    (T : Finset V) (a : V → ℤ) :
    colimit.ι (cechDegreeDiagram k rank K T) ⟨a⟩ ≫
      (cechDegreeColimitIso k rank K T).hom = localizedCechDegreeInclusion k rank K T a :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk a)

end LPCA


