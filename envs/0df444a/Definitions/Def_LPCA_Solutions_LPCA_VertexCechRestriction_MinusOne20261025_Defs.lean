-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_VertexCechRestriction_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:35:37.116807+00:00
-- url     : https://prove2.me/theorems/40a95f15-700f-4525-a8d9-e87c2049e86b
-- title:
--   Vertex Cech Restriction — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for vertex cech restriction, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_VertexCechRestriction.lean, selected declarations in lines 25–150; source SHA-256 86bcca95515609044a740436526bcf5e1e801132a4b2600de586e9dfe87971c6; exact-source certificate Sapelo2 job 49311470.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
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
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
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
import Mathlib.Tactic.Ring
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_redRestrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_dLin_idxCongr_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_restrictLin_dLin_Defs
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
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientFieldScalars_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableMaps_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCoordinates_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterActualComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCohomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterIncidence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterLinkTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterNonfaceVanishing_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterSigns_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyGrading_Defs
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
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_MinusOne20261025_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule

attribute [local instance 3000] _root_.LPCA.vertexRestrictionTermAddCommMonoid


theorem zeroDegreeActualTermEquiv_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (i : V)
    (T : Finset V) (a : V → ℤ) (p : ℕ) (hT : i ∉ T) (ha : a i = 0)
    (y : (localizedCechComplex k rank L T a).X p) :
    zeroDegreeActualTermEquiv k K i T a p hT ha
        (localizedCechTermRestriction k rank h T a p y) =
      localizedCechTermRestriction k rank (deletion_faces_mono h i) T a p
        (zeroDegreeActualTermEquiv k L i T a p hT ha y) := by
  apply (actualTermEquivModel k (deletion K i) T a p).injective
  rw [actualTermEquivModel_restriction k rank (deletion_faces_mono h i)]
  simp only [zeroDegreeActualTermEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [actualTermEquivModel_restriction k rank h]
  rfl

theorem positiveDegreeActualTermEquiv_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (i : V)
    (T : Finset V) (a : V → ℤ) (p : ℕ) (hT : i ∉ T) (ha : 0 < a i)
    (y : (localizedCechComplex k rank L T a).X p) :
    positiveDegreeActualTermEquiv k K i T a p hT ha
        (localizedCechTermRestriction k rank h T a p y) =
      localizedCechTermRestriction k rank (link_faces_mono h {i})
        T (Function.update a i 0) p
        (positiveDegreeActualTermEquiv k L i T a p hT ha y) := by
  apply (actualTermEquivModel k (link K {i}) T (Function.update a i 0) p).injective
  rw [actualTermEquivModel_restriction k rank (link_faces_mono h {i})]
  simp only [positiveDegreeActualTermEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [actualTermEquivModel_restriction k rank h]
  rfl

@[reassoc] theorem zeroDegreeCechComplexIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (i : V)
    (T : Finset V) (a : V → ℤ) (hT : i ∉ T) (ha : a i = 0) :
    localizedCechRestriction k rank h T a ≫ (zeroDegreeCechComplexIso k rank K i T a hT ha).hom =
      (zeroDegreeCechComplexIso k rank L i T a hT ha).hom ≫
        localizedCechRestriction k rank (deletion_faces_mono h i) T a := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact zeroDegreeActualTermEquiv_restriction k rank h i T a p hT ha y

@[reassoc] theorem positiveDegreeCechComplexIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (i : V)
    (T : Finset V) (a : V → ℤ) (hT : i ∉ T) (ha : 0 < a i) :
    localizedCechRestriction k rank h T a ≫ (positiveDegreeCechComplexIso k rank K i T a hT ha).hom =
      (positiveDegreeCechComplexIso k rank L i T a hT ha).hom ≫
        localizedCechRestriction k rank (link_faces_mono h {i}) T (Function.update a i 0) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact positiveDegreeActualTermEquiv_restriction k rank h i T a p hT ha y



@[reassoc] theorem zeroDegreeComplementCechComplexIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (i : V) (a : V → ℤ) (ha : a i = 0) :
    localizedCechRestriction k rank h (vertexSupport i) a ≫
        (zeroDegreeComplementCechComplexIso k rank K i a ha).hom =
      (zeroDegreeComplementCechComplexIso k rank L i a ha).hom ≫
        localizedCechRestriction k ((complementEmbedding i).trans rank)
          (restrictComplex_faces_mono (deletion_faces_mono h i) (complementEmbedding i))
          Finset.univ (a ∘ complementEmbedding i) := by
  dsimp only [zeroDegreeComplementCechComplexIso, vertexSupport, Iso.trans_hom]
  simp only [Category.assoc]
  rw [zeroDegreeCechComplexIso_restriction_assoc, restrictionCechComplexIso_restriction]

@[reassoc] theorem positiveDegreeComplementCechComplexIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (i : V) (a : V → ℤ) (ha : 0 < a i) :
    localizedCechRestriction k rank h (vertexSupport i) a ≫
        (positiveDegreeComplementCechComplexIso k rank K i a ha).hom =
      (positiveDegreeComplementCechComplexIso k rank L i a ha).hom ≫
        localizedCechRestriction k ((complementEmbedding i).trans rank)
          (restrictComplex_faces_mono (link_faces_mono h {i}) (complementEmbedding i))
          Finset.univ (a ∘ complementEmbedding i) := by
  dsimp only [positiveDegreeComplementCechComplexIso, vertexSupport, Iso.trans_hom]
  simp only [Category.assoc]
  rw [positiveDegreeCechComplexIso_restriction_assoc,
    restrictionCechComplexIso_restriction_assoc]
  rw [localizedCechRestriction_degree_cast k ((complementEmbedding i).trans rank)
    (restrictComplex_faces_mono (link_faces_mono h {i}) (complementEmbedding i))
    Finset.univ (update_restrict_complement i a)]

@[reassoc] theorem zeroDegreeComplementCechCohomologyIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (i : V)
    (a : V → ℤ) (q : ℕ) (ha : a i = 0) :
    localizedCechCohomologyRestriction k rank h (vertexSupport i) a q ≫
        (zeroDegreeComplementCechCohomologyIso k rank K i a q ha).hom =
      (zeroDegreeComplementCechCohomologyIso k rank L i a q ha).hom ≫
        localizedCechCohomologyRestriction k ((complementEmbedding i).trans rank)
          (restrictComplex_faces_mono (deletion_faces_mono h i) (complementEmbedding i))
          Finset.univ (a ∘ complementEmbedding i) q := by
  change HomologicalComplex.homologyMap (localizedCechRestriction k rank h (vertexSupport i) a) q ≫
      HomologicalComplex.homologyMap (zeroDegreeComplementCechComplexIso k rank K i a ha).hom q =
    HomologicalComplex.homologyMap (zeroDegreeComplementCechComplexIso k rank L i a ha).hom q ≫ _
  rw [← HomologicalComplex.homologyMap_comp,
    zeroDegreeComplementCechComplexIso_restriction, HomologicalComplex.homologyMap_comp]
  rfl

@[reassoc] theorem positiveDegreeComplementCechCohomologyIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (i : V)
    (a : V → ℤ) (q : ℕ) (ha : 0 < a i) :
    localizedCechCohomologyRestriction k rank h (vertexSupport i) a q ≫
        (positiveDegreeComplementCechCohomologyIso k rank K i a q ha).hom =
      (positiveDegreeComplementCechCohomologyIso k rank L i a q ha).hom ≫
        localizedCechCohomologyRestriction k ((complementEmbedding i).trans rank)
          (restrictComplex_faces_mono (link_faces_mono h {i}) (complementEmbedding i))
          Finset.univ (a ∘ complementEmbedding i) q := by
  change HomologicalComplex.homologyMap (localizedCechRestriction k rank h (vertexSupport i) a) q ≫
      HomologicalComplex.homologyMap (positiveDegreeComplementCechComplexIso k rank K i a ha).hom q =
    HomologicalComplex.homologyMap (positiveDegreeComplementCechComplexIso k rank L i a ha).hom q ≫ _
  rw [← HomologicalComplex.homologyMap_comp,
    positiveDegreeComplementCechComplexIso_restriction, HomologicalComplex.homologyMap_comp]
  rfl

end LPCA


