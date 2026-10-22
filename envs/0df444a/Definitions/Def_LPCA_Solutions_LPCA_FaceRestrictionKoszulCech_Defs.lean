-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
-- name    : LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-22T00:17:23.844178+00:00
-- url     : https://prove2.me/theorems/29c1416f-c939-4660-bd1c-5a6b7bae222f
-- title:
--   Face Restriction Koszul Čech for localized persistent commutative algebra
-- statement:
--   This bundle supplies face Restriction Koszul Čech for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual fraction maps from every coordinate-power resolution commute with the genuine face-ring quotient maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_FaceRestrictionKoszulCech.lean, selected declarations in lines 17–65; source SHA-256 9e4dbbc66df3d1759312c4ea2dc918f946b3e495dbc5acaef27bc00993d9c966; source certificate Sapelo2 job 49172236.

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
import Mathlib.CategoryTheory.Category.Preorder
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
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
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
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

theorem localizedFaceRestriction_stage {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) (n : ℕ) (r : FaceRing k L) :
    localizedFaceRestriction k h F
        (localizationTelescopeStage (invertedMonomial k L F) n r) =
      localizationTelescopeStage (invertedMonomial k K F) n (faceRingRestriction k h r) := by
  rw [localizationTelescopeStage_eq, localizationTelescopeStage_eq]
  change IsLocalization.map (LocalizedFaceRing k K F)
      (faceRingRestriction k h).toRingHom (faceRingRestriction_powers k h F)
      (IsLocalization.mk' (M := Submonoid.powers (invertedMonomial k L F))
        (LocalizedFaceRing k L F) r
        ⟨invertedMonomial k L F ^ (n + 1), ⟨n + 1, rfl⟩⟩) = _
  rw [IsLocalization.map_mk']
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_pow, faceRingRestriction_inverted]

/-- The actual fraction maps from every coordinate-power resolution
commute with the genuine face-ring quotient maps. -/
@[reassoc] theorem homLocalizationStage_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (T : Finset V) (n : ℕ) :
    (coordinateKoszulYonedaModuleMap k rank T (faceRingModuleRestriction k h)).app n ≫
        homLocalizationStage k rank K T n =
      homLocalizationStage k rank L T n ≫ ambientCechRestriction k rank h T := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext F
  change localizationTelescopeStage (invertedMonomial k K F.1) n
      (coordinateKoszulHomCoordinates k T p
        (ModuleCat.of (MvPolynomial V k) (FaceRing k K))
          (f ≫ faceRingModuleRestriction k h) F) =
    localizedFaceRestriction k h F.1
      (localizationTelescopeStage (invertedMonomial k L F.1) n
        (coordinateKoszulHomCoordinates k T p
          (ModuleCat.of (MvPolynomial V k) (FaceRing k L)) f F))
  rw [localizedFaceRestriction_stage]
  rfl

@[reassoc] theorem koszulHomColimitCechIso_restriction (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (T : Finset V) :
    colim.map (coordinateKoszulYonedaModuleMap k rank T (faceRingModuleRestriction k h)) ≫
        (koszulHomColimitCechIso k rank K T).hom =
      (koszulHomColimitCechIso k rank L T).hom ≫ ambientCechRestriction k rank h T := by
  apply colimit.hom_ext
  intro n
  simp only [Category.assoc, colimit.ι_map_assoc,
    koszulHomColimitCechIso_ι, reassoc_of% koszulHomColimitCechIso_ι]
  exact homLocalizationStage_restriction k rank h T n

end LPCA


