-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:35:20.428804+00:00
-- url     : https://prove2.me/theorems/ce82a12b-b317-4c76-87ec-d166ed767afa
-- title:
--   Explicit Garcia Stichtenoth Tower
-- statement:
--   Definitions and structural lemmas for Explicit Garcia Stichtenoth Tower, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ExplicitGarciaStichtenothTower.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceGaloisWFieldGenerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedPlaces_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGeneratorPoleDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivRatFunc_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityFibreDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroFibreDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepReciprocalRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_regularQuadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceGaloisWFieldGenerator
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGeneratorPoleDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldEquivRatFunc_X
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityFibreDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroFibreDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepDistinguishedCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepReciprocalRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_coe
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter FunctionFieldDifferential
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
abbrev f256GarciaStichtenothField (i : ℕ) : Type := SourceGaloisClosureField (i + 2)
scoped instance f256GarciaStichtenothBaseAlgebra (i : ℕ) :
    Algebra GaloisBaseField (f256GarciaStichtenothField i) := sourceGaloisClosureFieldAlgebra (i + 2)
scoped instance f256GarciaStichtenothConstantAlgebra (i : ℕ) :
    Algebra F256 (f256GarciaStichtenothField i) := sourceGaloisClosureConstantAlgebra (i + 2)
scoped instance f256GarciaStichtenothRatFuncAlgebra (i : ℕ) :
    Algebra (RatFunc F256) (f256GarciaStichtenothField i) := sourceGaloisClosureRatFuncAlgebra (i + 2)
scoped instance f256GarciaStichtenothPolynomialAlgebra (i : ℕ) :
    Algebra (Polynomial F256) (f256GarciaStichtenothField i) := sourceClosurePolynomialAlgebra (i + 2)
scoped instance f256GarciaStichtenothRatFuncTower (i : ℕ) :
    IsScalarTower F256 (RatFunc F256) (f256GarciaStichtenothField i) :=
  sourceGaloisClosureRatFuncScalarTower (i + 2)
scoped instance f256GarciaStichtenothPolynomialTower (i : ℕ) :
    IsScalarTower (Polynomial F256) (RatFunc F256) (f256GarciaStichtenothField i) :=
  sourceClosurePolynomialTower (i + 2)
scoped instance f256GarciaStichtenothFunctionField (i : ℕ) :
    _root_.FunctionField F256 (f256GarciaStichtenothField i) := sourceGaloisClosureFunctionField (i + 2)
scoped instance f256GarciaStichtenothSeparable (i : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (f256GarciaStichtenothField i) :=
  (sourceGaloisClosureRatFuncIsGalois (i + 2)).to_isSeparable
scoped instance f256GarciaStichtenothFullConstants (i : ℕ) :
    IsFullConstantField F256 (f256GarciaStichtenothField i) := sourceClosureFullConstants (i + 2)
scoped instance f256GarciaStichtenothDirectFullConstants (i : ℕ) :
    @IsFullConstantField F256 (f256GarciaStichtenothField i) _ _
      (@AffinePlace.constantAlgebra F256 (f256GarciaStichtenothField i) _ _
        (f256GarciaStichtenothPolynomialAlgebra i)) := sourceClosureDirectFullConstants (i + 2)
def f256GarciaStichtenothSeedEmbedding (i : ℕ) :
    SourceField (i + 2) →ₐ[GaloisBaseField] f256GarciaStichtenothField i :=
  sourceGaloisSeedToClosure (i + 2)
def f256GarciaStichtenothLength (i : ℕ) : ℕ := sourceGaloisClosureSelectedLength (i + 2)
def f256GarciaStichtenothSelectedRationalPlace (i : ℕ)
    (j : Fin (f256GarciaStichtenothLength i)) : RationalPlace F256 (f256GarciaStichtenothField i) :=
  sourceGaloisClosureSelectedRationalPlace (i + 2) j
def f256GarciaStichtenothSelectedPlace (i : ℕ) (j : Fin (f256GarciaStichtenothLength i)) :
    GlobalPlace F256 (f256GarciaStichtenothField i) :=
  (f256GarciaStichtenothSelectedRationalPlace i j).place
def f256GarciaStichtenothSelectedPlaces (i : ℕ) :
    Finset (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  sourceGaloisClosureSelectedPlaces (i + 2)
theorem f256GarciaStichtenothSelectedPlace_injective (i : ℕ) :
    Function.Injective (f256GarciaStichtenothSelectedPlace i) := by
  classical
  have hcard : (Finset.univ.image (f256GarciaStichtenothSelectedPlace i)).card =
      (Finset.univ : Finset (Fin (f256GarciaStichtenothLength i))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact sourceGaloisClosureSelectedPlaces_card (i + 2)
  exact fun a b h => Finset.card_image_iff.mp hcard (Finset.mem_univ a) (Finset.mem_univ b) h
theorem f256GarciaStichtenothSelectedPlaces_coe (i : ℕ) :
    (f256GarciaStichtenothSelectedPlaces i : Set (GlobalPlace F256 (f256GarciaStichtenothField i))) =
      Set.range (f256GarciaStichtenothSelectedPlace i) := by
  classical
  change (sourceGaloisClosureSelectedPlaces (i + 2) :
      Set (GlobalPlace F256 (SourceGaloisClosureField (i + 2)))) =
    Set.range (fun j : Fin (sourceGaloisClosureSelectedLength (i + 2)) =>
      (sourceGaloisClosureSelectedRationalPlace (i + 2) j).place)
  simp only [sourceGaloisClosureSelectedPlaces, Finset.coe_image, Finset.coe_univ, Set.image_univ]
def f256GarciaStichtenothSelectedPlaceEquiv (i : ℕ) :
    Fin (f256GarciaStichtenothLength i) ≃ ↑(f256GarciaStichtenothSelectedPlaces i) :=
  (Equiv.ofInjective (f256GarciaStichtenothSelectedPlace i)
    (f256GarciaStichtenothSelectedPlace_injective i)).trans
      (Equiv.setCongr (f256GarciaStichtenothSelectedPlaces_coe i).symm)
def f256GarciaStichtenothDivisorA (i : ℕ) : Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  sourceGaloisWZeroFibreDivisor (i + 2)
def f256GarciaStichtenothDivisorB (i : ℕ) : Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  sourceGaloisWInfinityFibreDivisor (i + 2)
def f256GarciaStichtenothDivisorD (i : ℕ) : Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  sourceGaloisClosureSelectedDivisor (i + 2)
def f256GarciaStichtenothAlpha (i : ℕ) : ℕ := sourceGaloisWZeroRamificationIndex (i + 2)
def f256GarciaStichtenothBeta (i : ℕ) : ℕ := sourceGaloisWInfinityRamificationIndex (i + 2)
def f256GarciaStichtenothCanonicalDifferential (i : ℕ) : Differential F256 (f256GarciaStichtenothField i) :=
  sourceClosureCanonicalDifferential (i + 2)
def f256GarciaStichtenothCanonicalDifferentialAtPlace (i : ℕ)
    (P : GlobalPlace F256 (f256GarciaStichtenothField i)) : Differential.simplePoleDifferentialLattice P :=
  sourceClosureCanonicalDifferentialAtPlace (i + 2) P
def f256GarciaStichtenothCanonicalDivisor (i : ℕ) : Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  sourceClosureCanonicalDivisor (i + 2)
def f256GarciaStichtenothGenus (i : ℕ) : ℕ := sourceClosureGenus (i + 2)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


