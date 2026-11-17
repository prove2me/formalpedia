-- Prove2me | Definitions.Def_N25_CanonicalModularDictionary
-- name    : N25_CanonicalModularDictionary
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:16:21.44705+00:00
-- url     : https://prove2.me/theorems/f62d6115-e66b-493d-8cde-2301d4110a01
-- title:
--   The coordinate-preserving canonical–modular function-field dictionary
-- statement:
--   The file identifies the canonical function field over $ℚ$ with the selected level-$25$ modular function field by sending the plane generators to $$u↦U_0,   v↦U_0/U_1.$$ It also transports all places through this constant-preserving field equivalence. This dictionary connects rational canonical points and their places to modular units and cusps.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Theorems.Thm_N25_U25_zero_transcendental
import Theorems.Thm_N25_unitPlaneToXH25_surjective
import Definitions.Def_N25_UnitPlaneModularMap
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitRelation25_qExpansion_certificate
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Definitions.Def_N25_Endgame
import Definitions.Def_N25
import Theorems.Thm_ModularForm_sturm_bound_of_isArithmetic
import Definitions.Def_N25_UnitPlaneFunctionCoordinates
import Definitions.Def_N25_UnitPlaneFieldPointLift
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Definitions.Def_N25_CanonicalFunctionCoordinates
/-! The coordinate-preserving dictionary between canonical and modular function fields. -/
noncomputable section
namespace N25

/-- The canonical function field is identified with the modular field through the fixed plane map. -/
def canonicalXHAlgEquiv25 : CanonicalFF25 ℚ ≃ₐ[ℚ] N25.Endgame.FQ :=
  let φ : UnitPlaneFF25 →ₐ[ℚ] N25.Endgame.FQ :=
    unitPlaneFieldPointLift25 (U25 0) (U25 0 / U25 1)
      (unitRelation25_qExpansion_certificate ℚ) U25_zero_transcendental
  canonicalUnitPlaneAlgEquiv25.symm.trans
    (AlgEquiv.ofBijective φ ⟨φ.injective, unitPlaneToXH25_surjective⟩)

/-- Places transport through the specified constant-preserving function-field identification. -/
def canonicalXHPlaceEquiv25 :
    AlgebraicCurve.Place ℚ (CanonicalFF25 ℚ) ≃ N25.Endgame.QPlace :=
  AlgebraicCurve.Place.congrEquiv canonicalXHAlgEquiv25.toRingEquiv
    (fun a => canonicalXHAlgEquiv25.commutes a)

end N25


