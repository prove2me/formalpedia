-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticClassDataExplicitPublicConstructors20261017
-- name    : MazurTransfer_Order13ActualPicardGeometricArithmeticClassDataExplicitPublicConstructors20261017
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T19:19:33.783946+00:00
-- url     : https://prove2.me/theorems/7d801a37-87e6-4fb1-bd7a-cfb2a06f2534
-- title:
--   The original geometric divisor and arithmetic class of a point of the same rational Picard family
-- statement:
--   Let K be a perfect characteristic-zero field, let a be a K-valued point of the existing rational represented Picard family, and choose a two-affine cover of the literal order-13 curve over K. Choose a full degree-zero divisor presentation of the actual line bundle associated to a. Its degree-zero divisor class is
--
--   $$\operatorname{cl}_K(a)=[D_a]\in\operatorname{Pic}^0(K(C_K)).$$
--
--   The complete original types and values of the chosen divisor and arithmetic-class constructors are preserved, as are the original scalar algebra providers. The named downstream consumers are presentation independence, injectivity, and transport of the diamond identities to the same Picard scheme.
-- source:
--   Original MazurTheorem Order13ActualPicardGeometricArithmeticClass.geometricPointDivisor and geometricArithmeticClass constructors, applied to the separately proved full original geometric degree-zero presentation. Official Anthropic FLT inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same existing rational represented Picard has an
intrinsic degree-zero divisor class at every perfect characteristic-zero
field point. The existing rational diamond transports this class by the
actual extension-field diamond. Named downstream consumer: promoting the
arithmetic diamond cyclotomic relation to a scheme morphism identity.
-/
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondPresentationData
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

noncomputable section
namespace MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGenericFieldAction
open Order13ActualPicardGeometricDiamondLineBundle Order13ActualPicardGeometricDiamondPresentation

open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase)

def geometricPointDivisor : Divisor.degZero (K := K) (F := actualCurveFunctionField K) :=
  (MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 a).choose

def geometricArithmeticClass : Pic0 K (actualCurveFunctionField K) :=
  Pic0.mk (geometricPointDivisor K 𝒱 a)


end MazurTransfer.Order13ActualPicardGeometricArithmeticClass
#print axioms MazurTransfer.Order13ActualPicardGeometricArithmeticClass.geometricPointDivisor
#print axioms MazurTransfer.Order13ActualPicardGeometricArithmeticClass.geometricArithmeticClass


