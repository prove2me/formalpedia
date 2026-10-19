-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardRationalNormKernelEquivalencesOriginalData20261018
-- name    : MazurTransfer_Order13ActualPicardRationalNormKernelEquivalencesOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T18:42:06.687701+00:00
-- url     : https://prove2.me/theorems/8dbb6c7b-0e8e-4213-ad18-6b1b8b8a56e3
-- title:
--   Original rational-to-arithmetic Picard norm-kernel equivalences
-- statement:
--   For every two-affine-open cover of the actual X₁(13) curve over the rationals, the original arithmetic class equivalence identifies each of the two rational represented-Picard norm kernels with the corresponding arithmetic divisor-class norm kernel. Both complete original constructor types and both entire nonproof values are checked, together with the original group-object provider type and value. Named downstream consumers are rational norm-kernel finiteness and cardinality transport.
-- source:
--   MazurTheorem Order13ActualPicardRationalNormKernelCardinality.rationalPiKernelEquiv and rationalPiConjugateKernelEquiv; original official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_KernelEquivalenceFromArithmeticClassTransportOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalNormComparisonOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardRationalNormComparison_rationalClass_schemePi
import Theorems.Thm_MazurTransfer_Order13ActualPicardRationalNormComparison_rationalClass_schemePiConjugate
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: transport the two rational kernels of the same represented Picard norm maps to the corresponding arithmetic divisor-class kernels through the original class equivalence. Named downstream consumers: actual_rational_norm_kernels_finite, actual_rational_norm_kernel_card_product and actual_rational_norm_kernel_card_dichotomy.
-/
noncomputable section
namespace MazurTransfer.Order13ActualPicardRationalNormKernelCardinality
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardRationalNormComparison
open scoped CategoryTheory.MonObj
local instance rationalKernelEquivOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
variable (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

def rationalPiKernelEquiv : rationalPi.ker ≃ Order13ActualDiamondPicardEndomorphisms.pi.ker :=
  KernelEquivalenceFromArithmeticClassTransport.kernelEquiv (rationalClassEquiv 𝒱)
    rationalPi Order13ActualDiamondPicardEndomorphisms.pi (rationalClass_schemePi 𝒱)

def rationalPiConjugateKernelEquiv :
    rationalPiConjugate.ker ≃ Order13ActualDiamondPicardEndomorphisms.piConjugate.ker :=
  KernelEquivalenceFromArithmeticClassTransport.kernelEquiv (rationalClassEquiv 𝒱)
    rationalPiConjugate Order13ActualDiamondPicardEndomorphisms.piConjugate
    (rationalClass_schemePiConjugate 𝒱)

end MazurTransfer.Order13ActualPicardRationalNormKernelCardinality
#print axioms MazurTransfer.Order13ActualPicardRationalNormKernelCardinality.rationalKernelEquivOriginalGroupProvider20261018
#print axioms MazurTransfer.Order13ActualPicardRationalNormKernelCardinality.rationalPiKernelEquiv
#print axioms MazurTransfer.Order13ActualPicardRationalNormKernelCardinality.rationalPiConjugateKernelEquiv


