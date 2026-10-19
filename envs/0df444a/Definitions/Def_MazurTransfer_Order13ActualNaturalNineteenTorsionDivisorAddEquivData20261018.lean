-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNaturalNineteenTorsionDivisorAddEquivData20261018
-- name    : MazurTransfer_Order13ActualNaturalNineteenTorsionDivisorAddEquivData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T11:13:40.004211+00:00
-- url     : https://prove2.me/theorems/524d1c72-41f1-4d7f-b452-6947485e28bd
-- title:
--   The original natural additive equivalence on actual nineteen-torsion
-- statement:
--   The original natural divisor-class map on actual Picard nineteen-torsion is an additive equivalence, formed directly from its publicly proved injectivity and surjectivity. This is the same original constructor and nonproof value, and is used to transport the actual divisorial Weil pairing and to identify finite torsion carriers.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionDivisorComparison.geometricNineteenTorsionDivisorAddEquiv, exact original constructor and value.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original additive equivalence induced by the
SAME natural nineteen-torsion divisor-class map, using its publicly
proved injectivity and surjectivity.
Named downstream consumer: actual divisorial Weil pairing transport
and finite arithmetic divisor-class nineteen-torsion.
-/
import Definitions.Def_MazurTransfer_Order13ActualGeometricNineteenTorsionNaturalDivisorMapOriginalFieldContextDataV320261018
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDivisorComparison_geometricTorsionClassHom_surjective
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDivisorComparison_geometricTorsionClassHom_injective
noncomputable section
namespace MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison
open AlgebraicCurve
open Order13ActualNormKernelProductCardinality
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
attribute [local instance] naturalDivisorMapOriginalFactProvider20261018 naturalDivisorMapOriginalAlgebraProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

def geometricNineteenTorsionDivisorAddEquiv :
    NineteenTorsion K ≃+ Pic0.torsion K (actualCurveFunctionField K) 19 :=
  AddEquiv.ofBijective (geometricTorsionClassHom K)
    ⟨geometricTorsionClassHom_injective K, geometricTorsionClassHom_surjective K⟩

end MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison
#print axioms MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison.geometricNineteenTorsionDivisorAddEquiv


