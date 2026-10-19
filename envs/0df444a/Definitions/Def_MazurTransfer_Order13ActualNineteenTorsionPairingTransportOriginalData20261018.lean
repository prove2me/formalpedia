-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionPairingTransportOriginalData20261018
-- name    : MazurTransfer_Order13ActualNineteenTorsionPairingTransportOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T11:32:20.781925+00:00
-- url     : https://prove2.me/theorems/9fa1edbb-33d1-4ece-b240-d82776ee727b
-- title:
--   Original transport of the actual nineteen-pairing to Picard torsion
-- statement:
--   This interface defines the original unit-valued pairing obtained by transporting supplied divisorial nineteen-pairing data through the same natural actual Picard torsion equivalence, and its specialization to the original actual divisorial pairing. Both complete original constructor types and nonproof values are preserved. Bilinearity, nondegeneracy and norm adjointness are subsequent proof contracts.
-- source:
--   MazurTheorem Order13ActualNineteenTorsionPairingTransport.pairingUnits and Order13ActualGeometricNineteenDivisorialPairing.actualGeometricNineteenPairing, exact original constructors and values.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original transfer of divisorial pairing values
through the SAME natural actual nineteen-torsion additive equivalence,
and its specialization to the original actual divisorial pairing.
Named downstream consumer: actual bilinearity, nondegeneracy and
norm-factor adjointness used for individual norm-kernel ranks.
-/
import Definitions.Def_MazurTransfer_Order13ActualNaturalNineteenTorsionDivisorAddEquivData20261018
import Definitions.Def_MazurTransfer_Order13ActualDivisorialNineteenPairingOriginalData20261018
noncomputable section
namespace MazurTransfer.Order13ActualNineteenTorsionPairingTransport
open AlgebraicCurve
open Order13ActualNormKernelProductCardinality Order13ActualGeometricNineteenTorsionDivisorComparison
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
local instance pairingTransportOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance pairingTransportOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (d : DivisorialWeilPairingData K (actualCurveFunctionField K) 19)

def pairingUnits (x y : NineteenTorsion K) : Kˣ :=
  Units.mk0 (d.pair (geometricNineteenTorsionDivisorAddEquiv K x)
    (geometricNineteenTorsionDivisorAddEquiv K y)) (d.pair_ne_zero _ _)

end MazurTransfer.Order13ActualNineteenTorsionPairingTransport
namespace MazurTransfer.Order13ActualGeometricNineteenDivisorialPairing
open Order13ActualNormKernelProductCardinality Order13ActualNineteenTorsionPairingTransport
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

def actualGeometricNineteenPairing (x y : NineteenTorsion K) : Kˣ :=
  pairingUnits K (actualDivisorialNineteenPairingData K) x y

end MazurTransfer.Order13ActualGeometricNineteenDivisorialPairing
#print axioms MazurTransfer.Order13ActualNineteenTorsionPairingTransport.pairingUnits
#print axioms MazurTransfer.Order13ActualGeometricNineteenDivisorialPairing.actualGeometricNineteenPairing


