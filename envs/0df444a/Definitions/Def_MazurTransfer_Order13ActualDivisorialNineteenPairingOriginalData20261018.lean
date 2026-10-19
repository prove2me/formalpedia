-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDivisorialNineteenPairingOriginalData20261018
-- name    : MazurTransfer_Order13ActualDivisorialNineteenPairingOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T11:21:57.536989+00:00
-- url     : https://prove2.me/theorems/a2f51edd-7253-408b-8699-bba3310855c1
-- title:
--   The original actual divisorial nineteen-pairing data
-- statement:
--   This constructor chooses the original divisorial Weil-pairing data at nineteen on the literal order-13 curve function field, over each original algebraically closed characteristic-zero field. It uses the actual transcendental x-coordinate and the original finite-generation theorem. Its complete original type and nonproof value are preserved. Perfection and character-map injectivity are subsequent theorem contracts.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenDivisorialPairing.actualDivisorialNineteenPairingData; official Anthropic FLT pairing existence at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses complete checked Anthropic FLT divisorial pairing existence at exact
pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the original divisorial nineteen-pairing data on the
actual order-13 function field. No perfection assertion is included.
Named downstream consumer: actual pairing character-map injectivity,
perfection, and natural transport to the actual Picard norm kernels.
-/
import Definitions.Def_MazurTransfer_Order13FieldHyperellipticFixedFieldData
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData
noncomputable section
namespace MazurTransfer.Order13ActualGeometricNineteenDivisorialPairing
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
local instance actualDivisorialPairingOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance actualDivisorialPairingOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

def actualDivisorialNineteenPairingData :
    DivisorialWeilPairingData K (actualCurveFunctionField K) 19 :=
  (Pic0.nonempty_divisorialWeilPairingData K (actualCurveFunctionField K)
    ⟨Order13PellActualOrdinaryChart.xImage K,
      Order13FieldOrdinaryPolynomialTranscendence.xImage_transcendental K,
      Order13FieldHyperellipticFixedField.curveField_finite K⟩ 19).some

end MazurTransfer.Order13ActualGeometricNineteenDivisorialPairing
#print axioms MazurTransfer.Order13ActualGeometricNineteenDivisorialPairing.actualDivisorialNineteenPairingData


