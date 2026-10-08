-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerDerivedData
-- name    : MazurTransfer_Order49Recurrence5DenseIntegerDerivedData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T11:06:00.053211+00:00
-- url     : https://prove2.me/theorems/e5c9c61a-1245-4511-8bec-953fd4ec2331
-- title:
--   Fifth resultant recurrence: exact dense integer data part
-- statement:
--   A bounded part of the fixed integer coefficient lists for the fifth order-seven resultant recurrence. This package contains mathematical coefficient data only. Polynomial interpretations and convolution identities are separately proved; the data assume no identity and no torsion conclusion.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0. Exact integer representations are extracted from actual typed definition expressions and checked by closed kernel polynomial interpretation proofs. The input lists reuse the two actual published exact data packages. Four intermediate lists now use the original total integer-list operations, each independently kernel compared with its original literal list. All other complete declaration bodies are byte preserved at Lean-owned AST ranges. The earlier combined and intermediate literal data jobs hit the platform token scanner timeout and are retained. Named downstream consumers: unchanged scalarResidual5Coefficient0 and scalarResidual5Coefficient1, recurrence5 and full every-curve order49 exclusion.

/- Total integer-list expressions for the fifth recurrence. Apache-2.0.
These expressions are separately kernel compared with the explicit fixed lists. -/
import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
namespace MazurTransfer.Order49Recurrence5DenseCandidate
def leadingSquare : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul b2 b2
def a3Square : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul a3 a3
def quotientConstant : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.add (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul b2 a2) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale (-1) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul b1 a3))
def exceptionalProductNumerator : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul a3Square exceptionalNumerator
end MazurTransfer.Order49Recurrence5DenseCandidate


