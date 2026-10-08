-- Prove2me | Definitions.Def_MazurTransfer_Order49Recurrence4ReusedDenseIntegerDataWithExtraTables
-- name    : MazurTransfer_Order49Recurrence4ReusedDenseIntegerDataWithExtraTables
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T12:01:22.076402+00:00
-- url     : https://prove2.me/theorems/ca06095e-f927-4bc2-9a8d-222dfe6ace75
-- title:
--   Fourth recurrence: reuse of exact verified dense integer inputs
-- statement:
--   Pure coefficient data for the original fourth resultant recurrence. The dividend aliases the existing third-recurrence divisor tables, the divisor aliases its remainder tables, and the new remainder aliases the existing fifth-recurrence divisor tables. The exceptional polynomial has a fixed denominator-cleared integer representation. No identity or torsion conclusion is assumed.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0. Reuses exact previously published dense data at the same Mathlib pin. The exceptional integer coefficients are candidates extracted from typed polynomial expressions; a separate ordinary kernel polynomial proof establishes their interpretation. Named downstream consumers: all three unchanged original scalarResidual4Coefficient identities, original recurrence4 and full every-curve order49 exclusion.

/- Apache-2.0. Exact integer representation for unchanged recurrence4 scalar consumers. -/
import Definitions.Def_MazurTransfer_Order49Recurrence3ExtraIntegerTables
import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
namespace MazurTransfer.Order49Recurrence4DenseCandidate
def a0 : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.b0
def a1 : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.b1
def a2 : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.b2
def a3 : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.b3
def a4 : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.b4
def b0 : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c0
def b1 : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c1
def b2 : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c2
def b3 : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c3
def c0 : List ℤ := MazurTransfer.Order49Recurrence5DenseCandidate.b0
def c1 : List ℤ := MazurTransfer.Order49Recurrence5DenseCandidate.b1
def c2 : List ℤ := MazurTransfer.Order49Recurrence5DenseCandidate.b2
def denominator : ℤ := 23215239933528791584969
def exceptionalNumerator : List ℤ := [
  -1,
  -19,
  -98,
  94,
  1355,
  -1375,
  -7054,
  18910,
  -19802,
  10514,
  -2928,
  436,
  -33,
  1
]
def leadingSquare : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul b3 b3
def a4Square : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul a4 a4
def quotientConstant : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.add (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul b3 a3) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale (-1) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul b2 a4))
def exceptionalProductNumerator : List ℤ := MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul a4Square exceptionalNumerator
end MazurTransfer.Order49Recurrence4DenseCandidate


