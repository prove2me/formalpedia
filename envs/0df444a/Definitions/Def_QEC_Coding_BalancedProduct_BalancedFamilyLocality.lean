-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
-- name    : QEC_Coding_BalancedProduct_BalancedFamilyLocality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:20:42.199214+00:00
-- url     : https://prove2.me/theorems/ae611e6b-690a-4219-8ce1-b22b25ba1c49
-- title:
--   Balanced Family Locality
-- statement:
--   Definitions and structural lemmas for Balanced Family Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
set_option autoImplicit false
namespace QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
def BalancedFamilyCertificate
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) : Prop :=
  let D := balancedSubsystem q hq40 hq
  let N := Fintype.card (BalancedQubitIndex q hq)
  let K := D.logicalQubits
  let dX := lpsDressedZLowerBound q hq
  let dZ := (Fintype.card (EdgeOrbit401 q hq) / 10000000) *
    lpsDressedXLowerBound q
  (D.complex.binaryCSSCode).stabilizer.IsSourceValidBinary ∧
    D.DressedXDistanceAtLeast dX ∧
    D.DressedZDistanceAtLeast dZ ∧
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence D.complex).localityProfile 806 ∧
    N = blocklengthCoefficient * q * (q ^ 2 - 1) ^ 2 ∧
    (q ^ 2 - 1) ^ 2 ≤ K ∧
    K ≤ (201 * (q ^ 2 - 1)) ^ 2 ∧
    N ^ 4 ≤ dimensionLowerCoefficient * K ^ 5 ∧
    K ^ 5 ≤ dimensionUpperCoefficient * N ^ 4 ∧
    N ^ 3 ≤ dressedXPowerCoefficient * dX ^ 5 ∧
    N ^ 3 ≤ dressedZPowerCoefficient * dZ ^ 5
end QEC.Coding.BalancedProduct.BE20Balanced


