-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
-- name    : QEC_Coding_ExpanderCodes_AlmostLinear
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:37:41.760251+00:00
-- url     : https://prove2.me/theorems/9df8369b-9962-4ebf-b9b5-8ecbebd64396
-- title:
--   Almost Linear
-- statement:
--   Definitions and structural lemmas for Almost Linear, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/AlmostLinear.lean

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
def PropositionOneExpandingMatrixFamily : Prop :=
  ∃ (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat),
    4 ≤ w ∧
    0 < gamma ∧
    0 < radiusNumerator ∧
    0 < radiusDenominator ∧
    0 < expansionNumerator ∧
    0 < expansionDenominator ∧
    ∀ (ell : Nat) [NeZero ell], 1 < ell →
      ∃ (n m : Nat)
        (A : Matrix (Fin m) (Fin (w * n))
          (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup ell))),
        m = 2 * (w / 4) * n ∧
        gamma * Nat.log 2 ell ≤ n ∧
        n ≤ gamma * (Nat.log 2 ell + 1) ∧
        (∀ i : Fin (w * n) × Cyclic.CyclicGroup ell,
          HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w) ∧
        (∀ i : Fin m × Cyclic.CyclicGroup ell,
          HammingWeight
            (PKDistance.tannerAction (LiftedProduct.starTranspose A)
              (Pi.single i 1)) ≤ w) ∧
        (PKDistance.tannerAction A).SmallSetExpandingAtRelativeRadius
          radiusNumerator radiusDenominator
          expansionNumerator expansionDenominator ∧
        (PKDistance.tannerAction
          (LiftedProduct.starTranspose A)).SmallSetExpandingAtRelativeRadius
            radiusNumerator radiusDenominator
            expansionNumerator expansionDenominator
def MiddleCohomologyDistanceAtMost
    {F i0 i1 i2 : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype i0] [Fintype i1] [Fintype i2]
    (K : ChainComplexData F (Word F i0) (Word F i1) (Word F i2))
    (d : Nat) : Prop :=
  ∃ z : Word F i1,
    z ∈ K.middleCocycleCode.carrier ∧
    z ∉ K.firstCoboundaryCheckCode.carrier ∧
    HammingWeight z ≤ d
def blockLength
    {aRow aCol : Type} [Fintype aRow] [Fintype aCol]
    (q : Nat) [NeZero q]
    (_A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) : Nat :=
  Fintype.card
    (LiftedProduct.QubitIndex aRow aCol Unit Unit (Cyclic.CyclicGroup q))
def certifiedDistanceLowerBound
    (q w radiusDenominator expansionNumerator expansionDenominator : Nat) : Nat :=
  let threshold := q / (2 * w * radiusDenominator)
  expansionNumerator * threshold /
    max (2 * expansionNumerator) (4 * expansionDenominator)
def FirstFamilyMember
    (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m : Nat)
    [NeZero q]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) : Prop :=
  let K := Module.finrank (ZMod 2)
    (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology
  let d := certifiedDistanceLowerBound q w radiusDenominator
    expansionNumerator expansionDenominator
  Odd q ∧
    m = 2 * (w / 4) * n ∧
    gamma * Nat.log 2 q ≤ n ∧
    n ≤ gamma * (Nat.log 2 q + 1) ∧
    blockLength q A = q * (w * n + m) ∧
    w * n - m ≤ K ∧
    K ≤ w * n + m ∧
    (LiftedProduct.binaryCSSCode (Cyclic.data q A)).stabilizer.IsSourceValidBinary ∧
    BoundedLocality
      (LiftedProduct.boundaryIncidence
        (Cyclic.data q A)).localityProfile (w + 2) ∧
    MiddleHomologyDistanceAtLeast
      (LiftedProduct.chainComplex (Cyclic.data q A)) d ∧
    MiddleCohomologyDistanceAtLeast
      (LiftedProduct.chainComplex (Cyclic.data q A)) d ∧
    MiddleCohomologyDistanceAtMost
      (LiftedProduct.chainComplex (Cyclic.data q A)) q ∧
    max (2 * expansionNumerator) (4 * expansionDenominator) * d ≤
      expansionNumerator * (q / (2 * w * radiusDenominator))
def FirstAlmostLinearFamily : Prop :=
  ∃ (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat),
    4 ≤ w ∧
    0 < gamma ∧
    0 < radiusNumerator ∧
    0 < radiusDenominator ∧
    0 < expansionNumerator ∧
    0 < expansionDenominator ∧
    ∀ B : Nat,
      ∃ (q n m : Nat) (_hq : NeZero q)
        (A : Matrix (Fin m) (Fin (w * n))
          (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))),
        B < q ∧
        FirstFamilyMember w gamma radiusNumerator radiusDenominator
          expansionNumerator expansionDenominator q n m A
def familyLift
    (w radiusDenominator B : Nat) : Nat :=
  2 * (B + 2 ^ radiusDenominator + 2 * w * radiusDenominator) + 1
end QEC.Coding.ExpanderCodes.PK20


