-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_Tradeoff
-- name    : QEC_Coding_ExpanderCodes_Tradeoff
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:35:05.631232+00:00
-- url     : https://prove2.me/theorems/d03b6d3f-a1e2-4997-a427-5eacae90d546
-- title:
--   Tradeoff
-- statement:
--   Definitions and structural lemmas for Tradeoff, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/Tradeoff.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
abbrev InitialC0 (q n m w : Nat) :=
  LiftedProduct.C0Index (Fin m) Unit (Cyclic.CyclicGroup q)
abbrev InitialQubit (q n m w : Nat) :=
  LiftedProduct.QubitIndex (Fin m) (Fin (w * n)) Unit Unit
    (Cyclic.CyclicGroup q)
abbrev InitialC2 (q n m w : Nat) :=
  LiftedProduct.C2Index (Fin (w * n)) Unit (Cyclic.CyclicGroup q)
abbrev FactorBit (r nc w : Nat) :=
  Fin (w * nc) × Cyclic.CyclicGroup r
abbrev FactorRawCheck (r mc : Nat) :=
  Fin mc × Cyclic.CyclicGroup r
abbrev FactorCheck
    (r nc mc w : Nat) [NeZero r]
    (C : Matrix (Fin mc) (Fin (w * nc))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r))) :=
  ClassicalRowReduction.ReducedCheck (PKDistance.tannerAction C)
noncomputable def tradeoffComplex
    (q n m r nc mc w : Nat) [NeZero q] [NeZero r]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (C : Matrix (Fin mc) (Fin (w * nc))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r))) :=
  twiceBalancedComplex
    (LiftedProduct.chainComplex (Cyclic.data q A))
    (ClassicalRowReduction.reducedBoundary (PKDistance.tannerAction C))
    (ClassicalRowReduction.reducedBoundary (PKDistance.tannerAction C))
def TradeoffMember
    (q n m r nc mc w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat)
    [NeZero q] [NeZero r]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (C : Matrix (Fin mc) (Fin (w * nc))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r))) : Prop :=
  let X := LiftedProduct.chainComplex (Cyclic.data q A)
  let Y := ClassicalRowReduction.reducedBoundary (PKDistance.tannerAction C)
  let sourceK := w * n - m
  let classicalK :=
    Fintype.card (FactorBit r nc w) - Fintype.card (FactorRawCheck r mc)
  let sourceD := certifiedDistanceLowerBound q w radiusDenominator
    expansionNumerator expansionDenominator
  let classicalD := classicalDistanceLowerBound
    (Fintype.card (FactorBit r nc w))
    radiusNumerator radiusDenominator
  let Q := tradeoffComplex q n m r nc mc w A C
  ((Q.binaryCSSCode).stabilizer.IsSourceValidBinary) ∧
    Fintype.card
      (SecondQubit
          (xZero := InitialC0 q n m w)
          (xOne := InitialQubit q n m w)
          (xTwo := InitialC2 q n m w)
          (bitOne := FactorBit r nc w)
          (checkOne := FactorCheck r nc mc w C)
          (bitTwo := FactorBit r nc w)
          (checkTwo := FactorCheck r nc mc w C)) =
      (Fintype.card (InitialQubit q n m w) *
          Fintype.card (FactorBit r nc w) +
        Fintype.card (InitialC2 q n m w) *
          Fintype.card (FactorCheck r nc mc w C)) *
          Fintype.card (FactorBit r nc w) +
      (Fintype.card (InitialC0 q n m w) *
          Fintype.card (FactorBit r nc w) +
        Fintype.card (InitialQubit q n m w) *
          Fintype.card (FactorCheck r nc mc w C)) *
          Fintype.card (FactorCheck r nc mc w C) ∧
    sourceK * classicalK * classicalK ≤
      Module.finrank (ZMod 2) Q.middleHomology ∧
    MiddleHomologyDistanceAtLeast Q (classicalD * sourceD) ∧
    MiddleCohomologyDistanceAtLeast Q (classicalD * sourceD) ∧
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence Q).localityProfile (3 * w + 2)
noncomputable def balancingExponent (alpha : ℝ) : ℝ :=
  alpha / (2 * (1 - alpha))
noncomputable def balancingLift (alpha : ℝ) (q : Nat) : Nat :=
  max 2 (Nat.ceil ((q : ℝ) ^ balancingExponent alpha))
def TwoProductConstructionFamily : Prop :=
  ∃ (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat),
    4 ≤ w ∧
    0 < gamma ∧
    0 < radiusNumerator ∧
    0 < radiusDenominator ∧
    0 < expansionNumerator ∧
    0 < expansionDenominator ∧
    ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 → ∀ B : Nat,
      ∃ (q n m r nc mc : Nat) (_hq : NeZero q) (_hr : NeZero r)
        (A : Matrix (Fin m) (Fin (w * n))
          (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
        (C : Matrix (Fin mc) (Fin (w * nc))
          (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup r))),
        B < q ∧
        r = balancingLift alpha q ∧
        (q : ℝ) ^ balancingExponent alpha ≤ r ∧
        gamma * Nat.log 2 r ≤ nc ∧
        nc ≤ gamma * (Nat.log 2 r + 1) ∧
        TradeoffMember q n m r nc mc w gamma radiusNumerator
          radiusDenominator expansionNumerator expansionDenominator A C ∧
        Fintype.card
            (SecondQubit
              (xZero := InitialC0 q n m w)
              (xOne := InitialQubit q n m w)
              (xTwo := InitialC2 q n m w)
              (bitOne := FactorBit r nc w)
              (checkOne := FactorCheck r nc mc w C)
              (bitTwo := FactorBit r nc w)
              (checkTwo := FactorCheck r nc mc w C)) ≤
          4 * blockLength q A * Fintype.card (FactorBit r nc w) ^ 2
end QEC.Coding.ExpanderCodes.PK20


