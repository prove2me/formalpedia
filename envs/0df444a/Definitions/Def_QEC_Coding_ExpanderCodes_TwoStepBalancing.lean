-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
-- name    : QEC_Coding_ExpanderCodes_TwoStepBalancing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:32:28.439789+00:00
-- url     : https://prove2.me/theorems/97f208ee-6318-4a88-a860-83396980b374
-- title:
--   Two Step Balancing
-- statement:
--   Definitions and structural lemmas for Two Step Balancing, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {xZero xOne xTwo bitOne checkOne bitTwo checkTwo : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype bitOne] [DecidableEq bitOne]
variable [Fintype checkOne] [DecidableEq checkOne]
variable [Fintype bitTwo] [DecidableEq bitTwo]
variable [Fintype checkTwo] [DecidableEq checkTwo]
noncomputable def firstBalancingData
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne) :=
  Data.ofComplexes X Y
abbrev FirstC0 (xZero xOne bitOne checkOne : Type u) :=
  C0Index xZero xOne bitOne checkOne
abbrev FirstQubit (xOne xTwo bitOne checkOne : Type u) :=
  QubitIndex xOne xTwo bitOne checkOne
abbrev FirstC2 (xTwo bitOne : Type u) := C2Index xTwo bitOne
noncomputable def firstBalancedComplex
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne) :=
  chainComplex (firstBalancingData X Y)
noncomputable def secondBalancingData
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo) :=
  Data.ofComplexes (dualChainComplex (firstBalancedComplex X Y₁)) Y₂
abbrev SecondC0
    (xOne xTwo bitOne checkOne bitTwo checkTwo : Type u) :=
  C0Index (FirstC2 xTwo bitOne)
    (FirstQubit xOne xTwo bitOne checkOne) bitTwo checkTwo
abbrev SecondQubit
    (xZero xOne xTwo bitOne checkOne bitTwo checkTwo : Type u) :=
  QubitIndex (FirstQubit xOne xTwo bitOne checkOne)
    (FirstC0 xZero xOne bitOne checkOne) bitTwo checkTwo
noncomputable instance secondQubitDecidableEq :
    DecidableEq
      (SecondQubit xZero xOne xTwo bitOne checkOne bitTwo checkTwo) :=
  Classical.decEq _
abbrev SecondC2
    (xZero xOne bitOne checkOne bitTwo : Type u) :=
  C2Index (FirstC0 xZero xOne bitOne checkOne) bitTwo
noncomputable def twiceBalancedComplex
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo) :=
  dualChainComplex (chainComplex (secondBalancingData X Y₁ Y₂))
def TwiceBalancedMemberCertificate
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo)
    (sourceDimension classicalDimensionOne classicalDimensionTwo
      sourceDistance classicalDistanceOne classicalDistanceTwo
      locality : Nat) : Prop :=
  ((twiceBalancedComplex X Y₁ Y₂).binaryCSSCode).stabilizer.IsSourceValidBinary ∧
    Fintype.card
        (SecondQubit xZero xOne xTwo bitOne checkOne bitTwo checkTwo) =
      (Fintype.card xOne * Fintype.card bitOne +
          Fintype.card xTwo * Fintype.card checkOne) *
        Fintype.card bitTwo +
      (Fintype.card xZero * Fintype.card bitOne +
          Fintype.card xOne * Fintype.card checkOne) *
        Fintype.card checkTwo ∧
    sourceDimension * classicalDimensionOne * classicalDimensionTwo ≤
      Module.finrank (ZMod 2) (twiceBalancedComplex X Y₁ Y₂).middleHomology ∧
    MiddleHomologyDistanceAtLeast (twiceBalancedComplex X Y₁ Y₂)
      (classicalDistanceOne * sourceDistance) ∧
    MiddleCohomologyDistanceAtLeast (twiceBalancedComplex X Y₁ Y₂)
      (classicalDistanceTwo * sourceDistance) ∧
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (twiceBalancedComplex X Y₁ Y₂)).localityProfile locality
end QEC.Coding.ExpanderCodes.PK20


