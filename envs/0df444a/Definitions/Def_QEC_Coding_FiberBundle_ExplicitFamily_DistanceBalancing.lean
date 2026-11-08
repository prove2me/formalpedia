-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
-- name    : QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:34:48.829671+00:00
-- url     : https://prove2.me/theorems/971351c2-5595-4e6b-8bef-cd051c6083f7
-- title:
--   Distance Balancing
-- statement:
--   Definitions and structural lemmas for Distance Balancing, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancing.lean

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
abbrev MainRelation
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  baseSupportRelation
    (RandomTwist.fiberBundleData baseSample twistSample)
abbrev MainReducedCheck
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  ClassicalWeightReduction.WeightReducedCheck
    (MainRelation baseSample twistSample)
abbrev MainReducedBit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  ClassicalWeightReduction.WeightReducedBit
    (MainRelation baseSample twistSample)
abbrev MainCZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  C0Index (MainReducedCheck baseSample twistSample) (ZMod (ell * ell))
abbrev MainQubit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  QubitIndex
    (MainReducedCheck baseSample twistSample)
    (MainReducedBit baseSample twistSample)
    (ZMod (ell * ell)) (ZMod (ell * ell))
abbrev MainCTwo
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :=
  C2Index (MainReducedBit baseSample twistSample) (ZMod (ell * ell))
abbrev BalanceBit {r : Nat} (sample : RandomBase.Sample r) :=
  ClassicalWeightReduction.WeightReducedBit
    (RandomBase.incidenceRelation sample)
abbrev BalanceCheck {r : Nat} (sample : RandomBase.Sample r) :=
  ClassicalWeightReduction.WeightReducedCheck
    (RandomBase.incidenceRelation sample)
noncomputable instance instDecidableEqMainCZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (MainCZero baseSample twistSample) := Classical.decEq _
noncomputable instance instDecidableEqMainQubit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (MainQubit baseSample twistSample) := Classical.decEq _
noncomputable instance instDecidableEqMainCTwo
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (MainCTwo baseSample twistSample) := Classical.decEq _
noncomputable def mainComplex
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (MainCZero baseSample twistSample))
      (Word (ZMod 2) (MainQubit baseSample twistSample))
      (Word (ZMod 2) (MainCTwo baseSample twistSample)) :=
  chainComplex
    (weightReducedData
      (RandomTwist.fiberBundleData baseSample twistSample))
noncomputable def balancedData
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    DistanceBalancing.Data
      (MainCTwo baseSample twistSample)
      (MainQubit baseSample twistSample)
      (MainCZero baseSample twistSample)
      (BalanceBit balanceSample) (BalanceCheck balanceSample) :=
  by
    classical
    exact DistanceBalancing.Data.ofComplexes
      (dualChainComplex (mainComplex baseSample twistSample))
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (RandomBase.incidenceRelation balanceSample))
def mainReducedHomologyDistance (r ell Delta : Nat) : Nat :=
  ((ell * (4 * r)) / (5000 * Delta)) / (101 * Delta)
def mainReducedCohomologyDistance (r ell Delta : Nat) : Nat :=
  (min ((ell * ell) / 2) ((6 * r) / (100000 * Delta))) /
    (101 * Delta)
def balancedHomologyDistanceAt (s : Nat) : Nat :=
  ((4 * RandomPartition.hho20BaseScale s) / 5) *
    mainReducedCohomologyDistance
      (RandomPartition.hho20BaseScale (2 * s))
      (RandomPartition.hho20FiberLength (2 * s))
      (RandomPartition.hho20DegreeScale (2 * s))
def balancedCohomologyDistanceAt (s : Nat) : Nat :=
  mainReducedHomologyDistance
    (RandomPartition.hho20BaseScale (2 * s))
    (RandomPartition.hho20FiberLength (2 * s))
    (RandomPartition.hho20DegreeScale (2 * s))
def balancedBlocklengthUpperAt (s : Nat) : Nat :=
  2611456 * RandomPartition.hho20BaseScale (2 * s) *
    RandomPartition.hho20DegreeScale (2 * s) *
    (RandomPartition.hho20FiberLength (2 * s) *
      RandomPartition.hho20FiberLength (2 * s)) *
    RandomPartition.hho20BaseScale s *
    RandomPartition.hho20DegreeScale s
end QEC.Coding.FiberBundle.HHO20DistanceBalancing


