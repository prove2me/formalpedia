-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
-- name    : QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:39:59.626381+00:00
-- url     : https://prove2.me/theorems/7ecafac5-ce6d-4416-8a64-1ca39732a120
-- title:
--   Asymptotics
-- statement:
--   Definitions and structural lemmas for Asymptotics, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u
def degreeCoefficient : Nat := 10000000 * 40000000000
def blocklengthCoefficient : Nat :=
  2611456 * 16 * degreeCoefficient ^ 2
def distanceCoefficient : Nat :=
  100000 * 101 * (4 * degreeCoefficient) ^ 2
def blocklengthScaleAt (s : Nat) : Nat :=
  blocklengthCoefficient * s ^ 4 *
    RandomPartition.hho20FiberLength s ^ 10
def dimensionScaleAt (s : Nat) : Nat :=
  RandomPartition.hho20FiberLength s ^ 6
def distanceScaleAt (s : Nat) : Nat :=
  (RandomPartition.hho20FiberLength s ^ 2 / 2) *
    (RandomPartition.hho20FiberLength s ^ 4 /
      (distanceCoefficient * s ^ 4))
def dimensionTradeoffCoefficient : Nat := blocklengthCoefficient ^ 3
def distanceTradeoffCoefficient : Nat :=
  blocklengthCoefficient ^ 3 * (8 * distanceCoefficient) ^ 5
def initialBlocklengthAt (s : Nat) : Nat :=
  7 * RandomPartition.hho20BaseScale s *
    RandomPartition.hho20FiberLength s ^ 2
def initialDimensionAt (s : Nat) : Nat :=
  RandomPartition.hho20BaseScale s
def initialXDistanceScaleAt (s : Nat) : Nat :=
  RandomPartition.hho20FiberLength s ^ 2 /
    (100000 * RandomPartition.hho20DegreeScale s)
def initialZDistanceScaleAt (s : Nat) : Nat :=
  RandomPartition.hho20FiberLength s ^ 3 /
    (5000 * RandomPartition.hho20DegreeScale s)
def initialLocalityScaleAt (s : Nat) : Nat :=
  101 * RandomPartition.hho20DegreeScale s + 2
def initialXTradeoffCoefficient : Nat :=
  56 * (100000 * degreeCoefficient) ^ 2
def initialZTradeoffCoefficient : Nat :=
  14 ^ 3 * 16 * (5000 * degreeCoefficient) ^ 4
def InitialFamilyCertificate
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (s : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  let D₀ := RandomTwist.fiberBundleData baseSample twistSample
  let X₀ := chainComplex D₀
  let N₀ := Fintype.card
    (QubitIndex (Fin (3 * r)) (Fin (4 * r))
      (ZMod (ell * ell)) (ZMod (ell * ell)))
  let K₀ := Module.finrank (ZMod 2) X₀.middleHomology
  (binaryCSSCode D₀).stabilizer.IsSourceValidBinary ∧
    CohomologyDistanceAtLeast D₀ (initialXDistanceScaleAt s) ∧
    HomologyDistanceAtLeast D₀ (initialZDistanceScaleAt s) ∧
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X₀).localityProfile
      (initialLocalityScaleAt s) ∧
    N₀ = initialBlocklengthAt s ∧
    K₀ = initialDimensionAt s ∧
    N₀ ≤ 7 * K₀ ^ 2 ∧
    7 * K₀ ^ 2 ≤ 2 * N₀ ∧
    N₀ ≤ initialXTradeoffCoefficient * s ^ 4 *
      initialXDistanceScaleAt s ^ 2 ∧
    N₀ ^ 3 ≤ initialZTradeoffCoefficient * s ^ 8 *
      initialZDistanceScaleAt s ^ 4
def FinalCZeroIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) : Type :=
  DistanceBalancing.C0Index
    (LocalityMainCTwo baseSample twistSample)
    (LocalityMainQubit baseSample twistSample)
    (BalanceBit balanceSample) (BalanceCheck balanceSample)
def FinalQubitIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) : Type :=
  DistanceBalancing.QubitIndex
    (LocalityMainQubit baseSample twistSample)
    (LocalityMainCZero baseSample twistSample)
    (BalanceBit balanceSample) (BalanceCheck balanceSample)
def FinalCTwoIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) : Type :=
  DistanceBalancing.C2Index
    (LocalityMainCZero baseSample twistSample)
    (BalanceBit balanceSample)
noncomputable instance instFintypeFinalCZeroIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    Fintype (FinalCZeroIndex baseSample twistSample balanceSample) := by
  unfold FinalCZeroIndex
  infer_instance
noncomputable instance instFintypeFinalQubitIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    Fintype (FinalQubitIndex baseSample twistSample balanceSample) := by
  unfold FinalQubitIndex
  infer_instance
noncomputable instance instDecidableEqFinalQubitIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    DecidableEq (FinalQubitIndex baseSample twistSample balanceSample) :=
  Classical.decEq _
noncomputable instance instFintypeFinalCTwoIndex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    Fintype (FinalCTwoIndex baseSample twistSample balanceSample) := by
  unfold FinalCTwoIndex
  infer_instance
noncomputable def finalComplex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (FinalCZeroIndex
        baseSample twistSample balanceSample))
      (Word (ZMod 2) (FinalQubitIndex
        baseSample twistSample balanceSample))
      (Word (ZMod 2) (FinalCTwoIndex
        baseSample twistSample balanceSample)) :=
  balancedLocalityComplex baseSample twistSample balanceSample
end QEC.Coding.FiberBundle.HHO20DistanceBalancing


