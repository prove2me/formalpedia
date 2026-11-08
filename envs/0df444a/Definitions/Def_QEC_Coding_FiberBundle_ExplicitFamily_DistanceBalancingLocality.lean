-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
-- name    : QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:36:20.255313+00:00
-- url     : https://prove2.me/theorems/eac86410-7aec-4916-a040-c3c0a724704c
-- title:
--   Distance Balancing Locality
-- statement:
--   Definitions and structural lemmas for Distance Balancing Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancingLocality.lean

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
def LocalityMainCZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Type :=
  MainCZero baseSample twistSample
def LocalityMainQubit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Type :=
  MainQubit baseSample twistSample
def LocalityMainCTwo
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Type :=
  MainCTwo baseSample twistSample
noncomputable instance instFintypeLocalityMainCZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Fintype (LocalityMainCZero baseSample twistSample) := by
  unfold LocalityMainCZero
  infer_instance
noncomputable instance instFintypeLocalityMainQubit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Fintype (LocalityMainQubit baseSample twistSample) := by
  unfold LocalityMainQubit
  infer_instance
noncomputable instance instFintypeLocalityMainCTwo
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Fintype (LocalityMainCTwo baseSample twistSample) := by
  unfold LocalityMainCTwo
  infer_instance
noncomputable instance instDecidableEqLocalityMainCZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (LocalityMainCZero baseSample twistSample) := Classical.decEq _
noncomputable instance instDecidableEqLocalityMainQubit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (LocalityMainQubit baseSample twistSample) := Classical.decEq _
noncomputable instance instDecidableEqLocalityMainCTwo
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (LocalityMainCTwo baseSample twistSample) := Classical.decEq _
noncomputable def mainLocalityComplex
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (LocalityMainCZero baseSample twistSample))
      (Word (ZMod 2) (LocalityMainQubit baseSample twistSample))
      (Word (ZMod 2) (LocalityMainCTwo baseSample twistSample)) :=
  mainComplex baseSample twistSample
noncomputable def balancedLocalityComplex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :=
  DistanceBalancing.chainComplex
    (DistanceBalancing.Data.ofComplexes
      (dualChainComplex (mainLocalityComplex baseSample twistSample))
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (RandomBase.incidenceRelation balanceSample)))
end QEC.Coding.FiberBundle.HHO20DistanceBalancing


