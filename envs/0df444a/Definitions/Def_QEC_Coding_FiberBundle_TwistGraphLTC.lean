-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
-- name    : QEC_Coding_FiberBundle_TwistGraphLTC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:42:50.046247+00:00
-- url     : https://prove2.me/theorems/167f9e0a-def4-4cf4-a04a-057669b95a18
-- title:
--   Twist Graph LTC
-- statement:
--   Definitions and structural lemmas for Twist Graph LTC, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphLTC.lean

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
noncomputable def pairCheckSyndrome
    {r typeCount ell : Nat}
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) : ZMod 2 :=
  ∑ b : Fin (4 * r),
    RandomBase.boundary baseSample a b *
      if RandomTwist.isTail twistSample a b then y b else z b
noncomputable def typeViolationSet
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    Finset (Fin (3 * r)) := by
  classical
  exact Finset.univ.filter fun a =>
    RandomTwist.checkType typeCount a = τ ∧
      pairCheckSyndrome baseSample twistSample y z a ≠ 0
noncomputable def typeViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) : Nat :=
  (typeViolationSet baseSample twistSample τ y z).card
noncomputable def outgoingTypeViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (τ : Fin typeCount) : Nat :=
  typeViolationCount baseSample twistSample τ
    (layerWord w u)
    (layerWord w (outNeighbor twistSample τ u))
noncomputable def incomingTypeViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (τ : Fin typeCount) : Nat :=
  typeViolationCount baseSample twistSample τ
    (layerWord w (inNeighbor twistSample τ u))
    (layerWord w u)
noncomputable def incidentViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) : Nat :=
  ∑ τ : Fin typeCount,
    (outgoingTypeViolationCount baseSample twistSample w u τ +
      incomingTypeViolationCount baseSample twistSample w u τ)
noncomputable def lightLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact Finset.univ.filter fun u =>
    Delta * HammingWeight (layerWord w u) ≤ 2 * (4 * r)
noncomputable def mediumLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact Finset.univ.filter fun u =>
    2 * (4 * r) < Delta * HammingWeight (layerWord w u) ∧
      Delta * HammingWeight (layerWord w u) < 4 * (4 * r)
noncomputable def heavyLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact Finset.univ.filter fun u =>
    4 * (4 * r) ≤ Delta * HammingWeight (layerWord w u)
noncomputable def nonheavyLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact Finset.univ.filter fun u =>
    Delta * HammingWeight (layerWord w u) < 4 * (4 * r)
noncomputable def neighborIncidenceCount
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (layers : Finset (ZMod ell))
    (u : ZMod ell) : Nat :=
  ∑ τ : Fin typeCount,
    ((if outNeighbor twistSample τ u ∈ layers then 1 else 0) +
      (if inNeighbor twistSample τ u ∈ layers then 1 else 0))
noncomputable def usableNonheavyLayerSet
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact (nonheavyLayerSet Delta w).filter fun u =>
    typeCount ≤
      5 * neighborIncidenceCount twistSample
        (nonheavyLayerSet Delta w) u
noncomputable def badNonheavyLayerSet
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) :=
  nonheavyLayerSet Delta w \ usableNonheavyLayerSet Delta twistSample w
noncomputable def twoSidedLightTypeSet
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) : Finset (Fin typeCount) := by
  classical
  exact Finset.univ.filter fun τ =>
    outNeighbor twistSample τ u ∈ lightLayerSet Delta w ∧
      inNeighbor twistSample τ u ∈ lightLayerSet Delta w
noncomputable def usableHeavyLayerSet
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact (heavyLayerSet Delta w).filter fun u =>
    98 * typeCount ≤
      100 * (twoSidedLightTypeSet Delta twistSample w u).card
def HasHHO20LayerMixing
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ w : Word (ZMod 2) (ZMod ell × Fin (4 * r)),
    5000 * Delta * HammingWeight w ≤ ell * (4 * r) →
      4 * (badNonheavyLayerSet Delta twistSample w).card ≤
          5 * (heavyLayerSet Delta w).card ∧
        ((mediumLayerSet Delta w).card <
            1000 * (heavyLayerSet Delta w).card →
          9 * (heavyLayerSet Delta w).card ≤
            10 * (usableHeavyLayerSet Delta twistSample w).card)
def HasHHO20LightChecks
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ (τ : Fin typeCount)
      (y z : Word (ZMod 2) (Fin (4 * r))),
    Delta * HammingWeight y ≤ 4 * (4 * r) →
    Delta * HammingWeight z ≤ 4 * (4 * r) →
      Delta * (HammingWeight y + HammingWeight z) ≤
        100 * typeCount *
          typeViolationCount baseSample twistSample τ y z
noncomputable def heavyIncidentViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r))) : Nat :=
  ∑ τ ∈ types,
    (typeViolationCount baseSample twistSample τ x (outWord τ) +
      typeViolationCount baseSample twistSample τ (inWord τ) x)
def HasHHO20HeavyChecks
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ (x : Word (ZMod 2) (Fin (4 * r)))
      (types : Finset (Fin typeCount))
      (outWord inWord :
        Fin typeCount → Word (ZMod 2) (Fin (4 * r))),
    4 * (4 * r) ≤ Delta * HammingWeight x →
    98 * typeCount ≤ 100 * types.card →
    (∀ τ ∈ types,
      Delta * HammingWeight (outWord τ) ≤ 2 * (4 * r) ∧
      Delta * HammingWeight (inWord τ) ≤ 2 * (4 * r)) →
      4 * r ≤
        100 *
          heavyIncidentViolationCount baseSample twistSample
            x types outWord inWord
def HasHHO20PartitionedChecks
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  HasHHO20LightChecks Delta baseSample twistSample ∧
    HasHHO20HeavyChecks Delta baseSample twistSample
end QEC.Coding.FiberBundle.TwistGraph


