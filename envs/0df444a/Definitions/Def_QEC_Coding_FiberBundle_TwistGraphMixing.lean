-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
-- name    : QEC_Coding_FiberBundle_TwistGraphMixing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:45:53.163205+00:00
-- url     : https://prove2.me/theorems/dfaae79d-0e3e-4400-89a1-067db1c9aa5d
-- title:
--   Twist Graph Mixing
-- statement:
--   Definitions and structural lemmas for Twist Graph Mixing, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphMixing.lean

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
noncomputable def neighborEdgeCount
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (source target : Finset (ZMod ell)) : Nat :=
  ∑ u ∈ source, neighborIncidenceCount twistSample target u
def HasHHO20EdgeMixing
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ w : Word (ZMod 2) (ZMod ell × Fin (4 * r)),
    20000 * (heavyLayerSet Delta w).card ≤ ell →
    9999 * ell ≤ 10000 * (lightLayerSet Delta w).card →
      10 * ell *
          neighborEdgeCount twistSample
            (nonheavyLayerSet Delta w) (heavyLayerSet Delta w) ≤
        22 * typeCount *
          (nonheavyLayerSet Delta w).card *
          (heavyLayerSet Delta w).card ∧
      ((mediumLayerSet Delta w).card <
          1000 * (heavyLayerSet Delta w).card →
        1998 * typeCount * (heavyLayerSet Delta w).card ≤
          1000 *
            neighborEdgeCount twistSample
              (heavyLayerSet Delta w) (lightLayerSet Delta w))
noncomputable def badHeavyLayerSet
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) :=
  heavyLayerSet Delta w \ usableHeavyLayerSet Delta twistSample w
end QEC.Coding.FiberBundle.TwistGraph


