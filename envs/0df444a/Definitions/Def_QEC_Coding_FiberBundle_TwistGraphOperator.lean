-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
-- name    : QEC_Coding_FiberBundle_TwistGraphOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:49:21.832117+00:00
-- url     : https://prove2.me/theorems/c0368471-fde2-48a9-9286-b87373cf6cf0
-- title:
--   Twist Graph Operator
-- statement:
--   Definitions and structural lemmas for Twist Graph Operator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphOperator.lean

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
noncomputable def undirectedNeighborSum
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (g : ZMod ell → Real)
    (u : ZMod ell) : Real :=
  ∑ τ : Fin typeCount,
    (g (outNeighbor twistSample τ u) +
      g (inNeighbor twistSample τ u))
noncomputable def adjacencyPairing
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (f g : ZMod ell → Real) : Real :=
  ∑ u : ZMod ell, f u * undirectedNeighborSum twistSample g u
def HasHHO20OperatorMixing
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ f g : ZMod ell → Real,
    (∑ u, f u) = 0 →
    (∑ u, g u) = 0 →
    (50000 * |adjacencyPairing twistSample f g|) ^ 2 ≤
      (2 * typeCount : Real) ^ 2 *
        (∑ u, (f u) ^ 2) *
        ∑ u, (g u) ^ 2
noncomputable def centeredIndicator
    {ell : Nat}
    (vertices : Finset (ZMod ell))
    (u : ZMod ell) : Real :=
  if u ∈ vertices then ell - vertices.card else -vertices.card
end QEC.Coding.FiberBundle.TwistGraph


