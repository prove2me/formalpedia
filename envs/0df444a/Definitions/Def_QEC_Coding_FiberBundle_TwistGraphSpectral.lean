-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectral
-- name    : QEC_Coding_FiberBundle_TwistGraphSpectral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:47:11.020307+00:00
-- url     : https://prove2.me/theorems/020d785c-344c-4bdc-b5db-9d8f6bb4ee58
-- title:
--   Twist Graph Spectral
-- statement:
--   Definitions and structural lemmas for Twist Graph Spectral, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectral.lean

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Mathlib.Data.Nat.Dist
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
def HasHHO20SquaredExpanderMixing
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ left right : Finset (ZMod ell),
    (50000 *
        Nat.dist
          (ell * neighborEdgeCount twistSample left right)
          (2 * typeCount * left.card * right.card)) ^ 2 ≤
      (2 * typeCount) ^ 2 *
        left.card * (ell - left.card) *
        right.card * (ell - right.card)
end QEC.Coding.FiberBundle.TwistGraph


