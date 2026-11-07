-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
-- name    : QEC_Coding_FiberBundle_TwistGraphFourier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:51:00.048443+00:00
-- url     : https://prove2.me/theorems/7ce9c11f-bf10-4016-81e9-a337513453da
-- title:
--   Twist Graph Fourier
-- statement:
--   Definitions and structural lemmas for Twist Graph Fourier, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphFourier.lean

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphOperator
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod
noncomputable def complexNeighborSum
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (g : ZMod ell → Complex)
    (u : ZMod ell) : Complex :=
  ∑ τ : Fin typeCount,
    (g (outNeighbor twistSample τ u) +
      g (inNeighbor twistSample τ u))
noncomputable def cayleyMultiplier
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (frequency : ZMod ell) : Complex :=
  ∑ τ : Fin typeCount,
    (ZMod.stdAddChar (step twistSample τ * frequency) +
      ZMod.stdAddChar (-(step twistSample τ * frequency)))
def HasHHO20CayleySpectrum
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ frequency : ZMod ell, frequency ≠ 0 →
    50000 * ‖cayleyMultiplier twistSample frequency‖ ≤
      2 * typeCount
end QEC.Coding.FiberBundle.TwistGraph


