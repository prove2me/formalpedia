-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
-- name    : QEC_Coding_ExpanderCodes_TannerScheduleBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:46:44.897938+00:00
-- url     : https://prove2.me/theorems/6ec951db-997b-4668-b62b-e4dc44e80d6c
-- title:
--   Tanner Schedule Bounds
-- statement:
--   Definitions and structural lemmas for Tanner Schedule Bounds, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
noncomputable local instance _p2m_local_instance_5f18e3d3db_23 : DecidableEq F := Classical.decEq F
noncomputable local instance _p2m_local_instance_5f18e3d3db_24 : DecidableEq
    (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :=
  Classical.decEq _
def coarseLowWeightFactor (w d q : Nat) : Nat :=
  d * (w + 1) ^ d * q ^ d
def coarseRectangleFactor (w m s q : Nat) : Nat :=
  4 ^ w *
    (s * ((w * w + 1) ^ s) * q ^ (4 * m * w + s))
def coarseRectangleExponent (w m s q : Nat) : Nat :=
  2 * w + (Nat.log q s + 1) +
    (Nat.log q (w * w + 1) + 1) * s + (4 * m * w + s)
end QEC.Coding.TannerLiftedProduct


