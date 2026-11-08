-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
-- name    : QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:48:45.367786+00:00
-- url     : https://prove2.me/theorems/dc856b94-8cf9-4831-a147-8ed272012aaf
-- title:
--   Tanner Scheduled Local Pair
-- statement:
--   Definitions and structural lemmas for Tanner Scheduled Local Pair, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
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
noncomputable local instance _p2m_local_instance_ffaee19b85_24 : DecidableEq F := Classical.decEq F
noncomputable local instance _p2m_local_instance_ffaee19b85_25 : DecidableEq
    (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :=
  Classical.decEq _
def quadraticWeightBase (q A : Nat) : Nat := q * A ^ 2
def logarithmicLocalRows (q A D : Nat) : Nat :=
  D + 2 * D * (Nat.log q A + 1) + 5
end QEC.Coding.TannerLiftedProduct


