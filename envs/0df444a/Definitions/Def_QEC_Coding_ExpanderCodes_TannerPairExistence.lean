-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
-- name    : QEC_Coding_ExpanderCodes_TannerPairExistence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:16:44.340237+00:00
-- url     : https://prove2.me/theorems/e00be0b5-3532-4b9d-8679-660452ea6ab5
-- title:
--   Tanner Pair Existence
-- statement:
--   Definitions and structural lemmas for Tanner Pair Existence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerPairExistence.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
noncomputable local instance _p2m_local_instance_62dc6baf31_23 : DecidableEq F := Classical.decEq F
noncomputable local instance _p2m_local_instance_62dc6baf31_24 : DecidableEq
    (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :=
  Classical.decEq _
end QEC.Coding.TannerLiftedProduct


