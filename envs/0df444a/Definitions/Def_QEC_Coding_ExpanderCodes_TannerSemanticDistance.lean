-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
-- name    : QEC_Coding_ExpanderCodes_TannerSemanticDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:41:18.071415+00:00
-- url     : https://prove2.me/theorems/ed1e5056-1b93-418d-bddf-52abe65214fe
-- title:
--   Tanner Semantic Distance
-- statement:
--   Definitions and structural lemmas for Tanner Semantic Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
noncomputable local instance _p2m_local_instance_138d9bf296_23 : DecidableEq F := Classical.decEq F
noncomputable local instance _p2m_local_instance_138d9bf296_24 : DecidableEq
    (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :=
  Classical.decEq _
end QEC.Coding.TannerLiftedProduct


