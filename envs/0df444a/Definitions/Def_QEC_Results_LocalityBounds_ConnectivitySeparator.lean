-- Prove2me | Definitions.Def_QEC_Results_LocalityBounds_ConnectivitySeparator
-- name    : QEC_Results_LocalityBounds_ConnectivitySeparator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:58:52.219018+00:00
-- url     : https://prove2.me/theorems/07d0dea9-0454-4b8b-86a6-d4ebc2f2e589
-- title:
--   Connectivity Separator
-- statement:
--   Definitions and structural lemmas for Connectivity Separator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/ConnectivitySeparator.lean

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_TwoPassDimension
set_option autoImplicit false
noncomputable section
namespace QEC.Locality
universe u v
namespace BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]
end BKQLDPCFamily
end QEC.Locality


