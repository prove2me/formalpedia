-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
-- name    : QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:32:16.038231+00:00
-- url     : https://prove2.me/theorems/d1b75861-6374-4082-9c46-ff250df3427a
-- title:
--   FPSEuler
-- statement:
--   Definitions and structural lemmas for FPSEuler, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSEuler.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
end


