-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:14.734478+00:00
-- url     : https://prove2.me/theorems/66bb7ab6-4218-4121-a835-b89c69f2141e
-- title:
--   Signed Length Map Eq Log Ord Frac Det
-- statement:
--   Definitions and structural lemmas for Signed Length Map Eq Log Ord Frac Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthMapEqLogOrdFracDet.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
namespace GlobalTheory.SignedLengthMapLogDet
open Module
section Order
variable {R : Type*} [CommRing R] [IsDomain R]
end Order
section Chain
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
end Chain
section Lattice
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end Lattice
end GlobalTheory.SignedLengthMapLogDet


