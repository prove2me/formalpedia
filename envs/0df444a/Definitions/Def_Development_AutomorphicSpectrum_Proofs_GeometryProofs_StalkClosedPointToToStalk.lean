-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
-- name    : Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:16.817383+00:00
-- url     : https://prove2.me/theorems/c3e77f29-ec1c-471c-aae0-7dcd4d23db0b
-- title:
--   Stalk Closed Point To To Stalk
-- statement:
--   Definitions and structural lemmas for Stalk Closed Point To To Stalk, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory CptModel
namespace CoordInhab
variable {o K : Type} [CommRing o] [Field K] [Algebra o K]
variable [IsFractionRing o K]
variable {R : Type} [CommRing R] [IsLocalRing R]
end CoordInhab
open CoordInhab
namespace CoordInhab
end CoordInhab
end GlobalTheory.CompanionTheory.Ar


