-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCechOneCocycleOnAffineCoverMixed
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCechOneCocycleOnAffineCoverMixed
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:59:34.988624+00:00
-- url     : https://prove2.me/theorems/09d34e3d-eb33-5b5a-9873-ce28c0ac9150
-- title:
--   Exists Cech One Cocycle On Affine Cover Mixed
-- statement:
--   Definitions and structural lemmas for Exists Cech One Cocycle On Affine Cover Mixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCechOneCocycleOnAffineCoverMixed.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
namespace GlobalTheory.CechMixed
open GlobalTheory.KS
end GlobalTheory.CechMixed


