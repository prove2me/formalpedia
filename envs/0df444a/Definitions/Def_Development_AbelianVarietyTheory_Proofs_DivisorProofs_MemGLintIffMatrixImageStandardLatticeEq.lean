-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGLintIffMatrixImageStandardLatticeEq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGLintIffMatrixImageStandardLatticeEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:16.535488+00:00
-- url     : https://prove2.me/theorems/b610af00-e1c5-4a7c-87ba-b52542183e7c
-- title:
--   Mem GLint Iff Matrix Image Standard Lattice Eq
-- statement:
--   Definitions and structural lemmas for Mem GLint Iff Matrix Image Standard Lattice Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGLintIffMatrixImageStandardLatticeEq.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
namespace GlobalTheory.LatOrbGL
variable {K : Type} [Field K] (V : ValuationSubring K)
end GlobalTheory.LatOrbGL


