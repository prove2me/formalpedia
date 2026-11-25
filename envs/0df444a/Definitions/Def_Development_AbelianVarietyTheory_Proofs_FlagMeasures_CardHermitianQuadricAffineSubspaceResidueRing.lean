-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianQuadricAffineSubspaceResidueRing
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianQuadricAffineSubspaceResidueRing
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:16.376971+00:00
-- url     : https://prove2.me/theorems/aebf6c6c-40a8-492e-9412-37be2444d6d7
-- title:
--   Card Hermitian Quadric Affine Subspace Residue Ring
-- statement:
--   Definitions and structural lemmas for Card Hermitian Quadric Affine Subspace Residue Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianQuadricAffineSubspaceResidueRing.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
namespace GlobalTheory.GramCount
variable {B : Type} [CommRing B] [Fintype B]
end GlobalTheory.GramCount


